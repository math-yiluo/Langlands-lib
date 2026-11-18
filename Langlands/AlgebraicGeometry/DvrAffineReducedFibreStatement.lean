import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-! # The reduced fibre theorem for affine DVR schemes with smooth generic fibre -/

noncomputable section

universe u

open TensorProduct

namespace Langlands.AlgebraicGeometry

/-- Affine form of the Raynaud–Faltings reduced fibre theorem, in the case of a
smooth generic fibre. For a flat finite-type algebra `A` over a DVR `R` whose
generic fibre `FractionRing R ⊗[R] A` is smooth, there is a faithfully flat DVR
extension `R'` in the same universe such that the integral closure `B` of
`A' = R' ⊗[R] A` in its generic fibre `A' ⊗[R'] FractionRing R'` is a finite
`A'`-module and `F ⊗[R'] B` is reduced for every field `F` under `R'`. -/
def DvrAffineReducedFibreStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (A : Type u) [CommRing A] [Algebra R A],
    Module.Flat R A → Algebra.FiniteType R A →
    Algebra.Smooth (FractionRing R) (FractionRing R ⊗[R] A) →
    ∃ (R' : Type u) (cR' : CommRing R'),
      letI := cR'
      ∃ (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (aR' : Algebra R R'),
        letI := aR'
        Module.FaithfullyFlat R R' ∧
        Module.Finite (R' ⊗[R] A)
          (integralClosure (R' ⊗[R] A) ((R' ⊗[R] A) ⊗[R'] FractionRing R')) ∧
        ∀ (F : Type u) [Field F] [Algebra R' F],
          IsReduced (F ⊗[R']
            integralClosure (R' ⊗[R] A) ((R' ⊗[R] A) ⊗[R'] FractionRing R'))

end Langlands.AlgebraicGeometry
