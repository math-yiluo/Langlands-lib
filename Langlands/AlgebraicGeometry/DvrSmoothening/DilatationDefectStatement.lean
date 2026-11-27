import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Langlands.AlgebraicGeometry.DvrSmootheningStatement
import Langlands.AlgebraicGeometry.DvrSmoothening.PointDefect
import Langlands.GroupScheme.Dilatation.Algebra

/-! # The defect of smoothness drops under dilatation of a good centre -/

universe u

open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.DvrSmoothening

/-- Let `R` be a discrete valuation ring with uniformizer `ϖ` and `A` an `R`-algebra of finite
type whose localization `A[1/ϖ]` (the generic fibre) is smooth over `R`. Let `J` be the
intersection of a set `S` of ideals, each the preimage of the maximal ideal
under a point of `A` with values in a discrete valuation ring of ramification index one over
`R`. Assume that `A ⧸ J` is smooth over the residue field of `R` and that
`(A ⧸ J) ⊗_A Ω_{A/R}` is free. Let `φ : A →ₐ[R] R'` be a point of ramification index one with
`J ⊆ φ⁻¹(𝔪_{R'})` and `φ'` its lift to the dilatation algebra `A[J/ϖ]`. If `φ` has positive
defect, then the defect of `φ'` is strictly smaller. -/
def DilatationDefectStatement : Prop :=
  ∀ (R A : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A] (ϖ : R), Irreducible ϖ →
    Algebra.Smooth R (Localization.Away (algebraMap R A ϖ)) →
    ∀ (J : Ideal A) (S : Set (Ideal A)), J = sInf S →
    (∀ p ∈ S, ∃ (R'' : Type u) (_ : CommRing R'') (_ : IsDomain R'')
      (_ : IsDiscreteValuationRing R'') (_ : Algebra R R'') (_ : IsLocalHom (algebraMap R R''))
      (ψ : A →ₐ[R] R''), IsRamificationIndexOne R R'' ∧
        (IsLocalRing.maximalIdeal R'').comap ψ = p) →
    Algebra.Smooth (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] (A ⧸ J)) →
    Module.Free (A ⧸ J) ((A ⧸ J) ⊗[A] Ω[A⁄R]) →
    ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
      [IsLocalHom (algebraMap R R')], IsRamificationIndexOne R R' →
    ∀ φ : A →ₐ[R] R', J ≤ (IsLocalRing.maximalIdeal R').comap φ →
    ∀ φ' : GroupScheme.Dilatation.blowupAlgebra ϖ J →ₐ[R] R',
      φ'.comp (GroupScheme.Dilatation.blowupMap ϖ J) = φ →
      pointDefect φ ≠ 0 → pointDefect φ' < pointDefect φ

end Langlands.AlgebraicGeometry.DvrSmoothening
