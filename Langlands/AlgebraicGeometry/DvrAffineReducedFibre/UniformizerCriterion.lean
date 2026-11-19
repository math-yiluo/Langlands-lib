import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.FibreTests
import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.FiniteNormalization
import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.NormalLocalizations
import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.PrincipalFibre
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # The reduced fibre criterion for a base uniformizer -/

open IsLocalRing TensorProduct

noncomputable section

universe u

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

section Principal

variable (R B : Type*) [CommRing R] [IsLocalRing R] [CommRing B] [Algebra R B]

/-- The residue tensor of an algebra is the quotient by the image of a generator
of the base maximal ideal. -/
def residueTensorEquivPrincipalQuotient {π : R} (hπ : maximalIdeal R = Ideal.span {π}) :
    ResidueField R ⊗[R] B ≃+* B ⧸ Ideal.span {algebraMap R B π} :=
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (maximalIdeal R)).symm.toRingEquiv.trans
    (Ideal.quotEquivOfEq (by rw [hπ, Ideal.map_span, Set.image_singleton]))

/-- The base uniformizer generates the maximal ideal of the localization at
all primes minimal over its image. -/
abbrev BaseUniformizerAtGenericPoints (π : R) : Prop :=
  ∀ (p : Ideal B) [p.IsPrime], (Ideal.span {algebraMap R B π}).IsMinimalPrime p →
    Ideal.span {algebraMap R (Localization.AtPrime p) π} = maximalIdeal (Localization.AtPrime p)

/-- Under the normality and regularity hypotheses for a principal fibre, a base
uniformizer at each generic point gives reducedness of the whole closed fibre. -/
theorem isReduced_residueTensor_of_uniformizer_at_minimalPrimes [IsNoetherianRing B]
    {π : R} (hπ : maximalIdeal R = Ideal.span {π})
    (hregular : algebraMap R B π ∈ nonZeroDivisors B)
    (hnormal : ∀ (p : Ideal B) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hgen : BaseUniformizerAtGenericPoints R B π) :
    IsReduced (ResidueField R ⊗[R] B) := by
  have : IsReduced (B ⧸ Ideal.span {algebraMap R B π}) := by
    apply isReduced_quotient_span_singleton_of_minimalPrimes hregular hnormal
    intro p hp hmin
    rw [Ideal.map_span, Set.image_singleton, ← IsScalarTower.algebraMap_apply, hgen p hmin]
    infer_instance
  let e := residueTensorEquivPrincipalQuotient R B hπ
  exact isReduced_of_injective e.toRingHom e.injective

end Principal

section DVR

variable (R A : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R] [PerfectField (ResidueField R)]
    [CommRing A] [Algebra R A] [Module.Flat R A] [Algebra.FiniteType R A]
    [Algebra.Smooth (FractionRing R) (FractionRing R ⊗[R] A)]

local notation "N" => integralClosure A (A ⊗[R] FractionRing R)

/-- Over a complete DVR with perfect residue field, the generic-fibre normalization
is finite, and the base uniformizer criterion gives reducedness over every field. -/
theorem finite_normalization_and_reduced_fibres_of_uniformizer {π : R} (hπ : Irreducible π)
    (hgen : BaseUniformizerAtGenericPoints R N π) :
    Module.Finite A N ∧ ∀ (F : Type u) [Field F] [Algebra R F], IsReduced (F ⊗[R] N) := by
  have hfinite : Module.Finite A N := finite_integralClosure_genericFibre_of_completeDvr R A
  refine ⟨hfinite, ?_⟩
  let G := A ⊗[R] FractionRing R
  have hnoeth : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  have hNnoeth : IsNoetherianRing N := IsNoetherianRing.of_finite A N
  have hregular : algebraMap R N π ∈ nonZeroDivisors N := by
    have hunit : IsUnit (algebraMap R G π) := by
      let : Algebra (FractionRing R) G := Algebra.TensorProduct.rightAlgebra
      have : IsScalarTower R (FractionRing R) G := Algebra.TensorProduct.right_isScalarTower
      rw [IsScalarTower.algebraMap_apply R (FractionRing R) G]
      have hπK : algebraMap R (FractionRing R) π ≠ 0 := by
        rw [← map_zero (algebraMap R (FractionRing R))]
        exact (IsFractionRing.injective R (FractionRing R)).ne hπ.ne_zero
      exact (isUnit_iff_ne_zero.mpr hπK).map (algebraMap (FractionRing R) G)
    rw [mem_nonZeroDivisors_iff_left]
    intro x hx
    apply Subtype.ext
    have hx' := congrArg (fun z : N => z.val) hx
    change algebraMap R G π * x.val = 0 at hx'
    exact hunit.mul_right_eq_zero.mp hx'
  have hred : IsReduced (ResidueField R ⊗[R] N) :=
    isReduced_residueTensor_of_uniformizer_at_minimalPrimes R N hπ.maximalIdeal_eq hregular
      (fun p _ => normal_localizations_genericNormalization R A p) hgen
  apply isReduced_tensor_integralClosure_of_residue_test R A (E := ResidueField R)
  let e := Algebra.TensorProduct.lid (ResidueField R) (ResidueField R ⊗[R] N)
  exact isReduced_of_injective e.toRingHom e.injective

end DVR

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
