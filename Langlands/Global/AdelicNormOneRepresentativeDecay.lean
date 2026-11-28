import Langlands.Global.AdelicNormOneCuspidalDecay
import Langlands.Global.AdelicCuspidalFibreVector
import Langlands.Global.AdelicNormOneClassicalCuspidalDensity
import Langlands.Global.AdelicNormOneKernelVectorUnfolding

/-! # Weighted norm-one representatives and continuous cuspidal tests -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  PositiveRealTorus RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F] {H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

local notation "A" => AdelicGroupPoints F H
local notation "A₁" => normOneSubgroup F H
local notation "X₁" => NormOneRationalQuotient F H
local notation "dq₁" => normOneRationalQuotientHaarMeasure F H

omit [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom] in
/-- A rationally invariant test with weighted norm-one representatives is bounded on all
norm-one points, using weight zero. -/
theorem HasRapidDecayOnNormOneRepresentatives.exists_normOne_bound {N : ℕ}
    {rho : MatrixRepresentation H (Fin N)} {t : A → ℂ}
    (hdec : HasRapidDecayOnNormOneRepresentatives rho t)
    (ht : IsLeftInvariantUnder F H (rationalSubgroup F H) t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : A₁, ‖t (x : A)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := hdec 0
  refine ⟨C, hC, fun x => ?_⟩
  obtain ⟨r, hr⟩ := hb x
  simpa only [pow_zero, mul_one, ht _ ⟨r, rfl⟩] using hr

variable (hH : IsConnectedReductive H)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ H)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hc : IsCentral i) [(Measure.haar : Measure (normOneSubgroup F H)).IsMulRightInvariant]

local notation "Q" => PositiveRationalQuotient F H T i
local notation "dq" => positiveRationalQuotientHaarMeasure F H T i
local notation "S" => fullAEL2CuspidalSubmodule F H parabolicDynamic hH T i hi I e hc

/-- The norm-one restriction of a bounded continuous cuspidal test represents a cuspidal
class and gives the same partial convolutions as the \(L^2\) representative. -/
theorem exists_cuspidalClass_of_bounded_normOneRestriction {t : A → ℂ} (ht : Continuous t)
    (hInv : IsLeftInvariantUnder F H (rationalSubgroup F H) t)
    (hCusp : HasZeroProperParabolicConstantTerms t) (C : ℝ) (hC : ∀ x : A₁, ‖t (x : A)‖ ≤ C) :
    ∃ v : S, (v.val : Q → ℂ) =ᵐ[dq] positiveQuotientOfNormOneRestriction T i hi I e hc ht hInv ∧
      ∀ (K : C_c(A, ℂ)) (y : A), normOnePartialConvolution T i K (v.val : Q → ℂ) y =
        normOnePartialConvolution T i K (positiveQuotientOfNormOneRestriction T i hi I e hc ht hInv) y := by
  let := AdelicSiegelFactors.isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_connectedReductive F H hH
  let := positiveRationalQuotient_borelSpace F H T i hi I e hc
  have hmp := measurePreserving_positiveQuotient F H T i hi I e hc
  let : IsFiniteMeasure dq := by
    rw [← hmp.map_eq]
    infer_instance
  let f := positiveQuotientOfNormOneRestriction T i hi I e hc ht hInv
  have hf : MemLp (f : Q → ℂ) 2 dq := by
    refine (memLp_const C).mono' f.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    obtain ⟨ξ, rfl⟩ := (positiveQuotientHomeomorph F H T i hi I e hc).surjective q
    obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (rationalNormOneSubgroup F H) ξ
    rw [positiveQuotientHomeomorph_mk]
    simpa only [f, positiveQuotientOfNormOneRestriction_mk] using hC x
  let v₀ := hf.toLp f
  let v : S := ⟨v₀, mem_fullAEL2CuspidalSubmodule_of_normOneRestriction T i hi I e hc
    parabolicDynamic hH ht hInv hCusp v₀ hf.coeFn_toLp⟩
  refine ⟨v, hf.coeFn_toLp, fun K y => ?_⟩
  change normOnePartialConvolution T i K v₀ y = normOnePartialConvolution T i K f y
  rw [normOnePartialConvolution_eq_inner T i hi I e hc,
    normOnePartialConvolution_eq_inner_toLp T i hi I e hc K f f.continuous hf]

/-- A fixed compactly supported continuous kernel gives a continuous rationally invariant
and pointwise cuspidal function from a cuspidal \(L^2\) class. -/
theorem normOnePartialConvolution_cuspidalClass (K : C_c(A, ℂ)) (v : S) :
    let t := normOnePartialConvolution T i K (v.val : Q → ℂ)
    Continuous t ∧ IsLeftInvariantUnder F H (rationalSubgroup F H) t ∧
      HasZeroProperParabolicConstantTerms t := by
  refine ⟨?_, ?_, hasZeroProperParabolicConstantTerms_normOnePartialConvolution T i hi I e hc hH
    K v.val v.property⟩
  · have h := Continuous.inner (𝕜 := ℂ) (continuous_cuspidalNormOneKernelVector hH T i hi I e hc K)
      (continuous_const (y := v))
    simpa only [inner_cuspidalNormOneKernelVector] using h
  · rintro _ ⟨r, rfl⟩ x
    exact normOnePartialConvolution_rational_mul T i K v.val r x

variable [IsAffineHom H.X.hom]

/-- The uniform decay proposition implies weighted norm-one representatives for the
partial convolution of an individual cuspidal class with a test kernel. -/
theorem hasNormOneRepresentativeDecay_normOnePartialConvolution
    (hDecay : NormOnePartialConvolutionRapidDecayStatement.{u})
    {N : ℕ} (rho : MatrixRepresentation H (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (K : C_c(A, ℂ)) (hK : IsAdelicTestFunction F H K) (v : S) :
    HasRapidDecayOnNormOneRepresentatives rho (normOnePartialConvolution T i K (v.val : Q → ℂ)) := by
  intro m
  obtain ⟨C, hC, hb⟩ := hDecay F H hH T i hi I e hc rho hN hrho K hK {1} isCompact_singleton m
  refine ⟨C * ‖v.val‖, mul_nonneg hC (norm_nonneg _), fun x => ?_⟩
  obtain ⟨r, hr⟩ := hb x
  exact ⟨r, by simpa only [mul_one, normOnePartialConvolution] using hr v.val v.property 1 rfl⟩

end Langlands.Global
