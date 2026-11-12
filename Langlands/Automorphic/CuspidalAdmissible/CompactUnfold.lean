import Langlands.Automorphic.CuspidalAdmissible.CuspRealization
import Langlands.Automorphic.CuspidalAdmissible.BandShift

/-!
# Square integrals over compact sets

For a realization with unitary central character, the square integral of a realized vector over
a compact subset of the adelic group is at most a fixed constant times its band integral: the
compact set meets each rational orbit in boundedly many points, and its determinant norms lie in
a closed band, covered by finitely many open bands.
-/

noncomputable section

universe uF

open MeasureTheory NumberField
open scoped Classical Topology ENNReal NNReal

set_option autoImplicit false

namespace Langlands.Automorphic.CuspidalAdmissible

open Langlands.Global Langlands.Automorphic Langlands.Automorphic.ContinuousRationalFunctions
  Langlands.Automorphic.CuspidalL2 Langlands.Automorphic.OperatorDeterminantSlice

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance compactUnfoldIsAffine :
    _root_.AlgebraicGeometry.IsAffine (matrixGroupScheme F n).X.left :=
  Langlands.GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance compactUnfoldSmooth : _root_.AlgebraicGeometry.Smooth (matrixGroupScheme F n).X.hom :=
  Langlands.GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)
local instance compactUnfoldRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance compactUnfoldContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance compactUnfoldSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance compactUnfoldFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance compactUnfoldStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

variable (S : OperatorRealization F n)

local instance compactUnfoldSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

set_option maxHeartbeats 1000000 in
/-- **Compact sets cost a constant.** -/
theorem exists_lintegral_compact_le [MeasurableSpace (AdelicGL F n)] [BorelSpace (AdelicGL F n)]
    (hn : n ≠ 0) (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) (hχ : ∀ x, ‖(χ x : ℂ)‖ = 1)
    (hSχ : S.HasCentralCharacter χ) {Kc : Set (AdelicGL F n)} (hKc : IsCompact Kc) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : S.Space,
      ∫⁻ g in Kc, ‖evaluate F n (S.toContinuous f) g‖ₑ ^ 2 ∂matrixHaarMeasure F n ≤
        C * bandNorm S f := by
  have := adelicGL_t2Space F n
  rcases Set.eq_empty_or_nonempty Kc with hemp | hne
  · refine ⟨0, ENNReal.zero_ne_top, fun f => ?_⟩
    rw [hemp, Measure.restrict_empty, lintegral_zero_measure]
    exact zero_le
  set D : AdelicGL F n → ℝ≥0 := fun g =>
    ((AdelicBlockDeterminantCharacter.determinantNorm F n g : ℝ≥0ˣ) : ℝ≥0) with hDdef
  have hDc : Continuous D :=
    Units.continuous_val.comp (AdelicBlockDeterminantCharacter.determinantNorm F n).continuous
  obtain ⟨gm, hgm, hmin⟩ := hKc.exists_isMinOn hne hDc.continuousOn
  obtain ⟨gM, hgM, hmax⟩ := hKc.exists_isMaxOn hne hDc.continuousOn
  have hm : 0 < D gm := pos_iff_ne_zero.mpr (Units.ne_zero _)
  obtain ⟨N, hN⟩ := exists_lintegral_closedBand_le F n S hn χ hχ hSχ (M := D gM) hm
  set A : Set (Quotient F n) := {q | D gm ≤ (quotientDeterminantNorm F n q : ℝ≥0) ∧
    (quotientDeterminantNorm F n q : ℝ≥0) ≤ D gM} with hAdef
  have hA : MeasurableSet A := by
    have hc : Continuous fun q : Quotient F n => (quotientDeterminantNorm F n q : ℝ≥0) :=
      Units.continuous_val.comp (quotientDeterminantNorm F n).continuous
    exact (isClosed_le continuous_const hc |>.inter (isClosed_le hc continuous_const)).measurableSet
  set Mk : ℝ≥0∞ := ({γ : RationalGL F n | ∃ g ∈ Kc,
    AdelicGL.rational F n γ * g ∈ Kc}.encard : ℝ≥0∞) with hMkdef
  have hMk : Mk ≠ ⊤ :=
    ENat.toENNReal_ne_top.mpr (finite_rational_compact F n Kc Kc hKc hKc).encard_lt_top.ne
  refine ⟨Mk * N, ENNReal.mul_ne_top hMk (ENNReal.natCast_ne_top N), fun f => ?_⟩
  have hle := lintegral_le_mul_quotient F n A hA Kc hKc.isClosed.measurableSet
    (fun x hx => by
      show D gm ≤ (quotientDeterminantNorm F n (point F n x) : ℝ≥0) ∧
        (quotientDeterminantNorm F n (point F n x) : ℝ≥0) ≤ D gM
      rw [quotientDeterminantNorm_point]
      exact ⟨hmin hx, hmax hx⟩)
    Mk (fun x => ENat.toENNReal_le.mpr (encard_rational_mul_mem_le F n Kc x))
    (fun q => ‖toQuotient F n S f q‖ₑ ^ 2)
    ((toQuotient F n S f).continuous.measurable.enorm.pow_const 2)
  calc ∫⁻ g in Kc, ‖evaluate F n (S.toContinuous f) g‖ₑ ^ 2 ∂matrixHaarMeasure F n
      = ∫⁻ g in Kc, ‖toQuotient F n S f (point F n g)‖ₑ ^ 2 ∂matrixHaarMeasure F n := by
        refine lintegral_congr fun g => ?_
        rw [toQuotient_point]
    _ ≤ Mk * ∫⁻ q in A, ‖toQuotient F n S f q‖ₑ ^ 2 ∂quotientHaarMeasure F n := hle
    _ ≤ Mk * (N * bandNorm S f) := by
        gcongr
        exact hN f
    _ = Mk * N * bandNorm S f := by ring

end Langlands.Automorphic.CuspidalAdmissible
