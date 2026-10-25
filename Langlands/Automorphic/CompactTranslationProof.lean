import Langlands.Automorphic.PreservationStatement
import Langlands.Global.ArchimedeanCovarianceProof

/-! # Compact right translation preserves actual automorphic forms -/

noncomputable section
universe u

namespace Langlands.Automorphic

open Langlands.Global

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Full adelic translation preserves the existence of a compact open finite level. -/
theorem hasFiniteLevel_continuousRightAction (g : AdelicGL K n)
    {f : ContinuousRationalFunctions K n} (hf : HasFiniteLevel K n f) :
    HasFiniteLevel K n (continuousRightAction K n g f) := by
  apply (hasFiniteLevel_iff_mem_finiteSmooth K n _).mpr
  exact (finiteSmoothSubrepresentation K n).apply_mem_toSubmodule g
    ((hasFiniteLevel_iff_mem_finiteSmooth K n f).mp hf)

/-- Each subgroup preserves its own finite vectors under the actual right action. -/
theorem isInfiniteFinite_infiniteSubgroupRightAction
    (U : Subgroup (InfiniteAdelicGL K n)) (k : U)
    {f : ContinuousRationalFunctions K n} (hf : IsInfiniteFinite K n U f) :
    IsInfiniteFinite K n U
      (continuousRightAction K n (AdelicGL.ofInfinite K n k.val) f) :=
  (infiniteFiniteSubrepresentation K n U).apply_mem_toSubmodule k hf

/-- Full adelic translation preserves the existing per-finite-slice growth predicate. -/
theorem hasPolynomialGrowth_continuousRightAction (g : AdelicGL K n)
    {f : ContinuousRationalFunctions K n} (hf : HasPolynomialGrowth K n f) :
    HasPolynomialGrowth K n (continuousRightAction K n g f) := by
  apply (mem_polynomialGrowthSubrepresentation K n _).mp
  exact (polynomialGrowthSubrepresentation K n).apply_mem_toSubmodule g
    ((mem_polynomialGrowthSubrepresentation K n f).mpr hf)

/-- Apply the same actual infinite translation to every slice in a family. -/
def infiniteTranslateFamily (g : InfiniteAdelicGL K n) :
    SmoothSliceFamily K n →ₗ[ℂ] SmoothSliceFamily K n where
  toFun F b := ArchimedeanGL.smoothRightAction K n g (F b)
  map_add' F H := by ext b x; rfl
  map_smul' c F := by ext b x; rfl

/-- Infinite translation acts on the complete slice family without changing its index. -/
theorem smoothSliceFamily_infiniteRightAction (g : InfiniteAdelicGL K n)
    (f : SmoothRationalFunctions K n) :
    smoothSliceFamily K n (smoothRightAction K n (AdelicGL.ofInfinite K n g) f) =
      infiniteTranslateFamily K n g (smoothSliceFamily K n f) := by
  funext b
  apply Subtype.ext
  funext a
  change ContinuousRationalFunctions.evaluate K n f.val
      (AdelicGL.pair K n a b * AdelicGL.ofInfinite K n g) =
    ContinuousRationalFunctions.evaluate K n f.val (AdelicGL.pair K n (a * g) b)
  rw [AdelicGL.ofInfinite_eq_pair, AdelicGL.pair_mul, mul_one]

/-- Reindex each central operator through the actual center algebra equivalence. -/
theorem centerFamilyOrbitSpan_infiniteTranslateFamily_le
    (g : InfiniteAdelicGL K n)
    (F : SmoothSliceFamily K n) :
    centerFamilyOrbitSpan K n (infiniteTranslateFamily K n g F) ≤
      (centerFamilyOrbitSpan K n F).map (infiniteTranslateFamily K n g) := by
  rw [centerFamilyOrbitSpan_eq_range]
  rintro _ ⟨z, rfl⟩
  apply Submodule.mem_map.mpr
  refine ⟨centerFamilyAction K n ((ArchimedeanGL.centerConjugation K n g).symm z) F,
    ?_, ?_⟩
  · rw [centerFamilyOrbitSpan_eq_range]
    exact ⟨(ArchimedeanGL.centerConjugation K n g).symm z, rfl⟩
  · funext b
    change ArchimedeanGL.smoothRightAction K n g
        (ArchimedeanGL.centerAction K n
          ((ArchimedeanGL.centerConjugation K n g).symm z) (F b)) =
      ArchimedeanGL.centerAction K n z
        (ArchimedeanGL.smoothRightAction K n g (F b))
    simpa only [AlgEquiv.apply_symm_apply] using
      ArchimedeanGL.centerRightCovariance K n g ((ArchimedeanGL.centerConjugation K n g).symm z) (F b)

/-- One finite-dimensional image controls the full translated family at once. -/
theorem isCenterFiniteFamily_infiniteTranslateFamily
    (g : InfiniteAdelicGL K n)
    {F : SmoothSliceFamily K n} (hF : IsCenterFiniteFamily K n F) :
    IsCenterFiniteFamily K n (infiniteTranslateFamily K n g F) := by
  have : Module.Finite ℂ (centerFamilyOrbitSpan K n F) := hF
  have : Module.Finite ℂ
      ((centerFamilyOrbitSpan K n F).map (infiniteTranslateFamily K n g)) :=
    inferInstance
  exact Submodule.finiteDimensional_of_le
    (centerFamilyOrbitSpan_infiniteTranslateFamily_le K n g F)

/-- Pull the common-family argument back to the actual smooth adelic functions. -/
theorem isCenterFinite_infiniteRightAction
    (g : InfiniteAdelicGL K n)
    {f : SmoothRationalFunctions K n} (hf : IsCenterFinite K n f) :
    IsCenterFinite K n (smoothRightAction K n (AdelicGL.ofInfinite K n g) f) := by
  change IsCenterFiniteFamily K n
    (smoothSliceFamily K n (smoothRightAction K n (AdelicGL.ofInfinite K n g) f))
  rw [smoothSliceFamily_infiniteRightAction]
  exact isCenterFiniteFamily_infiniteTranslateFamily K n g hf

/-- Every standard infinite compact translate of an actual automorphic form is automorphic. -/
theorem automorphicCompactTranslation :
    AutomorphicCompactTranslationStatement K n := by
  intro k f hf
  exact ⟨hasFiniteLevel_continuousRightAction K n _ hf.1,
    isInfiniteFinite_infiniteSubgroupRightAction K n _ k hf.2.1,
    isCenterFinite_infiniteRightAction K n k.val hf.2.2.1,
    hasPolynomialGrowth_continuousRightAction K n _ hf.2.2.2⟩

example : ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ),
    AutomorphicCompactTranslationStatement K n :=
  @automorphicCompactTranslation

end Langlands.Automorphic
