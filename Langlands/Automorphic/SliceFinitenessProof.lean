import Langlands.Automorphic.SliceFinitenessStatement

/-! # Finiteness transport to actual smooth infinite slices -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.SliceFinitenessProof

open Langlands.Global

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Evaluation of a smooth family intertwines the actual center actions. -/
def centerEvaluation (b : FiniteAdelicGL K n) :
    (centerFamilyRepresentation K n).IntertwiningMap
      (ArchimedeanGL.centerRepresentation K n) where
  toLinearMap := LinearMap.proj b
  isIntertwining' _ := rfl

theorem centerFiniteFamilyEvaluation : CenterFiniteFamilyEvaluationStatement K n := by
  intro F hF b
  exact FiniteVectors.IsFiniteVector.map (centerEvaluation K n b) hF

/-- The actual smooth adelic action restricted to an infinite-factor subgroup. -/
def smoothSubgroupAction (U : Subgroup (InfiniteAdelicGL K n)) :
    Representation ℂ U (SmoothRationalFunctions K n) :=
  (smoothRightAction K n).comp
    ((AdelicGL.ofInfinite K n).toMonoidHom.comp U.subtype)

/-- The smooth inclusion remains equivariant on the restricted actions. -/
def smoothSubgroupInclusion (U : Subgroup (InfiniteAdelicGL K n)) :
    (smoothSubgroupAction K n U).IntertwiningMap
      (infiniteSubgroupRightAction K n U) where
  toLinearMap := (smoothInclusion K n).toLinearMap
  isIntertwining' _ := by ext; rfl

/-- Taking a smooth slice commutes with the actual infinite-subgroup translations. -/
def smoothSliceIntertwiner (U : Subgroup (InfiniteAdelicGL K n))
    (b : FiniteAdelicGL K n) :
    (smoothSubgroupAction K n U).IntertwiningMap
      ((ArchimedeanGL.smoothRightAction K n).comp U.subtype) where
  toLinearMap := smoothInfiniteSlice K n b
  isIntertwining' k := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext a
    change ContinuousRationalFunctions.evaluate K n f.val
        (AdelicGL.pair K n a b * AdelicGL.ofInfinite K n k.val) =
      ContinuousRationalFunctions.evaluate K n f.val (AdelicGL.pair K n (a * k.val) b)
    rw [AdelicGL.ofInfinite_eq_pair, AdelicGL.pair_mul, mul_one]

theorem smoothSliceSubgroupFinite : SmoothSliceSubgroupFiniteStatement K n := by
  intro U f hf b
  let : AddCommGroup (SmoothRationalFunctions K n) :=
    Module.addCommMonoidToAddCommGroup ℂ
  have hs : @FiniteVectors.IsFiniteVector ℂ (inferInstance) U (inferInstance)
      (SmoothRationalFunctions K n) (inferInstance) (inferInstance)
      (smoothSubgroupAction K n U) f :=
    (@FiniteVectors.isFiniteVector_map_iff ℂ (inferInstance) U (inferInstance)
      (SmoothRationalFunctions K n) (inferInstance) (inferInstance)
      (ContinuousRationalFunctions K n) (inferInstance) (inferInstance)
      (smoothSubgroupAction K n U) (infiniteSubgroupRightAction K n U)
      (smoothSubgroupInclusion K n U) Subtype.val_injective f).mp hf
  exact @FiniteVectors.IsFiniteVector.map ℂ (inferInstance) U (inferInstance)
    (SmoothRationalFunctions K n) (inferInstance) (inferInstance)
    (ArchimedeanGL.SmoothFunctions K n) (inferInstance) (inferInstance)
    (smoothSubgroupAction K n U) ((ArchimedeanGL.smoothRightAction K n).comp U.subtype)
    (smoothSliceIntertwiner K n U b) f hs

/-- Both transports, for the exact published target and full parameter telescope. -/
theorem sliceFiniteness : SliceFinitenessStatement K n :=
  ⟨centerFiniteFamilyEvaluation K n, smoothSliceSubgroupFinite K n⟩

end Langlands.Automorphic.SliceFinitenessProof
