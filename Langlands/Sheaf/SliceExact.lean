import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! # Exact and conservative localization of sheaves to a slice site -/
noncomputable section
universe uC vC uA vA uK vK
namespace Langlands.Sheaf
open CategoryTheory CategoryTheory.Limits
variable {C : Type uC} [Category.{vC} C] [HasBinaryProducts C]
variable (J : GrothendieckTopology C) (A : Type uA) [Category.{vA} A] (V : C)

/-- Slice restriction preserves every limit shape that exists in the coefficient category. -/
instance overPullback_preservesLimitsOfShape {K : Type uK} [Category.{vK} K]
    [HasLimitsOfShape K A] : PreservesLimitsOfShape K (J.overPullback A V) := by
  have : PreservesLimitsOfShape K
      (J.overPullback A V ⋙ sheafToPresheaf (J.over V) A) := by
    change PreservesLimitsOfShape K (sheafToPresheaf J A ⋙
      (Functor.whiskeringLeft _ _ _).obj (Over.forget V).op)
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf (J.over V) A)

/-- Slice restriction is a left adjoint, so it preserves colimits of any size. -/
instance overPullback_preservesColimitsOfSize :
    PreservesColimitsOfSize.{vK,uK} (J.overPullback A V) :=
  ((Over.forgetAdjStar V).sheafPushforwardContinuous (J.over V) J).leftAdjoint_preservesColimits

instance overPullback_preservesFiniteLimits [HasFiniteLimits A] :
    PreservesFiniteLimits (J.overPullback A V) where
  preservesFiniteLimits _ _ _ := inferInstance

omit [HasBinaryProducts C] in
/-- A single object covering the site makes slice restriction conservative. -/
theorem overPullbackReflectsIsomorphisms
    (hV : J.CoversTop (fun _ : Unit => V)) : (J.overPullback A V).ReflectsIsomorphisms where
  reflects _ hf := Sheaf.isIso_of_coversTop hV (fun _ => hf)

end Langlands.Sheaf
