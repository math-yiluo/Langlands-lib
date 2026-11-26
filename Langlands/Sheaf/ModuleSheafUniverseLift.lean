import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Sites.Whiskering

/-! # Universe lift of module-valued sheaves -/

noncomputable section

universe u v w

namespace Langlands.Sheaf

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type w) [Ring R]

/-- The module lift preserves sheaves even when the sieves live above the original
module universe. The forgetful functor on the source is a right adjoint and the
forgetful functor on the target reflects the shape limits of the sheaf condition. -/
instance moduleUniverseLift_hasSheafCompose :
    J.HasSheafCompose (ModuleCat.uliftFunctor.{max u v, w} R) := by
  let F := ModuleCat.uliftFunctor.{max u v, w} R
  let G := forget (ModuleCat.{max u v w} R)
  have : PreservesLimitsOfSize.{v, max u v} (forget (ModuleCat.{w} R)) :=
    (ModuleCat.adj R).rightAdjoint_preservesLimits
  have : PreservesLimitsOfSize.{v, max u v} (F ⋙ G) := by
    change PreservesLimitsOfSize.{v, max u v} (forget (ModuleCat.{w} R) ⋙
      CategoryTheory.uliftFunctor.{max u v, w})
    infer_instance
  have : ReflectsLimitsOfSize.{max u v w, max u v w} G :=
    reflectsLimits_of_reflectsIsomorphisms (G := G)
  have : ReflectsLimitsOfSize.{v, max u v} G :=
    reflectsLimitsOfSize_shrink.{max u v, w, v, max u w} G
  have : PreservesLimitsOfSize.{v, max u v} F :=
    preservesLimits_of_reflects_of_preserves F G
  exact hasSheafCompose_of_preservesLimitsOfSize J (F := F)

/-- Lift the sections and restriction maps of a sheaf of modules to the universe
of the site, keeping the same coefficient ring. -/
def moduleSheafUniverseLift : Sheaf J (ModuleCat.{w} R) ⥤ Sheaf J (ModuleCat.{max u v w} R) :=
  sheafCompose J (ModuleCat.uliftFunctor.{max u v, w} R)

instance : (moduleSheafUniverseLift J R).Full := inferInstanceAs (sheafCompose J _).Full
instance : (moduleSheafUniverseLift J R).Faithful := inferInstanceAs (sheafCompose J _).Faithful

end Langlands.Sheaf
