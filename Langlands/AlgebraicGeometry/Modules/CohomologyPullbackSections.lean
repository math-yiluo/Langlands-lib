import Langlands.AlgebraicGeometry.Modules.PushforwardComparison
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Elementary sections and coefficient comparisons for cohomology pullback
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)}

/-- Pushforward followed by relative sections agrees with relative sections
on the source of a morphism over the affine base. -/
def relativePushforwardSectionsIso (h : Y ⟶ X) :
    Scheme.Modules.pushforward h.left ⋙ relativeGlobalSections X.hom ≅
      relativeGlobalSections Y.hom :=
  relativeGlobalSectionsCompIso h.left X.hom ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.pushforwardCongr h.w) moduleSpecΓFunctor

/-- Pullback of relative sections, induced by the actual pullback/pushforward
adjunction unit and the pushforward comparison. -/
def relativeGlobalSectionsPullback (h : Y ⟶ X) (M : X.left.Modules) :
    (relativeGlobalSections X.hom).obj M ⟶
      (relativeGlobalSections Y.hom).obj ((Scheme.Modules.pullback h.left).obj M) :=
  (relativeGlobalSections X.hom).map
      ((Scheme.Modules.pullbackPushforwardAdjunction h.left).unit.app M) ≫
    (relativePushforwardSectionsIso h).hom.app _

/-- Canonical identification of the twice-pulled-back coefficients of a
split pair with the original coefficients. -/
def relativeCohomologySplitCoefficientIso
    (m : Y ⟶ X) (j : X ⟶ Y) (w : j ≫ m = 𝟙 X) :
    Scheme.Modules.pullback m.left ⋙ Scheme.Modules.pullback j.left ≅
      𝟭 X.left.Modules :=
  Scheme.Modules.pullbackComp j.left m.left ≪≫
    Scheme.Modules.pullbackCongr (congrArg (fun f : X ⟶ X => f.left) w) ≪≫
    Scheme.Modules.pullbackId X.left

end Langlands.AlgebraicGeometry.Modules.DerivedSections
