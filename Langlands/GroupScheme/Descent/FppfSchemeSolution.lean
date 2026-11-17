import Langlands.GroupScheme.Descent.SchemeSolution
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Quotient maps of scheme solutions along fppf covers -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

universe u

namespace Langlands.GroupScheme.Descent

variable {B S : Scheme.{u}} {p : S ⟶ B} {G : GroupScheme S}

namespace SchemeSolution

variable {D : Datum p G} (s : SchemeSolution D)

instance proj_locallyOfFinitePresentation [LocallyOfFinitePresentation p] :
    LocallyOfFinitePresentation s.proj :=
  MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) s.square inferInstance

variable [Flat p] [LocallyOfFinitePresentation p] [Surjective p]


/-- Any map constant on the datum's relation factors through the actual quotient. -/
def fppfDesc {T : Scheme.{u}} (f : G.X.left ⟶ T)
    (hf : D.source ≫ f = D.target ≫ f) : s.obj.left ⟶ T :=
  EffectiveEpi.desc s.proj f (fun a b hab => s.comp_eq_of_proj_eq f hf a b hab)

@[reassoc] theorem fppfDesc_fac {T : Scheme.{u}} (f : G.X.left ⟶ T)
    (hf : D.source ≫ f = D.target ≫ f) : s.proj ≫ s.fppfDesc f hf = f := by
  exact EffectiveEpi.fac s.proj f (fun a b hab => s.comp_eq_of_proj_eq f hf a b hab)

theorem fppfDesc_unique {T : Scheme.{u}} (f : G.X.left ⟶ T)
    (hf : D.source ≫ f = D.target ≫ f) (a : s.obj.left ⟶ T)
    (ha : s.proj ≫ a = f) : a = s.fppfDesc f hf := by
  apply (cancel_epi s.proj).mp
  rw [ha, s.fppfDesc_fac]

end SchemeSolution

end Langlands.GroupScheme.Descent
