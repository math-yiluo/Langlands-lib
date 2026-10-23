import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs

/-! # Canonical rigidified pullback preserves the trivial bundle -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.SchemeModule.RigidifiedModule

set_option backward.isDefEq.respectTransparency false in
/-- The inverse unit comparison along a specified composite. -/
lemma pullbackUnitIso_inv_compHom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (eq : f ≫ g = h) :
    (Langlands.Scheme.Modules.pullbackUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map (Langlands.Scheme.Modules.pullbackUnitIso g).inv ≫
          compHom f g h eq (SheafOfModules.unit Z.ringCatSheaf) =
      (Langlands.Scheme.Modules.pullbackUnitIso h).inv := by
  subst eq
  rw [compHom_rfl]
  exact pullbackUnitIso_inv_comp f g

end Langlands.SchemeModule.RigidifiedModule

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.SchemeModule

variable {S X S' X' : Scheme.{u}} {ε : S ⟶ X} {ε' : S' ⟶ X'}

set_option backward.isDefEq.respectTransparency false in
/-- The canonical unit comparison respects the pulled-back trivial rigidification. -/
lemma pullbackTrivial_compatibility (f : X' ⟶ X) (g : S' ⟶ S)
    (comm : ε' ≫ f = g ≫ ε) :
    ((pullback f g comm).obj (trivial ε)).obj.rigidification.hom ≫
        (Scheme.Modules.pullback ε').map (Langlands.Scheme.Modules.pullbackUnitIso f).hom =
      (Langlands.Scheme.Modules.pullbackUnitIso ε').inv := by
  rw [← cancel_mono (Langlands.Scheme.Modules.pullbackUnitIso ε').hom,
    Iso.inv_hom_id, Category.assoc,
    ← Langlands.Scheme.Modules.pullbackUnitComposition S' X' X ε' f,
    ← Category.assoc]
  change (((RigidifiedModule.pullback f g comm).obj (trivial ε).obj).rigidification.hom ≫
      (Scheme.Modules.pullbackComp ε' f).hom.app (structureModule X)) ≫ _ = _
  erw [RigidifiedModule.pullback_rigidification_hom_comp f g comm (trivial ε).obj]
  change ((Langlands.Scheme.Modules.pullbackUnitIso g).inv ≫
      (Scheme.Modules.pullback g).map (Langlands.Scheme.Modules.pullbackUnitIso ε).inv ≫
        RigidifiedModule.compHom g ε (ε' ≫ f) comm.symm (structureModule X)) ≫ _ = _
  erw [RigidifiedModule.pullbackUnitIso_inv_compHom g ε (ε' ≫ f) comm.symm]
  exact Iso.inv_hom_id _

/-- Actual pullback of the canonically rigidified trivial bundle is canonically trivial. -/
def pullbackTrivialIso (f : X' ⟶ X) (g : S' ⟶ S) (comm : ε' ≫ f = g ≫ ε) :
    (pullback f g comm).obj (trivial ε) ≅ trivial ε' :=
  isoMk (Langlands.Scheme.Modules.pullbackUnitIso f)
    (pullbackTrivial_compatibility f g comm)

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
