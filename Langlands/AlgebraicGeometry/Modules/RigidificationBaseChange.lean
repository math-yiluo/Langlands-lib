import Langlands.AlgebraicGeometry.Modules.Rigidification

/-! # Pullback of rigidified modules along a commuting square -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.SchemeModule.RigidifiedModule

variable {S X S' X' : Scheme.{u}} {ε : S ⟶ X} {ε' : S' ⟶ X'}

/-- The pullback comparison associated to a commuting square of scheme morphisms. -/
def squarePullbackIso (f : X' ⟶ X) (g : S' ⟶ S) (comm : ε' ≫ f = g ≫ ε) :
    Scheme.Modules.pullback ε ⋙ Scheme.Modules.pullback g ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback ε' :=
  Scheme.Modules.pullbackComp g ε ≪≫
    Scheme.Modules.pullbackCongr comm.symm ≪≫
      (Scheme.Modules.pullbackComp ε' f).symm

/-- Pull back a rigidified module, given the structure-module comparison on the base. -/
def pullbackObj (f : X' ⟶ X) (g : S' ⟶ S) (comm : ε' ≫ f = g ≫ ε)
    (unitIso : structureModule S' ≅ (Scheme.Modules.pullback g).obj (structureModule S))
    (M : RigidifiedModule ε) : RigidifiedModule ε' where
  carrier := (Scheme.Modules.pullback f).obj M.carrier
  rigidification := unitIso ≪≫ (Scheme.Modules.pullback g).mapIso M.rigidification ≪≫
    (squarePullbackIso f g comm).app M.carrier

/-- Pullback along a commuting square, with an explicit structure-module comparison. -/
def pullbackWithUnit (f : X' ⟶ X) (g : S' ⟶ S) (comm : ε' ≫ f = g ≫ ε)
    (unitIso : structureModule S' ≅ (Scheme.Modules.pullback g).obj (structureModule S)) :
    RigidifiedModule ε ⥤ RigidifiedModule ε' where
  obj := pullbackObj f g comm unitIso
  map {M N} h := ⟨(Scheme.Modules.pullback f).map h.val, by
    change (unitIso.hom ≫ (Scheme.Modules.pullback g).map M.rigidification.hom ≫
      (squarePullbackIso f g comm).hom.app M.carrier) ≫
        (Scheme.Modules.pullback ε').map ((Scheme.Modules.pullback f).map h.val) =
      unitIso.hom ≫ (Scheme.Modules.pullback g).map N.rigidification.hom ≫
        (squarePullbackIso f g comm).hom.app N.carrier
    have hn := (squarePullbackIso f g comm).hom.naturality h.val
    simp only [Functor.comp_map] at hn
    rw [Category.assoc, Category.assoc, ← hn]
    change unitIso.hom ≫ (Scheme.Modules.pullback g).map M.rigidification.hom ≫
      (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback ε).map h.val) ≫
        (squarePullbackIso f g comm).hom.app N.carrier = _
    rw [← Category.assoc ((Scheme.Modules.pullback g).map M.rigidification.hom),
      ← Functor.map_comp, h.property]⟩
  map_id M := by apply Subtype.ext; exact (Scheme.Modules.pullback f).map_id M.carrier
  map_comp h k := by apply Subtype.ext; exact (Scheme.Modules.pullback f).map_comp h.val k.val

/-- Forgetting the new rigidification recovers the ordinary module pullback. -/
def pullbackWithUnitForgetIso (f : X' ⟶ X) (g : S' ⟶ S) (comm : ε' ≫ f = g ≫ ε)
    (unitIso : structureModule S' ≅ (Scheme.Modules.pullback g).obj (structureModule S)) :
    pullbackWithUnit f g comm unitIso ⋙ forget ε' ≅ forget ε ⋙ Scheme.Modules.pullback f :=
  Iso.refl _

end Langlands.SchemeModule.RigidifiedModule
