import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackStatements
import Langlands.AlgebraicGeometry.Modules.PullbackUnitProofs

/-! # Identity and composition compatibility of canonical rigidified pullback -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.SchemeModule.RigidifiedModule

/-- The pullback comparison `a^* (b^* N) ⟶ c^* N` attached to an equation `a ≫ b = c`. -/
def compHom {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (h : a ≫ b = c)
    (N : Z.Modules) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj N) ⟶
      (Scheme.Modules.pullback c).obj N :=
  (Scheme.Modules.pullbackComp a b).hom.app N ≫ (Scheme.Modules.pullbackCongr h).hom.app N

set_option backward.isDefEq.respectTransparency false in
/-- For the defining equation `a ≫ b = a ≫ b`, the comparison is Mathlib's `pullbackComp`. -/
lemma compHom_rfl {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (N : Z.Modules) :
    compHom a b (a ≫ b) rfl N = (Scheme.Modules.pullbackComp a b).hom.app N := by
  simp [compHom, Scheme.Modules.pullbackCongr]

set_option backward.isDefEq.respectTransparency false in
/-- Associativity of the generalized comparison maps. -/
@[reassoc]
lemma compHom_assoc {X Y Z W : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ W)
    (ab : X ⟶ Z) (bc : Y ⟶ W) (abc : X ⟶ W)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc) (habc : ab ≫ c = abc) (habc' : a ≫ bc = abc)
    (N : W.Modules) :
    compHom a b ab hab ((Scheme.Modules.pullback c).obj N) ≫ compHom ab c abc habc N =
      (Scheme.Modules.pullback a).map (compHom b c bc hbc N) ≫ compHom a bc abc habc' N := by
  subst hab hbc habc
  have h := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity a b c) N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at h
  simp only [compHom, Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_refl, NatTrans.id_app,
    Category.comp_id]
  rw [← cancel_epi ((Scheme.Modules.pullback a).map
      ((Scheme.Modules.pullbackComp b c).inv.app N)),
    ← cancel_epi ((Scheme.Modules.pullbackComp a (b ≫ c)).inv.app N), h]
  simp [← Functor.map_comp_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The generalized comparison when the first map is an identity. -/
lemma compHom_id_left {X Y : Scheme.{u}} (a : X ⟶ Y) (c : X ⟶ Y) (h : 𝟙 X ≫ a = c)
    (N : Y.Modules) :
    compHom (𝟙 X) a c h N =
      (Scheme.Modules.pullbackId X).hom.app ((Scheme.Modules.pullback a).obj N) ≫
        eqToHom (by subst h; simp) := by
  subst h
  have h := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality a) N
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    eqToHom_app] at h
  rw [← cancel_epi ((Scheme.Modules.pullbackComp (𝟙 X) a).inv.app N), reassoc_of% h]
  simp [compHom, Scheme.Modules.pullbackCongr]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse composition comparison when the second map is an identity. -/
lemma pullbackComp_inv_app_comp_pullbackId {X Y : Scheme.{u}} (a : X ⟶ Y) (N : Y.Modules) :
    (Scheme.Modules.pullbackComp a (𝟙 Y)).inv.app N ≫
        (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackId Y).hom.app N) =
      eqToHom (by simp) := by
  have h := NatTrans.congr_app (Scheme.Modules.pseudofunctor_left_unitality a) N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    eqToHom_app] at h
  refine Eq.trans ?_ h
  exact (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of the canonical unit comparison along a composite. -/
lemma pullbackUnitIso_inv_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Langlands.Scheme.Modules.pullbackUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map (Langlands.Scheme.Modules.pullbackUnitIso g).inv ≫
          (Scheme.Modules.pullbackComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf) =
      (Langlands.Scheme.Modules.pullbackUnitIso (f ≫ g)).inv := by
  have h := Langlands.Scheme.Modules.pullbackUnitComposition X Y Z f g
  rw [← Iso.comp_hom_eq_id]
  simp only [Category.assoc, h]
  simp [← Functor.map_comp_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical pulled-back rigidification, followed by the forward comparison. -/
@[reassoc]
lemma pullback_rigidification_hom_comp {S X S' X' : Scheme.{u}} {ε : S ⟶ X}
    {ε' : S' ⟶ X'} (f : X' ⟶ X) (g : S' ⟶ S) (comm : ε' ≫ f = g ≫ ε)
    (M : RigidifiedModule ε) :
    ((pullback f g comm).obj M).rigidification.hom ≫
        (Scheme.Modules.pullbackComp ε' f).hom.app M.carrier =
      (Langlands.Scheme.Modules.pullbackUnitIso g).inv ≫
        (Scheme.Modules.pullback g).map M.rigidification.hom ≫
          compHom g ε (ε' ≫ f) comm.symm M.carrier := by
  change ((Langlands.Scheme.Modules.pullbackUnitIso g).inv ≫
      (Scheme.Modules.pullback g).map M.rigidification.hom ≫
        ((Scheme.Modules.pullbackComp g ε).hom.app M.carrier ≫
          (Scheme.Modules.pullbackCongr comm.symm).hom.app M.carrier ≫
            (Scheme.Modules.pullbackComp ε' f).inv.app M.carrier)) ≫
      (Scheme.Modules.pullbackComp ε' f).hom.app M.carrier = _
  simp [compHom]

set_option backward.isDefEq.respectTransparency false in
/-- The identity comparison preserves the canonical pulled-back rigidification. -/
theorem pullbackIdentity : PullbackIdentityStatement.{u} := by
  intro S X ε comm M
  change ((Langlands.Scheme.Modules.pullbackUnitIso (𝟙 S)).inv ≫
      (Scheme.Modules.pullback (𝟙 S)).map M.rigidification.hom ≫
        (compHom (𝟙 S) ε (ε ≫ 𝟙 X) comm.symm M.carrier ≫
          (Scheme.Modules.pullbackComp ε (𝟙 X)).inv.app M.carrier)) ≫
      (Scheme.Modules.pullback ε).map ((Scheme.Modules.pullbackId X).hom.app M.carrier) = _
  have hu : Langlands.Scheme.Modules.pullbackUnitIso (𝟙 S) =
      (Scheme.Modules.pullbackId S).app (structureModule S) :=
    Iso.ext (Langlands.Scheme.Modules.pullbackUnitIdentity S)
  simp only [Category.assoc, pullbackComp_inv_app_comp_pullbackId, compHom_id_left, hu,
    Iso.app_inv]
  simp only [NatTrans.naturality_assoc, Functor.id_map]
  erw [Iso.inv_hom_id_app_assoc]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The composition comparison preserves the canonical pulled-back rigidifications. -/
theorem pullbackComposition : PullbackCompositionStatement.{u} := by
  intro S X S' X' S'' X'' ε ε' ε'' f g f' g' comm comm' comm'' M
  have hE : g' ≫ ε' ≫ f = ε'' ≫ f' ≫ f := by
    rw [← Category.assoc, ← comm', Category.assoc]
  have e1 := compHom_assoc ε'' f' f (ε'' ≫ f') (f' ≫ f) (ε'' ≫ f' ≫ f) rfl rfl
    (Category.assoc _ _ _) rfl M.carrier
  have e2 := compHom_assoc g' ε' f (ε'' ≫ f') (ε' ≫ f) (ε'' ≫ f' ≫ f) comm'.symm rfl
    (Category.assoc _ _ _) hE M.carrier
  have e3 := compHom_assoc g' g ε (g' ≫ g) (ε' ≫ f) (ε'' ≫ f' ≫ f) rfl comm.symm
    comm''.symm hE M.carrier
  have e4 := (Scheme.Modules.pullbackComp g' g).hom.naturality M.rigidification.hom
  simp only [compHom_rfl] at e1 e2 e3
  simp only [Functor.comp_map] at e4
  rw [← cancel_mono ((Scheme.Modules.pullbackComp ε'' (f' ≫ f)).hom.app M.carrier),
    pullback_rigidification_hom_comp, Category.assoc, ← e1]
  erw [pullback_rigidification_hom_comp_assoc]
  erw [e2]
  rw [← Functor.map_comp_assoc, pullback_rigidification_hom_comp]
  simp only [Functor.map_comp, Category.assoc]
  rw [← e3, reassoc_of% e4]
  erw [reassoc_of% (pullbackUnitIso_inv_comp g' g)]

/-- Identity and composition compatibility of canonical rigidified pullback. -/
theorem pullbackCoherence : PullbackCoherenceStatement.{u} :=
  ⟨pullbackIdentity, pullbackComposition⟩

end Langlands.SchemeModule.RigidifiedModule
