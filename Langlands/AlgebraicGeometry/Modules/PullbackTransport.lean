import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescentUniquenessProof
import Langlands.AlgebraicGeometry.Modules.EqualCompositePullback
import Langlands.AlgebraicGeometry.Modules.PullbackUnitProofs
import Langlands.AlgebraicGeometry.ModuleLocalHomPullbackProofs
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs
import Langlands.AlgebraicGeometry.Picard.RigidifiedIsoUniquenessProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

/-! # Transport of morphisms between pullbacks along further pullbacks -/

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.Scheme.Modules

open Langlands.SchemeModule.RigidifiedModule

variable {Z : Scheme.{u}}

/-- The canonical comparison `g^* (u^* C) ≅ u'^* C` attached to an equation `g ≫ u = u'`. -/
def compIso {X Y : Scheme.{u}} (g : X ⟶ Y) (u : Y ⟶ Z) (u' : X ⟶ Z) (h : g ≫ u = u')
    (C : Z.Modules) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback u).obj C) ≅
      (Scheme.Modules.pullback u').obj C :=
  UnitCocycleDescentUniqueness.compIso g u u' h C

lemma compIso_hom {X Y : Scheme.{u}} (g : X ⟶ Y) (u : Y ⟶ Z) (u' : X ⟶ Z) (h : g ≫ u = u')
    (C : Z.Modules) : (compIso g u u' h C).hom = compHom g u u' h C :=
  UnitCocycleDescentUniqueness.compIso_hom g u u' h C

/-- Transport a morphism `u^* C ⟶ v^* D` along `g`, identifying the pullbacks with the
pullbacks along prescribed composites `u'` and `v'`. -/
def transport {X Y : Scheme.{u}} (g : X ⟶ Y) {C D : Z.Modules} {u v : Y ⟶ Z} {u' v' : X ⟶ Z}
    (hu : g ≫ u = u') (hv : g ≫ v = v')
    (φ : (Scheme.Modules.pullback u).obj C ⟶ (Scheme.Modules.pullback v).obj D) :
    (Scheme.Modules.pullback u').obj C ⟶ (Scheme.Modules.pullback v').obj D :=
  (compIso g u u' hu C).inv ≫ (Scheme.Modules.pullback g).map φ ≫ (compIso g v v' hv D).hom

section Transport

variable {X Y : Scheme.{u}} (g : X ⟶ Y) {C D E : Z.Modules} {u v w : Y ⟶ Z}
  {u' v' w' : X ⟶ Z}

@[simp]
lemma transport_id (hu : g ≫ u = u') :
    transport g hu hu (𝟙 ((Scheme.Modules.pullback u).obj C)) = 𝟙 _ := by
  simp [transport]

@[reassoc]
lemma transport_comp (hu : g ≫ u = u') (hv : g ≫ v = v') (hw : g ≫ w = w')
    (φ : (Scheme.Modules.pullback u).obj C ⟶ (Scheme.Modules.pullback v).obj D)
    (ψ : (Scheme.Modules.pullback v).obj D ⟶ (Scheme.Modules.pullback w).obj E) :
    transport g hu hw (φ ≫ ψ) = transport g hu hv φ ≫ transport g hv hw ψ := by
  simp [transport]

lemma transport_congr {g g' : X ⟶ Y} (e : g = g') (hu : g ≫ u = u') (hv : g ≫ v = v')
    (hu' : g' ≫ u = u') (hv' : g' ≫ v = v')
    (φ : (Scheme.Modules.pullback u).obj C ⟶ (Scheme.Modules.pullback v).obj D) :
    transport g hu hv φ = transport g' hu' hv' φ := by
  subst e
  rfl

lemma transport_smul (hu : g ≫ u = u') (hv : g ≫ v = v') (r : Γ(Y, ⊤))
    (φ : (Scheme.Modules.pullback u).obj C ⟶ (Scheme.Modules.pullback v).obj D) :
    transport g hu hv (r • φ) = g.appTop r • transport g hu hv φ := by
  simp only [transport, pullback_map_smul, Linear.comp_smul, Linear.smul_comp]

instance transport_isIso (hu : g ≫ u = u') (hv : g ≫ v = v')
    (φ : (Scheme.Modules.pullback u).obj C ⟶ (Scheme.Modules.pullback v).obj D) [IsIso φ] :
    IsIso (transport g hu hv φ) := by
  unfold transport
  infer_instance

/-- Transport along a composite is iterated transport. -/
lemma transport_transport {W : Scheme.{u}} (g' : W ⟶ X) {u'' v'' : W ⟶ Z}
    (hu : g ≫ u = u') (hv : g ≫ v = v') (hu' : g' ≫ u' = u'') (hv' : g' ≫ v' = v'')
    (hu'' : (g' ≫ g) ≫ u = u'') (hv'' : (g' ≫ g) ≫ v = v'')
    (φ : (Scheme.Modules.pullback u).obj C ⟶ (Scheme.Modules.pullback v).obj D) :
    transport g' hu' hv' (transport g hu hv φ) = transport (g' ≫ g) hu'' hv'' φ := by
  have eC : (Scheme.Modules.pullback g').map (compIso g u u' hu C).hom ≫
      (compIso g' u' u'' hu' C).hom =
        (Scheme.Modules.pullbackComp g' g).hom.app ((Scheme.Modules.pullback u).obj C) ≫
          (compIso (g' ≫ g) u u'' hu'' C).hom := by
    rw [compIso_hom, compIso_hom, compIso_hom, ← compHom_rfl]
    exact (compHom_assoc g' g u (g' ≫ g) u' u'' rfl hu hu'' hu' C).symm
  have eD : (Scheme.Modules.pullback g').map (compIso g v v' hv D).hom ≫
      (compIso g' v' v'' hv' D).hom =
        (Scheme.Modules.pullbackComp g' g).hom.app ((Scheme.Modules.pullback v).obj D) ≫
          (compIso (g' ≫ g) v v'' hv'' D).hom := by
    rw [compIso_hom, compIso_hom, compIso_hom, ← compHom_rfl]
    exact (compHom_assoc g' g v (g' ≫ g) v' v'' rfl hv hv'' hv' D).symm
  have eC' : (compIso g' u' u'' hu' C).inv ≫
      (Scheme.Modules.pullback g').map (compIso g u u' hu C).inv =
        (compIso (g' ≫ g) u u'' hu'' C).inv ≫
          (Scheme.Modules.pullbackComp g' g).inv.app ((Scheme.Modules.pullback u).obj C) := by
    rw [← cancel_mono ((Scheme.Modules.pullback g').map (compIso g u u' hu C).hom),
      ← cancel_mono (compIso g' u' u'' hu' C).hom]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rw [eC]
    simp
  have nat := (Scheme.Modules.pullbackComp g' g).hom.naturality φ
  simp only [Functor.comp_map] at nat
  unfold transport
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% eC', eD, reassoc_of% nat]
  simp

/-- Iterated transport along a composite equal to a prescribed map. -/
lemma transport_transport_eq {W : Scheme.{u}} (g' : W ⟶ X) {k : W ⟶ Y} (hk : g' ≫ g = k)
    {u'' v'' : W ⟶ Z} (hu : g ≫ u = u') (hv : g ≫ v = v') (hu' : g' ≫ u' = u'')
    (hv' : g' ≫ v' = v'') (hu'' : k ≫ u = u'') (hv'' : k ≫ v = v'')
    (φ : (Scheme.Modules.pullback u).obj C ⟶ (Scheme.Modules.pullback v).obj D) :
    transport g' hu' hv' (transport g hu hv φ) = transport k hu'' hv'' φ := by
  subst hk
  exact transport_transport g g' hu hv hu' hv' hu'' hv'' φ

end Transport

section Unit

/-- The canonical identification of the pullbacks of the structure sheaf along two maps. -/
def unitTransfer {X : Scheme.{u}} (a b : X ⟶ Z) :
    (Scheme.Modules.pullback a).obj (SheafOfModules.unit Z.ringCatSheaf) ⟶
      (Scheme.Modules.pullback b).obj (SheafOfModules.unit Z.ringCatSheaf) :=
  (pullbackUnitIso a).hom ≫ (pullbackUnitIso b).inv

variable {X Y : Scheme.{u}}

instance (a b : X ⟶ Z) : IsIso (unitTransfer a b) := by
  unfold unitTransfer
  infer_instance

@[simp]
lemma unitTransfer_self (a : X ⟶ Z) : unitTransfer a a = 𝟙 _ := by
  simp [unitTransfer]

@[reassoc (attr := simp)]
lemma unitTransfer_comp (a b c : X ⟶ Z) :
    unitTransfer a b ≫ unitTransfer b c = unitTransfer a c := by
  simp [unitTransfer]

set_option backward.isDefEq.respectTransparency false in
/-- The composition comparison is compatible with the canonical unit comparisons. -/
lemma compIso_unit (g : X ⟶ Y) (a : Y ⟶ Z) (a' : X ⟶ Z) (h : g ≫ a = a') :
    (compIso g a a' h (SheafOfModules.unit Z.ringCatSheaf)).hom ≫ (pullbackUnitIso a').hom =
      (Scheme.Modules.pullback g).map (pullbackUnitIso a).hom ≫ (pullbackUnitIso g).hom := by
  subst h
  rw [← pullbackUnitComposition X Y Z g a]
  simp [compIso, UnitCocycleDescentUniqueness.compIso, Scheme.Modules.pullbackCongr]

lemma transport_unitTransfer (g : X ⟶ Y) {a b : Y ⟶ Z} {a' b' : X ⟶ Z}
    (ha : g ≫ a = a') (hb : g ≫ b = b') :
    transport g ha hb (unitTransfer a b) = unitTransfer a' b' := by
  have h1 := compIso_unit g a a' ha
  have h2 := compIso_unit g b b' hb
  unfold transport unitTransfer
  rw [← cancel_epi (compIso g a a' ha _).hom, Iso.hom_inv_id_assoc, reassoc_of% h1,
    ← cancel_mono (pullbackUnitIso b').hom]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id, h2]
  simp [← Functor.map_comp_assoc]

end Unit

section Constancy

variable {X Y : Scheme.{u}} (pr : Y ⟶ X) [IsIso pr.appTop]

/-- On a scheme whose global functions all come from `X` along `pr`, a morphism from a line
bundle is a constant multiple of any isomorphism: there is a global function on `X`
relating their transports along every section of `pr`. -/
lemma exists_transport_eq_smul {C D : Z.Modules} {u v : Y ⟶ Z}
    (hC : Langlands.AlgebraicGeometry.Picard.IsLocallyFreeRankOne
      ((Scheme.Modules.pullback u).obj C))
    (φ ψ : (Scheme.Modules.pullback u).obj C ⟶ (Scheme.Modules.pullback v).obj D) [IsIso ψ] :
    ∃ c : Γ(X, ⊤), ∀ (s : X ⟶ Y) (_ : s ≫ pr = 𝟙 X) {u' v' : X ⟶ Z}
      (hu : s ≫ u = u') (hv : s ≫ v = v'),
        transport s hu hv φ = c • transport s hu hv ψ := by
  obtain ⟨d, hd⟩ := exists_eq_smul_id_of_isLocallyFreeRankOne hC (φ ≫ inv ψ)
  have hφ : φ = d • ψ := by
    calc φ = (φ ≫ inv ψ) ≫ ψ := by simp
      _ = d • ψ := by rw [hd, Linear.smul_comp, Category.id_comp]
  refine ⟨(inv pr.appTop) d, fun s hs u' v' hu hv => ?_⟩
  rw [hφ, transport_smul]
  congr 1
  have e : s.appTop (pr.appTop ((inv pr.appTop) d)) = (inv pr.appTop) d := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hs, Scheme.Hom.id_appTop]
    rfl
  rw [← e]
  congr 1
  rw [← CommRingCat.comp_apply, IsIso.inv_hom_id]
  rfl

end Constancy

section EqualComposite

variable {U X Y' : Scheme.{u}} (p : X ⟶ Y') (q : Y' ⟶ Z) (C : Z.Modules)

/-- The canonical comparison along equal composites is compatible with the composition
comparisons for a further map `q`. -/
lemma equalCompositeIso_hom_compIso (a b : U ⟶ X) (h : a ≫ p = b ≫ p) {w : U ⟶ Z}
    (ha : a ≫ (p ≫ q) = w) (hb : b ≫ (p ≫ q) = w) :
    (equalCompositeIso p a b h ((Scheme.Modules.pullback q).obj C)).hom ≫
        (Scheme.Modules.pullback b).map (compIso p q (p ≫ q) rfl C).hom ≫
          (compIso b (p ≫ q) w hb C).hom =
      (Scheme.Modules.pullback a).map (compIso p q (p ≫ q) rfl C).hom ≫
        (compIso a (p ≫ q) w ha C).hom := by
  have e1 := compHom_assoc b p q (b ≫ p) (p ≫ q) w rfl rfl
    (by rw [Category.assoc, hb]) hb C
  have e2 := compHom_assoc a p q (b ≫ p) (p ≫ q) w h rfl
    (by rw [Category.assoc, hb]) ha C
  rw [compHom_rfl] at e1
  rw [equalCompositeIso_hom_eq_compHom, compIso_hom, compIso_hom, compIso_hom, Category.assoc,
    ← e1, Iso.inv_hom_id_app_assoc, e2]

/-- If the transports of a trivialization `α'` along `a` and `b` agree up to the canonical
unit comparison, then the transported automorphism along `a, b` is trivial. -/
lemma equalCompositeUnitAut_eq_refl_of_transport {m : X ⟶ Z}
    (α' : (Scheme.Modules.pullback (p ≫ q)).obj C ⟶
      (Scheme.Modules.pullback m).obj (SheafOfModules.unit Z.ringCatSheaf)) [IsIso α']
    (a b : U ⟶ X) (h : a ≫ p = b ≫ p) {w a' b' : U ⟶ Z}
    (ha : a ≫ (p ≫ q) = w) (hb : b ≫ (p ≫ q) = w) (ha' : a ≫ m = a') (hb' : b ≫ m = b')
    (heq : transport a ha ha' α' ≫ unitTransfer a' b' = transport b hb hb' α') :
    equalCompositeUnitAut p a b h
        (compIso p q (p ≫ q) rfl C ≪≫ asIso α' ≪≫ pullbackUnitIso m) = Iso.refl _ := by
  subst ha' hb'
  have hE := equalCompositeIso_hom_compIso p q C a b h ha hb
  have key : ∀ (c : U ⟶ X) (hc : c ≫ (p ≫ q) = w),
      (Scheme.Modules.pullback c).map α' ≫
          (Scheme.Modules.pullback c).map (pullbackUnitIso m).hom ≫ (pullbackUnitIso c).hom =
        (compIso c (p ≫ q) w hc C).hom ≫ transport c hc rfl α' ≫
          (pullbackUnitIso (c ≫ m)).hom := by
    intro c hc
    rw [← compIso_unit c m (c ≫ m) rfl]
    unfold transport
    simp
  have main : (equalCompositeIso p a b h ((Scheme.Modules.pullback q).obj C)).hom ≫
      (Scheme.Modules.pullback b).map (compIso p q (p ≫ q) rfl C).hom ≫
        (Scheme.Modules.pullback b).map α' ≫
          (Scheme.Modules.pullback b).map (pullbackUnitIso m).hom ≫ (pullbackUnitIso b).hom =
      (Scheme.Modules.pullback a).map (compIso p q (p ≫ q) rfl C).hom ≫
        (Scheme.Modules.pullback a).map α' ≫
          (Scheme.Modules.pullback a).map (pullbackUnitIso m).hom ≫ (pullbackUnitIso a).hom := by
    rw [key b hb, reassoc_of% hE, ← heq, key a ha]
    simp only [unitTransfer, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  ext1
  rw [equalCompositeUnitAut_hom, Iso.refl_hom]
  simp only [Iso.trans_hom, Iso.trans_inv, asIso_hom, asIso_inv, Functor.map_comp,
    Category.assoc]
  rw [main]
  simp

end EqualComposite

section Rigidified

open Langlands.SchemeModule

variable {S X S' X' : Scheme.{u}} {ε : S ⟶ X} {ε' : S' ⟶ X'}

/-- The rigidification of a rigidified module, as a morphism out of the pulled-back
structure sheaf. -/
def sectionMap (L : RigidifiedModule ε) :
    (Scheme.Modules.pullback ε).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
      (Scheme.Modules.pullback ε).obj L.carrier :=
  (pullbackUnitIso ε).hom ≫ L.rigidification.hom

instance (L : RigidifiedModule ε) : IsIso (sectionMap L) := by
  unfold sectionMap
  infer_instance

/-- The rigidification of a pulled-back rigidified module is the transported section map. -/
lemma pullback_rigidification_compIso (L : RigidifiedModule ε) (f : X' ⟶ X) (g : S' ⟶ S)
    (comm : ε' ≫ f = g ≫ ε) {w : S' ⟶ X} (h : ε' ≫ f = w) (hg : g ≫ ε = w) :
    ((RigidifiedModule.pullback f g comm).obj L).rigidification.hom ≫
        (compIso ε' f w h L.carrier).hom =
      (pullbackUnitIso w).inv ≫ transport g hg hg (sectionMap L) := by
  have hu := compIso_unit g ε w hg
  have hsq : (RigidifiedModule.squarePullbackIso f g comm).hom.app L.carrier ≫
      (compIso ε' f w h L.carrier).hom = (compIso g ε w hg L.carrier).hom := by
    subst h
    rw [compIso_hom, compHom_rfl, compIso_hom]
    simp only [RigidifiedModule.squarePullbackIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rfl
  have hinv : (pullbackUnitIso w).inv ≫
      (compIso g ε w hg (SheafOfModules.unit X.ringCatSheaf)).inv =
      (pullbackUnitIso g).inv ≫ (Scheme.Modules.pullback g).map (pullbackUnitIso ε).inv := by
    rw [← cancel_mono ((Scheme.Modules.pullback g).map (pullbackUnitIso ε).hom),
      ← cancel_mono (pullbackUnitIso g).hom]
    simp only [Category.assoc]
    rw [Iso.map_inv_hom_id_assoc, Iso.inv_hom_id, ← hu]
    simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id]
  change ((pullbackUnitIso g).inv ≫ (Scheme.Modules.pullback g).map L.rigidification.hom ≫
    (RigidifiedModule.squarePullbackIso f g comm).hom.app L.carrier) ≫ _ = _
  unfold transport sectionMap
  rw [Category.assoc, Category.assoc, hsq, reassoc_of% hinv]
  simp only [Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc]

/-- A rigidified morphism between two pullbacks of a rigidified module intertwines the
transported section maps. -/
lemma transport_sectionMap_comp_of_hom (L : RigidifiedModule ε)
    {f₁ f₂ : X' ⟶ X} {g₁ g₂ : S' ⟶ S} (comm₁ : ε' ≫ f₁ = g₁ ≫ ε)
    (comm₂ : ε' ≫ f₂ = g₂ ≫ ε)
    (Φ : (Scheme.Modules.pullback f₁).obj L.carrier ⟶ (Scheme.Modules.pullback f₂).obj L.carrier)
    (hΦ : ((RigidifiedModule.pullback f₁ g₁ comm₁).obj L).rigidification.hom ≫
        (Scheme.Modules.pullback ε').map Φ =
      ((RigidifiedModule.pullback f₂ g₂ comm₂).obj L).rigidification.hom)
    {w₁ w₂ : S' ⟶ X} (h₁ : ε' ≫ f₁ = w₁) (hg₁ : g₁ ≫ ε = w₁) (h₂ : ε' ≫ f₂ = w₂)
    (hg₂ : g₂ ≫ ε = w₂) :
    transport g₁ hg₁ hg₁ (sectionMap L) ≫ transport ε' h₁ h₂ Φ =
      unitTransfer w₁ w₂ ≫ transport g₂ hg₂ hg₂ (sectionMap L) := by
  have e₁ := pullback_rigidification_compIso L f₁ g₁ comm₁ h₁ hg₁
  have e₂ := pullback_rigidification_compIso L f₂ g₂ comm₂ h₂ hg₂
  rw [← cancel_epi (pullbackUnitIso w₁).inv, ← reassoc_of% e₁]
  unfold unitTransfer
  rw [Category.assoc, Iso.inv_hom_id_assoc, ← e₂, ← hΦ]
  unfold transport
  simp

/-- The intertwining of `transport_sectionMap_comp_of_hom`, transported further along a
map `k` into the base of the section. -/
lemma transport_sectionMap_comp_of_hom_comp (L : RigidifiedModule ε)
    {f₁ f₂ : X' ⟶ X} {g₁ g₂ : S' ⟶ S} (comm₁ : ε' ≫ f₁ = g₁ ≫ ε)
    (comm₂ : ε' ≫ f₂ = g₂ ≫ ε)
    (Φ : (Scheme.Modules.pullback f₁).obj L.carrier ⟶ (Scheme.Modules.pullback f₂).obj L.carrier)
    (hΦ : ((RigidifiedModule.pullback f₁ g₁ comm₁).obj L).rigidification.hom ≫
        (Scheme.Modules.pullback ε').map Φ =
      ((RigidifiedModule.pullback f₂ g₂ comm₂).obj L).rigidification.hom)
    {V : Scheme.{u}} (k : V ⟶ S') {k₁ k₂ : V ⟶ S} (hk₁ : k ≫ g₁ = k₁) (hk₂ : k ≫ g₂ = k₂)
    {w₁ w₂ : V ⟶ X} (h₁ : (k ≫ ε') ≫ f₁ = w₁) (hg₁ : k₁ ≫ ε = w₁)
    (h₂ : (k ≫ ε') ≫ f₂ = w₂) (hg₂ : k₂ ≫ ε = w₂) :
    transport k₁ hg₁ hg₁ (sectionMap L) ≫ transport (k ≫ ε') h₁ h₂ Φ =
      unitTransfer w₁ w₂ ≫ transport k₂ hg₂ hg₂ (sectionMap L) := by
  have H := transport_sectionMap_comp_of_hom L comm₁ comm₂ Φ hΦ rfl comm₁.symm rfl comm₂.symm
  have h₁' : k ≫ (ε' ≫ f₁) = w₁ := by rw [← Category.assoc, h₁]
  have h₂' : k ≫ (ε' ≫ f₂) = w₂ := by rw [← Category.assoc, h₂]
  have H' := congrArg (transport k h₁' h₂') H
  rw [transport_comp k h₁' h₁' h₂', transport_comp k h₁' h₂' h₂',
    transport_transport_eq g₁ k hk₁ _ _ _ _ hg₁ hg₁,
    transport_transport_eq ε' k rfl _ _ _ _ h₁ h₂, transport_unitTransfer,
    transport_transport_eq g₂ k hk₂ _ _ _ _ hg₂ hg₂] at H'
  exact H'

/-- A rigidified trivialization of a pullback of a rigidified module is inverse to the
transported section map. -/
lemma transport_sectionMap_comp_of_trivial (L : RigidifiedModule ε)
    {f : X' ⟶ X} {g : S' ⟶ S} (comm : ε' ≫ f = g ≫ ε)
    (Φ : (Scheme.Modules.pullback f).obj L.carrier ⟶ SheafOfModules.unit X'.ringCatSheaf)
    (hΦ : ((RigidifiedModule.pullback f g comm).obj L).rigidification.hom ≫
        (Scheme.Modules.pullback ε').map Φ = (pullbackUnitIso ε').inv)
    {w : S' ⟶ X} (h : ε' ≫ f = w) (hg : g ≫ ε = w) :
    transport g hg hg (sectionMap L) ≫ transport ε' h h (Φ ≫ (pullbackUnitIso f).inv) =
      𝟙 _ := by
  have e := pullback_rigidification_compIso L f g comm h hg
  have hu := compIso_unit ε' f w h
  rw [← cancel_epi (pullbackUnitIso w).inv, ← reassoc_of% e, Category.comp_id]
  unfold transport
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% hΦ]
  rw [← cancel_mono (pullbackUnitIso w).hom, Category.assoc, Category.assoc, hu]
  simp [← Functor.map_comp_assoc]

end Rigidified

end Langlands.Scheme.Modules
