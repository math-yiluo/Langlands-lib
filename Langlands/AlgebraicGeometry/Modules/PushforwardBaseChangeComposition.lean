import Langlands.AlgebraicGeometry.Modules.OpenDirectImageBaseChange

/-! # Composition of the specified ordinary base-change comparison -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

section AdjointComposition
variable {S S' S'' : Scheme.{u}} (b : S' ⟶ S) (c : S'' ⟶ S')

lemma conjugateEquiv_pullbackComp_hom :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction (c ≫ b))
      ((Scheme.Modules.pullbackPushforwardAdjunction b).comp
        (Scheme.Modules.pullbackPushforwardAdjunction c))
      (Scheme.Modules.pullbackComp c b).hom = (Scheme.Modules.pushforwardComp c b).inv := by
  refine (Iso.hom_comp_eq_id _).mp ?_
  rw [← Scheme.Modules.conjugateEquiv_pullbackComp_inv c b]
  exact conjugateEquiv_comm _ _ (Iso.hom_inv_id _)

lemma homEquiv_comp_pullbackComp_hom (A : S.Modules) (B : S''.Modules)
    (k : (Scheme.Modules.pullback (c ≫ b)).obj A ⟶ B) :
    (((Scheme.Modules.pullbackPushforwardAdjunction b).comp
      (Scheme.Modules.pullbackPushforwardAdjunction c)).homEquiv A B)
      ((Scheme.Modules.pullbackComp c b).hom.app A ≫ k) =
    (Scheme.Modules.pullbackPushforwardAdjunction (c ≫ b)).homEquiv A B k ≫
      (Scheme.Modules.pushforwardComp c b).inv.app B := by
  have hu := unit_conjugateEquiv
    (Scheme.Modules.pullbackPushforwardAdjunction (c ≫ b))
    ((Scheme.Modules.pullbackPushforwardAdjunction b).comp
      (Scheme.Modules.pullbackPushforwardAdjunction c))
    (Scheme.Modules.pullbackComp c b).hom A
  rw [conjugateEquiv_pullbackComp_hom] at hu
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← hu,
    Category.assoc]
  rw [← NatTrans.naturality]
  rfl

/-- The adjunction unit for a composite, expressed using the iterated pullback. -/
lemma unit_pullbackComp_hom (A : S.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (c ≫ b)).unit.app A =
    (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app A ≫
      (Scheme.Modules.pushforward b).map
        ((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
          ((Scheme.Modules.pullback b).obj A)) ≫
      (Scheme.Modules.pushforward b).map ((Scheme.Modules.pushforward c).map
        ((Scheme.Modules.pullbackComp c b).hom.app A)) ≫
      (Scheme.Modules.pushforwardComp c b).hom.app
        ((Scheme.Modules.pullback (c ≫ b)).obj A) := by
  have h := unit_conjugateEquiv
    (Scheme.Modules.pullbackPushforwardAdjunction (c ≫ b))
    ((Scheme.Modules.pullbackPushforwardAdjunction b).comp
      (Scheme.Modules.pullbackPushforwardAdjunction c))
    (Scheme.Modules.pullbackComp c b).hom A
  rw [conjugateEquiv_pullbackComp_hom, Adjunction.comp_unit_app] at h
  have h' := h =≫ (Scheme.Modules.pushforwardComp c b).hom.app
    ((Scheme.Modules.pullback (c ≫ b)).obj A)
  dsimp only [Functor.comp_obj, Functor.id_obj] at h' ⊢
  simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Functor.comp_map] using h'

end AdjointComposition

section BaseComposition
variable {S S' S'' X X' X'' : Scheme.{u}}
  (b : S' ⟶ S) (c : S'' ⟶ S') (f : X ⟶ S) (f' : X' ⟶ S') (f'' : X'' ⟶ S'')
  (p : X' ⟶ X) (q : X'' ⟶ X')
  (w : p ≫ f = f' ≫ b) (v : q ≫ f' = f'' ≫ c)

include w v in
lemma compositeBaseChangeSquare : (q ≫ p) ≫ f = f'' ≫ (c ≫ b) := by
  rw [Category.assoc, w, ← Category.assoc q f', v, Category.assoc]

/-- Coherence of the pushforward comparison across two squares. -/
lemma pushforwardSquareIso_composition (N : X''.Modules) :
    (Scheme.Modules.pushforward f).map ((Scheme.Modules.pushforwardComp q p).hom.app N) ≫
      (pushforwardSquareIso (c ≫ b) f f'' (q ≫ p)
        (compositeBaseChangeSquare b c f f' f'' p q w v)).hom.app N ≫
      (Scheme.Modules.pushforwardComp c b).inv.app ((Scheme.Modules.pushforward f'').obj N) =
    (pushforwardSquareIso b f f' p w).hom.app ((Scheme.Modules.pushforward q).obj N) ≫
      (Scheme.Modules.pushforward b).map ((pushforwardSquareIso c f' f'' q v).hom.app N) := by
  apply Scheme.Modules.hom_ext
  intro U
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    pushforwardSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app, Category.assoc,
    Category.id_comp, Category.comp_id]
  change N.presheaf.map _ = N.presheaf.map _ ≫ N.presheaf.map _
  rw [← Functor.map_comp]
  congr 1

/-- The comparison obtained by applying base change twice. -/
def iteratedPushforwardBaseChange (M : X.Modules) :
    (Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback b).obj
      ((Scheme.Modules.pushforward f).obj M)) ⟶
      (Scheme.Modules.pushforward f'').obj ((Scheme.Modules.pullback (q ≫ p)).obj M) :=
  (Scheme.Modules.pullback c).map (pushforwardBaseChange b f f' p w M) ≫
    pushforwardBaseChange c f' f'' q v ((Scheme.Modules.pullback p).obj M) ≫
    (Scheme.Modules.pushforward f'').map ((Scheme.Modules.pullbackComp q p).hom.app M)

/-- The specified comparison is compatible with composing base-change squares. -/
theorem pushforwardBaseChange_composition (M : X.Modules) :
    (Scheme.Modules.pullbackComp c b).hom.app ((Scheme.Modules.pushforward f).obj M) ≫
      pushforwardBaseChange (c ≫ b) f f'' (q ≫ p)
        (compositeBaseChangeSquare b c f f' f'' p q w v) M =
    iteratedPushforwardBaseChange b c f f' f'' p q w v M := by
  apply (((Scheme.Modules.pullbackPushforwardAdjunction b).comp
    (Scheme.Modules.pullbackPushforwardAdjunction c)).homEquiv _ _).injective
  rw [homEquiv_comp_pullbackComp_hom, pushforwardBaseChange, Equiv.apply_symm_apply]
  unfold iteratedPushforwardBaseChange
  rw [Adjunction.comp_homEquiv]
  change _ = (Scheme.Modules.pullbackPushforwardAdjunction b).homEquiv _ _
    ((Scheme.Modules.pullbackPushforwardAdjunction c).homEquiv _ _
      ((Scheme.Modules.pullback c).map (pushforwardBaseChange b f f' p w M) ≫
        pushforwardBaseChange c f' f'' q v ((Scheme.Modules.pullback p).obj M) ≫
        (Scheme.Modules.pushforward f'').map ((Scheme.Modules.pullbackComp q p).hom.app M)))
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    pushforwardBaseChange, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_naturality_right, pushforwardBaseChange, Equiv.apply_symm_apply]
  rw [unit_pullbackComp_hom p q M]
  simp only [Functor.map_comp, Category.assoc]
  have hq := (pushforwardSquareIso b f f' p w).hom.naturality
    ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app ((Scheme.Modules.pullback p).obj M))
  have hc := congrArg (Scheme.Modules.pushforward b).map
    ((pushforwardSquareIso c f' f'' q v).hom.naturality
      ((Scheme.Modules.pullbackComp q p).hom.app M))
  have ha := (pushforwardSquareIso b f f' p w).hom.naturality
    ((Scheme.Modules.pushforward q).map ((Scheme.Modules.pullbackComp q p).hom.app M))
  dsimp only [Functor.comp_obj, Functor.id_obj] at hq hc ha
  simp only [Functor.comp_map, Functor.map_comp] at hq hc ha
  rw [← reassoc_of% hq, ← hc, ← reassoc_of% ha,
    ← pushforwardSquareIso_composition b c f f' f'' p q w v]

end BaseComposition
end Langlands.AlgebraicGeometry.Modules.DerivedSections
