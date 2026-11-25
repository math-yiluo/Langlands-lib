/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.EtaleSetTerminalTransport

/-! # Transport of matching families to fpqc descent data

## References

* Stacks Project, Tag 0GLZ, first paragraph
* Tag 09XN
* Stacks Project, Tag 0GLZ (first proof paragraph); Tags 03CB and 03CC
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private noncomputable abbrev L {S T : Scheme.{u}} (f : T ⟶ S) :=
  Scheme.etaleSetPullback f

private noncomputable abbrev b {S T : Scheme.{u}} (f : T ⟶ S) :=
  MorphismProperty.Over.pullback @Etale ⊤ f

private abbrev Γ {S : Scheme.{u}} (H : Sheaf S.smallEtaleTopology (Type (u + 1))) :=
  H.obj.obj (op (Scheme.Etale.mk (𝟙 S)))

private noncomputable abbrev η {S T : Scheme.{u}} (f : T ⟶ S) :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (b f) (Type (u + 1))
    (S.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale)).unit

-- The base change of an identity is terminal, with its explicit inverse pullback lift.
private noncomputable def terminalIso {S T : Scheme.{u}} (f : T ⟶ S) :
    (b f).obj (Scheme.Etale.mk (𝟙 S)) ≅ Scheme.Etale.mk (𝟙 T) :=
  MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 S) f)) (Category.comp_id _)

private noncomputable def terminalLift {S T : Scheme.{u}} (f : T ⟶ S) :
    Scheme.Etale.mk (𝟙 T) ⟶ (b f).obj (Scheme.Etale.mk (𝟙 S)) :=
  MorphismProperty.Over.homMk
    (pullback.lift f (𝟙 T) ((Category.comp_id _).trans (Category.id_comp _).symm))
    (by simp)

private lemma terminalLift_eq {S T : Scheme.{u}} (f : T ⟶ S) :
    terminalLift f = (terminalIso f).inv := by
  apply (cancel_mono (terminalIso f).hom).1
  rw [Iso.inv_hom_id]
  apply MorphismProperty.Over.Hom.ext
  change pullback.lift f (𝟙 T) _ ≫ pullback.snd (𝟙 S) f = 𝟙 T
  exact pullback.lift_snd _ _ _

-- Inverse-image restriction evaluated on terminal sections.
private noncomputable def res {S T : Scheme.{u}} (f : T ⟶ S)
    (H : Sheaf S.smallEtaleTopology (Type (u + 1))) : Γ H ⟶ Γ ((L f).obj H) :=
  ((η f).app H).hom.app (op (Scheme.Etale.mk (𝟙 S))) ≫
    ((L f).obj H).obj.map (terminalLift f).op

private noncomputable abbrev c {R S T : Scheme.{u}} (e : S ⟶ R) (f : T ⟶ S) :=
  Classical.choose etaleSetInverseImageCompositionUnits.2.2 R S T e f

-- Terminal transport after cancelling the second-projection isomorphism.
private noncomputable def tr {R S T : Scheme.{u}}
    (e : S ⟶ R) (f : T ⟶ S) (k : T ⟶ R) (hk : f ≫ e = k)
    (H : Sheaf R.smallEtaleTopology (Type (u + 1))) :
    Γ ((L k).obj H) ≅ Γ ((L f).obj ((L e).obj H)) :=
  (eqToIso (congrArg (fun k ↦ Γ ((L k).obj H)) hk)).symm ≪≫
    (asIso (((c e f).hom.app H).hom.app (op (Scheme.Etale.mk (𝟙 T))))).symm

private lemma terminalTransport_normalize {R S T : Scheme.{u}}
    (e : S ⟶ R) (f : T ⟶ S) (k : T ⟶ R) (hk : f ≫ e = k)
    (H : Sheaf R.smallEtaleTopology (Type (u + 1))) :
    (etaleSetTerminalTransport e f k hk H).hom ≫
        ((L f).obj ((L e).obj H)).obj.map (terminalLift f).op = (tr e f k hk H).hom := by
  subst k
  simp only [etaleSetTerminalTransport, tr, Iso.trans_hom, terminalLift_eq,
    Functor.mapIso_hom, Iso.op_hom, terminalIso, Category.assoc]
  rw [← Functor.map_comp, ← op_comp]
  simp

private lemma terminalTransport_restriction {R S T : Scheme.{u}}
    (e : S ⟶ R) (f : T ⟶ S) (k : T ⟶ R) (hk : f ≫ e = k)
    (H : Sheaf R.smallEtaleTopology (Type (u + 1))) :
    ((η f).app ((L e).obj H)).hom.app (op (Scheme.Etale.mk (𝟙 S))) ≫
        (etaleSetTerminalTransport e f k hk H).inv =
      res f ((L e).obj H) ≫ (tr e f k hk H).inv := by
  simp only [etaleSetTerminalTransport, tr, res, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Iso.op_inv, terminalLift_eq, terminalIso, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
-- A coefficient morphism commutes with terminal restriction by the two naturality squares.
private lemma res_naturality {S T : Scheme.{u}} (f : T ⟶ S)
    {H H' : Sheaf S.smallEtaleTopology (Type (u + 1))} (ψ : H ⟶ H') :
    ψ.hom.app (op (Scheme.Etale.mk (𝟙 S))) ≫ res f H' =
      res f H ≫ ((L f).map ψ).hom.app (op (Scheme.Etale.mk (𝟙 T))) := by
  have hu := NatTrans.congr_app (congrArg (fun q ↦ q.hom) ((η f).naturality ψ))
    (op (Scheme.Etale.mk (𝟙 S)))
  change ψ.hom.app (op (Scheme.Etale.mk (𝟙 S))) ≫
      ((η f).app H').hom.app (op (Scheme.Etale.mk (𝟙 S))) =
    ((η f).app H).hom.app (op (Scheme.Etale.mk (𝟙 S))) ≫
      ((L f).map ψ).hom.app (op ((b f).obj (Scheme.Etale.mk (𝟙 S)))) at hu
  dsimp only [res]
  simp only [Category.assoc]
  rw [reassoc_of% hu, ← (((L f).map ψ).hom.naturality (terminalLift f).op)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
-- The triangle square follows from coefficient naturality and composition associativity.
private lemma transport_triangle {R S V T : Scheme.{u}}
    (e : S ⟶ R) (f : V ⟶ S) (h : T ⟶ V)
    (k : V ⟶ R) (l : T ⟶ S) (p : T ⟶ R)
    (hk : f ≫ e = k) (hl : h ≫ f = l) (hp : h ≫ k = p) (hp₀ : l ≫ e = p)
    (H : Sheaf R.smallEtaleTopology (Type (u + 1))) :
    res h ((L k).obj H) ≫ (tr k h p hp H).inv ≫ (tr e l p hp₀ H).hom =
      (tr e f k hk H).hom ≫ res h ((L f).obj ((L e).obj H)) ≫
        ((c f h).hom.app ((L e).obj H)).hom.app (op (Scheme.Etale.mk (𝟙 T))) ≫
        eqToHom (congrArg (fun l ↦ Γ ((L l).obj ((L e).obj H))) hl) := by
  subst k
  subst l
  subst p
  have hn := res_naturality h ((c e f).hom.app H)
  have hc := NatTrans.congr_app (congrArg (fun q ↦ q.hom)
    ((Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).2.2
      R S V T e f h H)) (op (Scheme.Etale.mk (𝟙 T)))
  simp only [tr, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    eqToIso_refl, Iso.refl_hom, Iso.refl_inv, asIso_hom, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    eqToHom_refl, Category.comp_id] at hc
  apply (cancel_epi (((c e f).hom.app H).hom.app
    (op (Scheme.Etale.mk (𝟙 V))))).1
  rw [reassoc_of% hn, reassoc_of% hc]
  erw [Category.id_comp, IsIso.hom_inv_id, Category.comp_id]
  simp only [asIso_inv, IsIso.hom_inv_id_assoc]

private lemma tr_eq {R S T : Scheme.{u}} (e : S ⟶ R)
    (l l' : T ⟶ S) (p : T ⟶ R) (hp : l ≫ e = p) (hp' : l' ≫ e = p)
    (hl : l = l') (H : Sheaf R.smallEtaleTopology (Type (u + 1)))
    (x : Γ ((L p).obj H)) :
    (tr e l p hp H).hom x =
      Eq.mp (congrArg (fun l ↦ Γ ((L l).obj ((L e).obj H))) hl.symm)
        ((tr e l' p hp' H).hom x) := by
  subst l'
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The overlap equation has several nested inverse-image functors and dependent equality casts.
/-- A compatible family of sections of `P`, identified via `e` with sections of the étale
pullbacks of `F`, transports to a family of sections of the iterated pullbacks of `F` that
agree on the overlaps, i.e. to descent data. -/
theorem proEtaleComparisonMatchingTransport
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (P : X.ProEtᵒᵖ ⥤ Type (u + 1))
    (e : ∀ Y : X.ProEt, P.obj (op Y) ≃
      ((Scheme.etaleSetPullback Y.hom).obj F).obj.obj
        (op (Scheme.Etale.mk (𝟙 Y.left))))
    (hres : ∀ (Y Z : X.ProEt) (g : Z ⟶ Y) (s : P.obj (op Y)),
      e Z (P.map g.op s) =
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ g.left) (Type (u + 1))
          (Y.left.smallGrothendieckTopology @Etale)
          (Z.left.smallGrothendieckTopology @Etale)).unit.app
            ((Scheme.etaleSetPullback Y.hom).obj F)).hom.app
              (op (Scheme.Etale.mk (𝟙 Y.left))) ≫
          (etaleSetTerminalTransport Y.hom g.left Z.hom g.w F).inv) (e Y s))
    {I : Type v} (Y : X.ProEt) (Z : I → X.ProEt) (g : ∀ i, Z i ⟶ Y)
    (s : ∀ i, P.obj (op (Z i))) (hs : Presieve.Arrows.Compatible P g s) :
    ∃ t : ∀ i, ((Scheme.etaleSetPullback (g i).left).obj
        ((Scheme.etaleSetPullback Y.hom).obj F)).obj.obj
          (op (Scheme.Etale.mk (𝟙 (Z i).left))),
      (∀ i, t i =
        ((Scheme.etaleSetPullback (g i).left).obj
          ((Scheme.etaleSetPullback Y.hom).obj F)).obj.map
          (MorphismProperty.Over.homMk
            (pullback.lift (g i).left (𝟙 (Z i).left)
              ((Category.comp_id _).trans (Category.id_comp _).symm)) (by simp) :
            Scheme.Etale.mk (𝟙 (Z i).left) ⟶
              (MorphismProperty.Over.pullback @Etale ⊤ (g i).left).obj
                (Scheme.Etale.mk (𝟙 Y.left))).op
          ((etaleSetTerminalTransport Y.hom (g i).left (Z i).hom
            (MorphismProperty.Over.w (g i)) F).hom (e (Z i) (s i)))) ∧
      (∀ i j,
      ((Classical.choose etaleSetInverseImageCompositionUnits.2.2
          Y.left ((Z i).left) (pullback ((g i).left) ((g j).left)) ((g i).left) (pullback.fst ((g
            i).left) ((g j).left))).hom.app ((Scheme.etaleSetPullback Y.hom).obj F)).hom.app
        (op (Scheme.Etale.mk (𝟙 (pullback ((g i).left) ((g j).left)))))
        (((Scheme.etaleSetPullback (pullback.fst ((g i).left) ((g j).left))).obj
            ((Scheme.etaleSetPullback ((g i).left)).obj ((Scheme.etaleSetPullback Y.hom).obj
              F))).obj.map
          (MorphismProperty.Over.homMk
            (pullback.lift (pullback.fst ((g i).left) ((g j).left)) (𝟙 (pullback ((g i).left) ((g
              j).left)))
              ((Category.comp_id _).trans (Category.id_comp _).symm))
            (by simp) :
            Scheme.Etale.mk (𝟙 (pullback ((g i).left) ((g j).left))) ⟶
              (MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst ((g i).left) ((g j).left))).obj
                (Scheme.Etale.mk (𝟙 ((Z i).left)))).op
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst ((g i).left) ((g j).left))) _
            (((Z i).left).smallGrothendieckTopology @Etale)
            ((pullback ((g i).left) ((g j).left)).smallGrothendieckTopology @Etale)).unit.app
              ((Scheme.etaleSetPullback ((g i).left)).obj ((Scheme.etaleSetPullback Y.hom).obj
                F))).hom.app
            (op (Scheme.Etale.mk (𝟙 ((Z i).left)))) (t i))) =
        Eq.mp (congrArg (fun k : pullback ((g i).left) ((g j).left) ⟶ Y.left ↦
          ((Scheme.etaleSetPullback k).obj ((Scheme.etaleSetPullback Y.hom).obj F)).obj.obj
            (op (Scheme.Etale.mk (𝟙 (pullback ((g i).left) ((g j).left))))))
          (pullback.condition (f := (g i).left) (g := (g j).left)).symm)
        (((Classical.choose etaleSetInverseImageCompositionUnits.2.2
            Y.left ((Z j).left) (pullback ((g i).left) ((g j).left)) ((g j).left) (pullback.snd
              ((g i).left) ((g j).left))).hom.app ((Scheme.etaleSetPullback Y.hom).obj F)).hom.app
          (op (Scheme.Etale.mk (𝟙 (pullback ((g i).left) ((g j).left)))))
          (((Scheme.etaleSetPullback (pullback.snd ((g i).left) ((g j).left))).obj
              ((Scheme.etaleSetPullback ((g j).left)).obj ((Scheme.etaleSetPullback Y.hom).obj
                F))).obj.map
            (MorphismProperty.Over.homMk
              (pullback.lift (pullback.snd ((g i).left) ((g j).left)) (𝟙 (pullback ((g i).left)
                ((g j).left)))
                ((Category.comp_id _).trans (Category.id_comp _).symm))
              (by simp) :
              Scheme.Etale.mk (𝟙 (pullback ((g i).left) ((g j).left))) ⟶
                (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd ((g i).left) ((g
                  j).left))).obj
                  (Scheme.Etale.mk (𝟙 ((Z j).left)))).op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd ((g i).left) ((g j).left))) _
              (((Z j).left).smallGrothendieckTopology @Etale)
              ((pullback ((g i).left) ((g j).left)).smallGrothendieckTopology @Etale)).unit.app
                ((Scheme.etaleSetPullback ((g j).left)).obj ((Scheme.etaleSetPullback Y.hom).obj
                  F))).hom.app
              (op (Scheme.Etale.mk (𝟙 ((Z j).left)))) (t j))))) := by
  classical
  let t (i : I) := (tr Y.hom (g i).left (Z i).hom (g i).w F).hom (e (Z i) (s i))
  refine ⟨t, ?_, ?_⟩
  · intro i
    exact (ConcreteCategory.congr_hom
      (terminalTransport_normalize Y.hom (g i).left (Z i).hom (g i).w F)
      (e (Z i) (s i))).symm
  · intro i j
    have hgi : WeaklyEtale (g i).left := by
      have : WeaklyEtale ((g i).left ≫ Y.hom) := by
        erw [(g i).w]
        infer_instance
      exact WeaklyEtale.of_comp (g i).left Y.hom
    have hgj : WeaklyEtale (g j).left := by
      have : WeaklyEtale ((g j).left ≫ Y.hom) := by
        erw [(g j).w]
        infer_instance
      exact WeaklyEtale.of_comp (g j).left Y.hom
    -- The scheme overlap is again weakly etale over X.
    let W : X.ProEt := Scheme.ProEt.mk
      (pullback.fst (g i).left (g j).left ≫ (Z i).hom)
    let a : W ⟶ Z i := MorphismProperty.Over.homMk
      (pullback.fst (g i).left (g j).left) rfl
    let d : W ⟶ Z j := MorphismProperty.Over.homMk
      (pullback.snd (g i).left (g j).left) (by
        change _ = pullback.fst (g i).left (g j).left ≫ (Z i).hom
        have h₁ : (g i).left ≫ Y.hom = (Z i).hom := (g i).w
        have h₂ : (g j).left ≫ Y.hom = (Z j).hom := (g j).w
        rw [← h₁, ← h₂, ← Category.assoc, ← Category.assoc, pullback.condition])
    have had : a ≫ g i = d ≫ g j := by
      apply MorphismProperty.Over.Hom.ext
      exact pullback.condition
    have hp (m : I) (q : W ⟶ Z m) : (q.left ≫ (g m).left) ≫ Y.hom = W.hom := by
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun z ↦ q.left ≫ z) (g m).w).trans q.w)
    have hr (m : I) (q : W ⟶ Z m) := hres (Z m) W q (s m)
    simp only [terminalTransport_restriction, comp_apply] at hr
    -- Evaluate the two triangle squares on the matching family.
    have hi := ConcreteCategory.congr_hom
      (transport_triangle Y.hom (g i).left a.left (Z i).hom
        (a.left ≫ (g i).left) W.hom (g i).w rfl a.w (hp i a) F)
      (e (Z i) (s i))
    have hj := ConcreteCategory.congr_hom
      (transport_triangle Y.hom (g j).left d.left (Z j).hom
        (d.left ≫ (g j).left) W.hom (g j).w rfl d.w (hp j d) F)
      (e (Z j) (s j))
    simp only [comp_apply, eqToHom_refl, id_apply] at hi hj
    erw [← hr i a] at hi
    erw [← hr j d] at hj
    change ((c (g i).left a.left).hom.app ((L Y.hom).obj F)).hom.app
        (op (Scheme.Etale.mk (𝟙 W.left))) (res a.left
          ((L (g i).left).obj ((L Y.hom).obj F)) (t i)) =
      Eq.mp (congrArg (fun k : W.left ⟶ Y.left ↦ Γ ((L k).obj ((L Y.hom).obj F)))
        (pullback.condition (f := (g i).left) (g := (g j).left)).symm)
        (((c (g j).left d.left).hom.app ((L Y.hom).obj F)).hom.app
          (op (Scheme.Etale.mk (𝟙 W.left)))
          (res d.left ((L (g j).left).obj ((L Y.hom).obj F)) (t j)))
    erw [← hi]
    have hmatch := congrArg (e W) (hs i j W a d had)
    erw [hmatch]
    exact (tr_eq Y.hom (a.left ≫ (g i).left) (d.left ≫ (g j).left) W.hom
      (hp i a) (hp j d) pullback.condition F (e W (P.map d.op (s j)))).trans
        (congrArg (Eq.mp _) hj)

end AlgebraicGeometry
