/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveSetDescentInjective
public import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits

/-! # Constancy of compatible finite-descent stalk coordinates

Source: Stacks Project, Étale Cohomology, Lemma 09Z2 and Remark 09Z3.
(blueprint: lem-weil-pbc-sets-finite-descent-coordinates-constant).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private noncomputable def restrictGerm {S T : Scheme.{u}} (e : T ⟶ S)
    (H : Sheaf T.smallEtaleTopology (Type (u + 1)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S)
    (t : {t : Spec (.of Ω) ⟶ T // t ≫ e = x}) :=
  colimit.pre ((Functor.Elements.π (Scheme.pointSmallEtale t.1).fiber).op ⋙ H.obj)
    (Etale.baseChangeNbhd e x t).op

private theorem restrictGerm_apply {S T : Scheme.{u}} (e : T ⟶ S)
    (H : Sheaf T.smallEtaleTopology (Type (u + 1)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S)
    (t : {t : Spec (.of Ω) ⟶ T // t ≫ e = x})
    (U : S.Etale) (z : (Scheme.pointSmallEtale x).fiber.obj U)
    (s : H.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ e).obj U))) :
    restrictGerm e H x t
      ((Scheme.pointSmallEtale x).toPresheafFiber U z
        ((e.Etale.sheafPushforwardContinuous (Type (u + 1))
          S.smallEtaleTopology T.smallEtaleTopology).obj H).obj s) =
    (Scheme.pointSmallEtale t.1).toPresheafFiber ((MorphismProperty.Over.pullback @Etale ⊤ e).obj U)
      ((Etale.baseChangeNbhd e x t).obj (Functor.elementsMk _ U z)).2 H.obj s :=
  ConcreteCategory.congr_hom (colimit.ι_pre
    ((Functor.Elements.π (Scheme.pointSmallEtale t.1).fiber).op ⋙ H.obj)
    (Etale.baseChangeNbhd e x t).op (op (Functor.elementsMk _ U z))) s

private noncomputable def unitGerm {S T : Scheme.{u}} (e : T ⟶ S)
    (H : Sheaf S.smallEtaleTopology (Type (u + 1)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S)
    (t : {t : Spec (.of Ω) ⟶ T // t ≫ e = x}) :=
  (Scheme.pointSmallEtale x).sheafFiber.map
    (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (MorphismProperty.Over.pullback
    @Etale ⊤ e) (Type (u + 1)) (S.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology
    @Etale)).unit).app H) ≫
    restrictGerm e ((Scheme.etaleSetPullback e).obj H) x t

private theorem unitGerm_apply {S T : Scheme.{u}} (e : T ⟶ S)
    (H : Sheaf S.smallEtaleTopology (Type (u + 1)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S)
    (t : {t : Spec (.of Ω) ⟶ T // t ≫ e = x})
    (U : S.Etale) (z : (Scheme.pointSmallEtale x).fiber.obj U)
    (s : H.obj.obj (op U)) :
    unitGerm e H x t ((Scheme.pointSmallEtale x).toPresheafFiber U z H.obj s) =
      (Scheme.pointSmallEtale t.1).toPresheafFiber ((MorphismProperty.Over.pullback @Etale ⊤ e).obj
        U)
        ((Etale.baseChangeNbhd e x t).obj (Functor.elementsMk _ U z)).2
        ((Scheme.etaleSetPullback e).obj H).obj
        (etaleSetDescentUnit e H U s) := by
  change restrictGerm e ((Scheme.etaleSetPullback e).obj H) x t
    ((Scheme.pointSmallEtale x).presheafFiber.map
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (MorphismProperty.Over.pullback
      @Etale ⊤ e) (Type (u + 1)) (S.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology
      @Etale)).unit).app H).hom
      ((Scheme.pointSmallEtale x).toPresheafFiber U z H.obj s)) = _
  erw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply]
  exact restrictGerm_apply e ((Scheme.etaleSetPullback e).obj H) x t U z (etaleSetDescentUnit e H U
    s)

private noncomputable def sectionComparison {X Y W : Scheme.{u}}
    (f : Y ⟶ X) (g : W ⟶ Y)
    (G : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale)
    (s : ((Scheme.etaleSetPullback f).obj G).obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤
      f).obj U))) :
    ((Scheme.etaleSetPullback (g ≫ f)).obj G).obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤
      (g ≫ f)).obj U)) :=
  etaleSetDescentComparison f g G U s

private noncomputable def sectionGerm {X Y : Scheme.{u}} (f : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology (Type (u + 1)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (t : {t : Spec (.of Ω) ⟶ Y // t ≫ f = x})
    (U : X.Etale) (z : (Scheme.pointSmallEtale x).fiber.obj U)
    (s : ((Scheme.etaleSetPullback f).obj G).obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤
      f).obj U))) :
    (Scheme.pointSmallEtale t.1).sheafFiber.obj ((Scheme.etaleSetPullback f).obj G) :=
  restrictGerm f ((Scheme.etaleSetPullback f).obj G) x t
    ((Scheme.pointSmallEtale x).toPresheafFiber U z
      ((f.Etale.sheafPushforwardContinuous (Type (u + 1))
        X.smallEtaleTopology Y.smallEtaleTopology).obj ((Scheme.etaleSetPullback f).obj G)).obj s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A single composition comparison preserves coordinates of germs at a lift.
Source: Stacks Project, Étale Cohomology, Lemma 09Z2, last paragraph and Remark 09Z3;
Tag 03Q1 (3), and Sites, Tags 03CB and 03CC.

Proof: Substitute the composite for k. Let Q be restriction of the second stalk
unit followed by the stalk map of the composition isomorphism. Naturality of germs
and the pullback pasting projection equations show that Q sends a section germ
to its comparison-section germ. Representing every base-stalk element by a section
germ, the composition-unit equation gives Q R_f = R_k, where R denotes restriction
of the stalk unit. Injectivity of c and its diagonal equation give R_f c = identity.
Consequently d Q = c by the diagonal equation for d. Applying this to the given
germ proves the result. -/
private theorem etaleSetDescentComparison_coordinates
    {X Y W : Scheme.{u}} (f : Y ⟶ X) (g : W ⟶ Y) (k : W ⟶ X)
    (hk : g ≫ f = k) (G : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (t : {t : Spec (.of Ω) ⟶ Y // t ≫ f = x})
    (w : {w : Spec (.of Ω) ⟶ W // w ≫ k = x}) (hw : w.1 ≫ g = t.1)
    (c : (Scheme.pointSmallEtale t.1).sheafFiber.obj ((Scheme.etaleSetPullback f).obj G) →
      (Scheme.pointSmallEtale x).sheafFiber.obj G)
    (hc : Function.Bijective c)
    (hdiag : ∀ a, c ((colimit.pre
      ((Functor.Elements.π (Scheme.pointSmallEtale t.1).fiber).op ⋙ ((Scheme.etaleSetPullback
        f).obj G).obj)
      (Etale.baseChangeNbhd f x t).op)
      ((Scheme.pointSmallEtale x).sheafFiber.map
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1)) (X.smallGrothendieckTopology
        @Etale) (Y.smallGrothendieckTopology @Etale)).unit).app G) a)) = a)
    (d : (Scheme.pointSmallEtale w.1).sheafFiber.obj ((Scheme.etaleSetPullback k).obj G) →
      (Scheme.pointSmallEtale x).sheafFiber.obj G)
    (hd : Function.Bijective d)
    (hddiag : ∀ a, d ((colimit.pre
      ((Functor.Elements.π (Scheme.pointSmallEtale w.1).fiber).op ⋙ ((Scheme.etaleSetPullback
        k).obj G).obj)
      (Etale.baseChangeNbhd k x w).op)
      ((Scheme.pointSmallEtale x).sheafFiber.map
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤ k) (Type (u + 1)) (X.smallGrothendieckTopology
        @Etale) (W.smallGrothendieckTopology @Etale)).unit).app G) a)) = a)
    (U : X.Etale) (z : (Scheme.pointSmallEtale x).fiber.obj U)
    (s : ((Scheme.etaleSetPullback f).obj G).obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤
      f).obj U))) :
    c (sectionGerm f G x t U z s) =
      d (sectionGerm k G x w U z
        (cast (congrArg (fun k : W ⟶ X ↦ ((Scheme.etaleSetPullback k).obj G).obj.obj
          (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj U))) hk) (sectionComparison f g G U
            s))) := by
  subst k
  let H := (Scheme.etaleSetPullback f).obj G
  let K := (Scheme.etaleSetPullback (g ≫ f)).obj G
  let w' : {w' : Spec (.of Ω) ⟶ W // w' ≫ g = t.1} := ⟨w.1, hw⟩
  let φ := ((Classical.choose etaleSetInverseImageCompositionUnits.2.2) X Y W f g).hom.app G
  let Q := unitGerm g H t.1 w' ≫ (Scheme.pointSmallEtale w.1).sheafFiber.map φ
  have hQ : ∀ (V : X.Etale) (y : (Scheme.pointSmallEtale x).fiber.obj V)
      (a : H.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V))),
      Q (restrictGerm f H x t
        ((Scheme.pointSmallEtale x).toPresheafFiber V y
          ((f.Etale.sheafPushforwardContinuous (Type (u + 1))
            X.smallEtaleTopology Y.smallEtaleTopology).obj H).obj a)) =
      restrictGerm (g ≫ f) K x w
        ((Scheme.pointSmallEtale x).toPresheafFiber V y
          (((g ≫ f).Etale.sheafPushforwardContinuous (Type (u + 1))
            X.smallEtaleTopology W.smallEtaleTopology).obj K).obj
          (etaleSetDescentComparison f g G V a)) := by
    intro V y a
    rw [restrictGerm_apply]
    change (Scheme.pointSmallEtale w.1).presheafFiber.map φ.hom
      (unitGerm g H t.1 w'
        ((Scheme.pointSmallEtale t.1).toPresheafFiber ((MorphismProperty.Over.pullback @Etale ⊤
          f).obj V)
          ((Etale.baseChangeNbhd f x t).obj (Functor.elementsMk _ V y)).2 H.obj a)) = _
    rw [unitGerm_apply]
    erw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply]
    rw [restrictGerm_apply]
    let j := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).hom.app V
    let z₀ := ((Etale.baseChangeNbhd (g ≫ f) x w).obj (Functor.elementsMk _ V y)).2
    let z₁ := ((Etale.baseChangeNbhd g t.1 w').obj
      (Functor.elementsMk _ ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)
        ((Etale.baseChangeNbhd f x t).obj (Functor.elementsMk _ V y)).2)).2
    have hz : (Scheme.pointSmallEtale w.1).fiber.map j z₀ = z₁ := by
      apply Over.OverMorphism.ext
      change z₀.left ≫ j.left = z₁.left
      change Scheme.Hom.basePt (g ≫ f) (Functor.elementsMk _ V y) w ≫ j.left =
        Scheme.Hom.basePt g
          (Functor.elementsMk _ ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)
            ((Etale.baseChangeNbhd f x t).obj (Functor.elementsMk _ V y)).2) w'
      dsimp only [j]
      rw [MorphismProperty.Over.pullbackComp_hom_app_left]
      simp only [pullback.map_id, Category.id_comp]
      change pullback.lift y.left w.1 _ ≫
        (pullbackLeftPullbackSndIso V.hom f g).inv =
          pullback.lift (pullback.lift y.left t.1 _) w.1 _
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_fst,
            pullback.lift_fst]
        · simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd,
            pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_fst_assoc]
          exact hw
      · simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd,
          pullback.lift_snd]
    have he := (Scheme.pointSmallEtale w.1).toPresheafFiber_w_apply j z₀ K.obj
      (φ.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)))
        (etaleSetDescentUnit g H ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V) a))
    rw [hz] at he
    exact he.symm
  have hQU : ∀ a, Q (unitGerm f G x t a) = unitGerm (g ≫ f) G x w a := by
    intro a
    obtain ⟨V, y, a, rfl⟩ :=
      (Scheme.pointSmallEtale x).toPresheafFiber_jointly_surjective (P := G.obj) a
    change Q (restrictGerm f H x t
      ((Scheme.pointSmallEtale x).presheafFiber.map
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1)) (X.smallGrothendieckTopology
        @Etale) (Y.smallGrothendieckTopology @Etale)).unit).app G).hom
        ((Scheme.pointSmallEtale x).toPresheafFiber V y G.obj a))) = _
    erw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply]
    erw [hQ]
    rw [unitGerm_apply]
    rw [restrictGerm_apply]
    congr 1
    have hu := (Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).1
      X Y W f g G V a
    unfold etaleSetDescentComparison
    change K.obj.map
      ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).hom.app V).op
      (φ.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)))
        (etaleSetDescentUnit g H ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)
          (etaleSetDescentUnit f G V a))) = _
    erw [hu]
    change K.obj.map
      ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).hom.app V).op
      (K.obj.map
        ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).inv.app V).op
        (etaleSetDescentUnit (g ≫ f) G V a)) = _
    rw [← Functor.map_comp_apply, ← op_comp, Iso.hom_inv_id_app]
    simp
  let a := restrictGerm f H x t
    ((Scheme.pointSmallEtale x).toPresheafFiber U z
      ((f.Etale.sheafPushforwardContinuous (Type (u + 1))
        X.smallEtaleTopology Y.smallEtaleTopology).obj H).obj s)
  have ha : unitGerm f G x t (c a) = a := hc.1 (hdiag (c a))
  have hda : d (Q a) = c a := by
    calc
      d (Q a) = d (Q (unitGerm f G x t (c a))) := congrArg (fun a' ↦ d (Q a')) ha.symm
      _ = c a := by
        rw [hQU]
        exact hddiag (c a)
  change c a = d (restrictGerm (g ≫ f) K x w
    ((Scheme.pointSmallEtale x).toPresheafFiber U z
      (((g ≫ f).Etale.sheafPushforwardContinuous (Type (u + 1))
        X.smallEtaleTopology W.smallEtaleTopology).obj K).obj
        (sectionComparison f g G U s)))
  erw [← hQ]
  exact hda.symm


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem descent_coordinate_at_lift
    {X X' : Scheme.{u}} (f : X' ⟶ X)
    (G : Sheaf X.smallEtaleTopology (Type (u + 1)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (t : {t : Spec (.of Ω) ⟶ X' // t ≫ f = x}) :
    ∃ c : (Scheme.pointSmallEtale t.1).sheafFiber.obj
        ((Scheme.etaleSetPullback f).obj G) →
        (Scheme.pointSmallEtale x).sheafFiber.obj G,
      Function.Bijective c ∧ ∀ a : (Scheme.pointSmallEtale x).sheafFiber.obj G,
        c ((colimit.pre
          ((Functor.Elements.π (Scheme.pointSmallEtale t.1).fiber).op ⋙
            ((Scheme.etaleSetPullback f).obj G).obj)
          (Etale.baseChangeNbhd f x t).op)
          ((Scheme.pointSmallEtale x).sheafFiber.map
            ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
              (X.smallGrothendieckTopology @Etale)
              (X'.smallGrothendieckTopology @Etale)).unit.app G) a)) = a := by
  rcases t with ⟨t, ht⟩
  subst x
  obtain ⟨c, hc, hg, -⟩ := etaleSetInverseImageStalkGerm X X' f G Ω t
  refine ⟨c, hc, ?_⟩
  intro a
  obtain ⟨U, z, s, rfl⟩ :=
    (Scheme.pointSmallEtale (t ≫ f)).toPresheafFiber_jointly_surjective (P := G.obj) a
  change c ((colimit.pre
    ((Functor.Elements.π (Scheme.pointSmallEtale t).fiber).op ⋙
      ((Scheme.etaleSetPullback f).obj G).obj)
    (Etale.baseChangeNbhd f (t ≫ f) ⟨t, rfl⟩).op)
      ((Scheme.pointSmallEtale (t ≫ f)).presheafFiber.map
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
      (X.smallGrothendieckTopology @Etale)
      (X'.smallGrothendieckTopology @Etale)).unit.app G).hom
      ((Scheme.pointSmallEtale (t ≫ f)).toPresheafFiber U z G.obj s))) = _
  erw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply]
  have hpre := ConcreteCategory.congr_hom
    (colimit.ι_pre
      ((Functor.Elements.π (Scheme.pointSmallEtale t).fiber).op ⋙
        ((Scheme.etaleSetPullback f).obj G).obj)
      (Etale.baseChangeNbhd f (t ≫ f) ⟨t, rfl⟩).op (op (Functor.elementsMk _ U z)))
    (etaleSetDescentUnit f G U s)
  erw [hpre]
  exact hg U z s

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem eqToHom_apply_cast {A B : Type u} (h : A = B) (a : A) :
    eqToHom h a = cast h a := by
  subst B
  rfl

private theorem cast_section_eq {I : Type*} (A : I → Type*)
    {i j k : I} (h : j = i) (hi : i = k) (hj : j = k)
    {l : A i} {r : A j} (hs : l = cast (congrArg A h) r) :
    cast (congrArg A hi) l = cast (congrArg A hj) r := by
  subst j
  subst k
  exact hs

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Evaluate two compatible comparisons at a point of their common source.
The composition comparison on germs identifies both evaluations with the same
coordinate; compatibility therefore makes the two source coordinates equal. -/
private theorem coordinates_on_square
    {X X' W : Scheme.{u}} (f : X' ⟶ X)
    (g₁ g₂ : W ⟶ X') (k : W ⟶ X)
    (hk₁ : g₁ ≫ f = k) (hk₂ : g₂ ≫ f = k)
    (G : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (c : ∀ t : {t : Spec (.of Ω) ⟶ X' // t ≫ f = x},
      (Scheme.pointSmallEtale t.1).sheafFiber.obj ((Scheme.etaleSetPullback f).obj G) →
        (Scheme.pointSmallEtale x).sheafFiber.obj G)
    (hc : ∀ t, Function.Bijective (c t))
    (hdiag : ∀ t a, c t ((colimit.pre
          ((Functor.Elements.π (Scheme.pointSmallEtale t.1).fiber).op ⋙
            ((Scheme.etaleSetPullback f).obj G).obj)
          (Etale.baseChangeNbhd f x t).op) ((Scheme.pointSmallEtale x).sheafFiber.map
            ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
              (X.smallGrothendieckTopology @Etale)
              (X'.smallGrothendieckTopology @Etale)).unit.app G) a)) = a)
    (U : X.Etale)
    (s' : ((Scheme.etaleSetPullback f).obj G).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
        U)))
    (hs :
      cast (congrArg (fun k : W ⟶ X ↦ ((Scheme.etaleSetPullback k).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj U))) hk₁) (sectionComparison f g₁ G U
          s') =
      cast (congrArg (fun k : W ⟶ X ↦ ((Scheme.etaleSetPullback k).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj U))) hk₂) (sectionComparison f g₂ G U
          s'))
    (z : (Scheme.pointSmallEtale x).fiber.obj U)
    (t v : {t : Spec (.of Ω) ⟶ X' // t ≫ f = x})
    (w : {w : Spec (.of Ω) ⟶ W // w ≫ k = x})
    (hwfst : w.1 ≫ g₁ = t.1) (hwsnd : w.1 ≫ g₂ = v.1) :
      c t (sectionGerm f G x t U z s') =
        c v (sectionGerm f G x v U z s') := by
  obtain ⟨d, hd, hddiag⟩ := descent_coordinate_at_lift k G x w
  have ht := etaleSetDescentComparison_coordinates f g₁ k hk₁
    G Ω x t w hwfst (c t) (hc t) (hdiag t) d hd hddiag U z s'
  have hv := etaleSetDescentComparison_coordinates f g₂ k hk₂
    G Ω x v w hwsnd (c v) (hc v) (hdiag v) d hd hddiag U z s'
  let q := fun a ↦ d (sectionGerm k G x w U z a)
  exact ht.trans ((congrArg q hs).trans hv.symm)


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem coordinates_on_commuting_square
    {X X' W : Scheme.{u}} (f : X' ⟶ X)
    (g₁ g₂ : W ⟶ X') (hp : g₁ ≫ f = g₂ ≫ f)
    (G : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (c : ∀ t : {t : Spec (.of Ω) ⟶ X' // t ≫ f = x},
      (Scheme.pointSmallEtale t.1).sheafFiber.obj ((Scheme.etaleSetPullback f).obj G) →
        (Scheme.pointSmallEtale x).sheafFiber.obj G)
    (hc : ∀ t, Function.Bijective (c t))
    (hdiag : ∀ t a, c t ((colimit.pre
          ((Functor.Elements.π (Scheme.pointSmallEtale t.1).fiber).op ⋙
            ((Scheme.etaleSetPullback f).obj G).obj)
          (Etale.baseChangeNbhd f x t).op) ((Scheme.pointSmallEtale x).sheafFiber.map
            ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
              (X.smallGrothendieckTopology @Etale)
              (X'.smallGrothendieckTopology @Etale)).unit.app G) a)) = a)
    (U : X.Etale)
    (s' : ((Scheme.etaleSetPullback f).obj G).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
        U)))
    (hs :
        etaleSetDescentComparison f (g₁) G U s' =
          eqToHom (congrArg
            (fun k : W ⟶ X ↦ ((Scheme.etaleSetPullback k).obj G).obj.obj
              (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
                U))) hp.symm)
            (etaleSetDescentComparison f (g₂) G
              U s'))
    (z : (Scheme.pointSmallEtale x).fiber.obj U)
    (t v : {t : Spec (.of Ω) ⟶ X' // t ≫ f = x})
    (w₀ : Spec (.of Ω) ⟶ W) (hwfst : w₀ ≫ g₁ = t.1) (hwsnd : w₀ ≫ g₂ = v.1) :
      c t (sectionGerm f G x t U z s') =
        c v (sectionGerm f G x v U z s') := by
  generalize hk₁ : g₁ ≫ f = k
  have hk₂ : g₂ ≫ f = k := hp.symm.trans hk₁
  have hw : w₀ ≫ k = x := by
    rw [← hk₁, ← Category.assoc, hwfst]
    exact t.2
  have hs₀ := hs.trans (eqToHom_apply_cast _ _)
  have hs' := cast_section_eq
    (fun k : W ⟶ X ↦ ((Scheme.etaleSetPullback k).obj G).obj.obj (op
      ((MorphismProperty.Over.pullback @Etale ⊤ k).obj U)))
    (i := g₁ ≫ f) (j := g₂ ≫ f) (k := k) hp.symm hk₁ hk₂
    (l := sectionComparison f g₁ G U s') (r := sectionComparison f g₂ G U s') hs₀
  exact coordinates_on_square f g₁ g₂ k hk₁ hk₂
    G Ω x c hc hdiag U s' hs' z t v ⟨w₀, hw⟩ hwfst hwsnd


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Compatible comparison pullbacks give equal coordinates at any two geometric lifts.
Source: Stacks Project, Étale Cohomology, Lemma 09Z2, last paragraph, and Remark 09Z3.
(blueprint: lem-weil-pbc-sets-finite-descent-coordinates-constant).

Proof: The inverse-image stalk bijection identifies the restriction of the stalk unit
at every lift with the identity. Hence any bijective coordinate identification satisfying
`hdiag` is the inverse of that restriction, so agrees with the germ-compatible
identification of Tag 03Q1 (3). For two lifts t and v, their pair gives a geometric
point of X' ×_X X' by the pullback universal property. Pull the equality of comparison
sections to its germ. The composition-unit formula of the inverse-image comparison
identifies the first germ with the coordinate at t and the second with the coordinate
at v. To justify this for arbitrary germs, represent their image under the bijective
inverse-image stalk comparison by a germ of a section of G; the germ formula represents
the original germ by the unit of that section. The composition-unit formula applies
on this representative. Naturality of germs under the fibre-product pasting isomorphism
and transport along the pullback condition identify the two ambient stalks. Applying
the composite inverse-image stalk comparison to the compatible germs therefore gives
the asserted equality. No lift is chosen: if the fibre is empty the assertion is
vacuous, and it also holds for the empty sheaf because there is then no section s'. -/
theorem finiteSurjectiveSetDescent_coordinates_constant
    {X X' : Scheme.{u}} (f : X' ⟶ X) [IsFinite f]
    (G : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (c : ∀ t : {t : Spec (.of Ω) ⟶ X' // t ≫ f = x},
      (Scheme.pointSmallEtale t.1).sheafFiber.obj ((Scheme.etaleSetPullback f).obj G) →
        (Scheme.pointSmallEtale x).sheafFiber.obj G)
    (hc : ∀ t, Function.Bijective (c t))
    (hdiag : ∀ t a, c t ((colimit.pre
          ((Functor.Elements.π (Scheme.pointSmallEtale t.1).fiber).op ⋙
            ((Scheme.etaleSetPullback f).obj G).obj)
          (Etale.baseChangeNbhd f x t).op) ((Scheme.pointSmallEtale x).sheafFiber.map
            ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
              (X.smallGrothendieckTopology @Etale)
              (X'.smallGrothendieckTopology @Etale)).unit.app G) a)) = a)
    (s' : ((Scheme.etaleSetPullback f).obj G).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
        (Scheme.Etale.mk (𝟙 X)))))
    (hs :
        etaleSetDescentComparison f (pullback.fst f f) G (Scheme.Etale.mk (𝟙 X)) s' =
          eqToHom (congrArg
            (fun k : pullback f f ⟶ X ↦ ((Scheme.etaleSetPullback k).obj G).obj.obj
              (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
                (Scheme.Etale.mk (𝟙 X))))) (pullback.condition (f := f) (g := f)).symm)
            (etaleSetDescentComparison f (pullback.snd f f) G
              (Scheme.Etale.mk (𝟙 X)) s'))
    (z : (Scheme.pointSmallEtale x).fiber.obj (Scheme.Etale.mk (𝟙 X))) :
    ∀ t v : {t : Spec (.of Ω) ⟶ X' // t ≫ f = x},
      c t ((colimit.pre
          ((Functor.Elements.π (Scheme.pointSmallEtale t.1).fiber).op ⋙
            ((Scheme.etaleSetPullback f).obj G).obj)
          (Etale.baseChangeNbhd f x t).op)
        ((Scheme.pointSmallEtale x).toPresheafFiber (Scheme.Etale.mk (𝟙 X)) z
      ((f.Etale.sheafPushforwardContinuous (Type (u + 1))
        X.smallEtaleTopology X'.smallEtaleTopology).obj
          ((Scheme.etaleSetPullback f).obj G)).obj s')) =
      c v ((colimit.pre
          ((Functor.Elements.π (Scheme.pointSmallEtale v.1).fiber).op ⋙
            ((Scheme.etaleSetPullback f).obj G).obj)
          (Etale.baseChangeNbhd f x v).op)
        ((Scheme.pointSmallEtale x).toPresheafFiber (Scheme.Etale.mk (𝟙 X)) z
      ((f.Etale.sheafPushforwardContinuous (Type (u + 1))
        X.smallEtaleTopology X'.smallEtaleTopology).obj
          ((Scheme.etaleSetPullback f).obj G)).obj s')) := by
  intro t v
  obtain ⟨w₀, hwfst, hwsnd⟩ := pullback.exists_lift f f t.1 v.1 (t.2.trans v.2.symm)
  exact coordinates_on_commuting_square f (pullback.fst f f) (pullback.snd f f)
    (pullback.condition (f := f) (g := f)) G Ω x c hc hdiag
    (Scheme.Etale.mk (𝟙 X)) s' hs z t v w₀ hwfst hwsnd

end AlgebraicGeometry
