/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
public import WeilConjectures.AlgebraicGeometry.OpenCoverTensorPullbackComparison

/-! # Composition square for restriction and tensor pullback
Source: Stacks Project, Sheaves on Spaces, Tags 0095 and 0096.
(blueprint: lem-pc-open-cover-tensor-pullback-composition). -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
attribute [local irreducible] tensorPullback openCoverTensorPullbackComparison

private lemma mapped_path_square
    {C D : Type*} [Category C] [Category D] [Quiver.IsThin C] (F : C ⥤ D)
    {A B₁ B₂ C₁ C₂ E : C} (a : A ⟶ B₁) (b : B₁ ⟶ C₁) (c : C₁ ⟶ E)
    (d : A ⟶ B₂) (e : B₂ ⟶ C₂) (f : C₂ ⟶ E) :
    (𝟙 _ ≫ F.map a) ≫ (F.map b ≫ 𝟙 _) ≫ 𝟙 _ ≫ F.map c =
      (𝟙 _ ≫ F.map d ≫ 𝟙 _) ≫ (𝟙 _ ≫ F.map e) ≫ 𝟙 _ ≫ F.map f ≫ 𝟙 _ := by
  simp only [Category.id_comp, Category.comp_id, ← Functor.map_comp]
  congr 1
  exact Subsingleton.elim _ _

private lemma mate_associator_inv
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {G : B ⥤ C} {H : C ⥤ D}
    {R : B ⥤ A} {S : C ⥤ B} {T : D ⥤ C}
    (a : F ⊣ R) (b : G ⊣ S) (c : H ⊣ T) :
    conjugateEquiv ((a.comp b).comp c) (a.comp (b.comp c))
      (Functor.associator F G H).inv = (Functor.associator T S R).inv := by
  have h : conjugateIsoEquiv (a.comp (b.comp c)) ((a.comp b).comp c)
      (Functor.associator F G H) = Functor.associator T S R := by
    apply Iso.ext
    exact conjugateEquiv_associator_hom a b c
  exact congrArg Iso.inv h

private lemma mate_pullbackComp_hom {A B C : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) :
    conjugateEquiv (pullbackPushforwardAdjunction (f ≫ g))
      ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
      (pullbackComp f g).hom = (pushforwardComp f g).inv := by
  have h : conjugateIsoEquiv
      ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
      (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).symm =
      pushforwardComp f g := by
    apply Iso.ext
    exact conjugateEquiv_pullbackComp_inv f g
  exact congrArg Iso.inv h

private lemma mate_pullbackCongr {A B : Scheme.{u}} {f g : A ⟶ B} (w : f = g) :
    conjugateEquiv (pullbackPushforwardAdjunction g) (pullbackPushforwardAdjunction f)
      (pullbackCongr w).hom = (pushforwardCongr w).inv := by
  subst g
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, conjugateEquiv_id]
  ext N V
  simp

private lemma mate_openCoverComparison {A B : Scheme.{u}}
    (f : B ⟶ A) (U : A.OpenCover.{u}) (a : U.I₀) :
    conjugateEquiv
      ((Classical.choose (exists_tensorPullbackAdjunction f)).comp
        (pullbackPushforwardAdjunction ((U.pullback₁ f).f a)))
      ((pullbackPushforwardAdjunction (U.f a)).comp
        (pullbackPushforwardAdjunction (U.pullbackHom f a)))
      (openCoverTensorPullbackComparison f U a).hom =
      (pushforwardComp ((U.pullback₁ f).f a) f).hom ≫
        (pushforwardCongr (U.pullbackHom_map f a)).inv ≫
          (pushforwardComp (U.pullbackHom f a) (U.f a)).inv := by
  unfold openCoverTensorPullbackComparison
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, ← Category.assoc]
  rw [← conjugateEquiv_comp _
    ((pullbackPushforwardAdjunction f).comp
      (pullbackPushforwardAdjunction ((U.pullback₁ f).f a)))]
  rw [← conjugateEquiv_comp _
    (pullbackPushforwardAdjunction (((U.pullback₁ f).f a) ≫ f))]
  rw [← conjugateEquiv_comp _
    (pullbackPushforwardAdjunction (U.pullbackHom f a ≫ U.f a))]
  simp only [conjugateEquiv_whiskerRight, Adjunction.leftAdjointUniq,
    Iso.symm_inv, conjugateIsoEquiv_symm_apply_hom, Iso.refl_hom,
    Equiv.apply_symm_apply, Functor.whiskerLeft_id', Category.id_comp,
    conjugateEquiv_pullbackComp_inv, mate_pullbackCongr, mate_pullbackComp_hom,
    Category.assoc]

/-- Restriction comparisons commute with two successive tensor pullbacks.
Source: Stacks Project, Tags 0095 and 0096, pullback and its adjunction.
(blueprint: lem-pc-open-cover-tensor-pullback-composition).
Proof: The hypotheses identify the two projections of the supplied chart
isomorphism with those of the iterated pullback chart. Expand the three
restriction comparisons into ordinary pullback composition and the unique
comparison of left adjoints to pushforward. Transpose the resulting square
through the tensor and ordinary pullback adjunctions. Mates preserve horizontal
and vertical composition, and the unique comparison of left adjoints is the
mate of the identity on pushforward. Hence every intermediate comparison
cancels. On right adjoints the remaining square is pushforward associativity
and the two projection equations hs and hk. On sections over each open it is
just the same restriction map on both sides. Injectivity of the mate
correspondence proves the square of left adjoints; evaluate at M. The assertion
holds for every module, including zero, and for empty charts and identity maps.
There is no local map, global morphism or recovery hypothesis in this square. -/
theorem openCoverTensorPullbackComparison_composition
    {X Y Z : Scheme.{u}} (q : Y ⟶ X) (p : Z ⟶ Y) (b : Z ⟶ X)
    (wpq : p ≫ q = b) (U₀ : X.OpenCover.{u}) (α : U₀.I₀)
    (s : ((U₀.pullback₁ q : Y.OpenCover.{u}).pullback₁ p : Z.OpenCover.{u}).X α ≅
      (U₀.pullback₁ b).X α)
    (hs : s.hom ≫ (U₀.pullback₁ b).f α =
      ((U₀.pullback₁ q : Y.OpenCover.{u}).pullback₁ p : Z.OpenCover.{u}).f α)
    (hk : s.hom ≫ U₀.pullbackHom b α =
      Scheme.Cover.pullbackHom (U₀.pullback₁ q : Y.OpenCover.{u}) p α ≫ U₀.pullbackHom q α)
    (M : X.Modules) :
    let U : Y.OpenCover.{u} := U₀.pullback₁ q
    let V : Z.OpenCover.{u} := U.pullback₁ p
    let W : Z.OpenCover.{u} := U₀.pullback₁ b
    let t₀ := openCoverTensorPullbackComparison b U₀ α
    let t₁ := openCoverTensorPullbackComparison q U₀ α
    let t₂ := openCoverTensorPullbackComparison p U α
    let c := tensorPullbackCompositionIso p q b wpq
    let l := pullbackComp s.hom (U₀.pullbackHom b α) ≪≫ pullbackCongr hk ≪≫
      (pullbackComp (U.pullbackHom p α) (U₀.pullbackHom q α)).symm
    let v := pullbackComp s.hom (W.f α) ≪≫ pullbackCongr hs
    (pullback s.hom).map (t₀.hom.app M) ≫ v.hom.app ((tensorPullback b).obj M) ≫
        (pullback (V.f α)).map (c.hom.app M) =
      l.hom.app ((pullback (U₀.f α)).obj M) ≫
        (pullback (U.pullbackHom p α)).map (t₁.hom.app M) ≫
          t₂.hom.app ((tensorPullback q).obj M) := by
  classical
  dsimp only
  let t₀ := openCoverTensorPullbackComparison b U₀ α
  let t₁ := openCoverTensorPullbackComparison q U₀ α
  let t₂ := openCoverTensorPullbackComparison p (U₀.pullback₁ q : Y.OpenCover.{u}) α
  let c := tensorPullbackCompositionIso p q b wpq
  let l := pullbackComp s.hom (U₀.pullbackHom b α) ≪≫ pullbackCongr hk ≪≫
    (pullbackComp (Scheme.Cover.pullbackHom (U₀.pullback₁ q : Y.OpenCover.{u}) p α)
      (U₀.pullbackHom q α)).symm
  let v := pullbackComp s.hom ((U₀.pullback₁ b : Z.OpenCover.{u}).f α) ≪≫ pullbackCongr hs
  let a₀ := pullbackPushforwardAdjunction (U₀.f α)
  let a₁ := pullbackPushforwardAdjunction (U₀.pullbackHom q α)
  let a₂ := pullbackPushforwardAdjunction
    (Scheme.Cover.pullbackHom (U₀.pullback₁ q : Y.OpenCover.{u}) p α)
  let ab := pullbackPushforwardAdjunction (U₀.pullbackHom b α)
  let au := pullbackPushforwardAdjunction ((U₀.pullback₁ q : Y.OpenCover.{u}).f α)
  let av := pullbackPushforwardAdjunction
    (((U₀.pullback₁ q : Y.OpenCover.{u}).pullback₁ p : Z.OpenCover.{u}).f α)
  let aw := pullbackPushforwardAdjunction ((U₀.pullback₁ b : Z.OpenCover.{u}).f α)
  let as := pullbackPushforwardAdjunction s.hom
  let aq := Classical.choose (exists_tensorPullbackAdjunction q)
  let ap := Classical.choose (exists_tensorPullbackAdjunction p)
  let aT := Classical.choose (exists_tensorPullbackAdjunction b)
  let lhs := Functor.whiskerRight t₀.hom (pullback s.hom) ≫
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft (tensorPullback b) v.hom ≫
      Functor.whiskerRight c.hom
        (pullback (((U₀.pullback₁ q : Y.OpenCover.{u}).pullback₁ p : Z.OpenCover.{u}).f α))
  let rhs := (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (pullback (U₀.f α)) l.hom ≫
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight t₁.hom
          (pullback (Scheme.Cover.pullbackHom (U₀.pullback₁ q : Y.OpenCover.{u}) p α)) ≫
          (Functor.associator _ _ _).hom ≫
            Functor.whiskerLeft (tensorPullback q) t₂.hom ≫
              (Functor.associator _ _ _).inv
  have hv : conjugateEquiv av (aw.comp as) v.hom =
      (pushforwardCongr hs).inv ≫
        (pushforwardComp s.hom ((U₀.pullback₁ b : Z.OpenCover.{u}).f α)).inv := by
    dsimp only [v, av, aw, as, Iso.trans_hom]
    rw [← conjugateEquiv_comp _
      (pullbackPushforwardAdjunction (s.hom ≫ (U₀.pullback₁ b : Z.OpenCover.{u}).f α))]
    rw [mate_pullbackCongr, mate_pullbackComp_hom]
  have hl : conjugateEquiv (a₁.comp a₂) (ab.comp as) l.hom =
      (pushforwardComp (Scheme.Cover.pullbackHom (U₀.pullback₁ q : Y.OpenCover.{u}) p α)
        (U₀.pullbackHom q α)).hom ≫
        (pushforwardCongr hk).inv ≫
          (pushforwardComp s.hom (U₀.pullbackHom b α)).inv := by
    dsimp only [l, a₁, a₂, ab, as, Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc,
      ← conjugateEquiv_comp _
        (pullbackPushforwardAdjunction
          (Scheme.Cover.pullbackHom (U₀.pullback₁ q : Y.OpenCover.{u}) p α ≫ U₀.pullbackHom q α)),
      ← conjugateEquiv_comp _
        (pullbackPushforwardAdjunction (s.hom ≫ U₀.pullbackHom b α))]
    simp only [conjugateEquiv_pullbackComp_inv, mate_pullbackCongr,
      mate_pullbackComp_hom]
  have hc : conjugateEquiv (aq.comp ap) aT c.hom =
      (pushforwardComp p q).hom ≫ (pushforwardCongr wpq).hom := by
    dsimp only [c, tensorPullbackCompositionIso, conjugateIsoEquiv_symm_apply_hom,
      Iso.trans_hom]
    exact Equiv.apply_symm_apply _ _
  have h : lhs = rhs := by
    apply (conjugateEquiv ((aq.comp ap).comp av) ((a₀.comp ab).comp as)).injective
    dsimp only [lhs, rhs]
    simp only [← Category.assoc]
    rw [← conjugateEquiv_comp _ (aT.comp av),
      ← conjugateEquiv_comp _ (aT.comp (aw.comp as)),
      ← conjugateEquiv_comp _ ((aT.comp aw).comp as)]
    rw [← conjugateEquiv_comp _ (aq.comp (ap.comp av)),
      ← conjugateEquiv_comp _ (aq.comp (au.comp a₂)),
      ← conjugateEquiv_comp _ ((aq.comp au).comp a₂),
      ← conjugateEquiv_comp _ ((a₀.comp a₁).comp a₂),
      ← conjugateEquiv_comp _ (a₀.comp (a₁.comp a₂)),
      ← conjugateEquiv_comp _ (a₀.comp (ab.comp as))]
    simp only [conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft,
      conjugateEquiv_associator_hom, mate_associator_inv, hc, hv, hl]
    dsimp only [a₀, a₁, a₂, ab, au, av, aw, as, aq, ap, aT, t₀, t₁, t₂]
    simp only [mate_openCoverComparison]
    apply NatTrans.ext
    funext N
    apply hom_ext
    intro O
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.map_comp, Hom.comp_app, pushforwardComp_hom_app_app,
      pushforwardComp_inv_app_app,
      pushforwardCongr_hom_app_app, pushforwardCongr_inv_app_app,
      pushforward_map_app, pushforward_obj_presheaf_map, Category.id_comp,
      Category.comp_id]
    exact mapped_path_square N.presheaf _ _ _ _ _ _
  have hm := congrArg (fun n ↦ n.app M) h
  simpa only [lhs, rhs, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, t₀, t₁, t₂, c, l, v] using hm

end AlgebraicGeometry.Scheme.Modules
