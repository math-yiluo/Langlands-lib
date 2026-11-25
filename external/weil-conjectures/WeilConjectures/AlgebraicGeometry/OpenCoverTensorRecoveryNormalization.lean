/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleRecoveryComparisonIso
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
public import WeilConjectures.AlgebraicGeometry.OpenCoverTensorPullbackComparison

/-! # Normalization of one tensor recovery comparison
Source: Stacks Project, Tags 0095 and 0096. -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

private lemma mapped_path_triangle
    {C D : Type*} [Category C] [Category D] [Quiver.IsThin C] (F : C ⥤ D)
    {A B C₁ E : C} (a : A ⟶ B) (b : B ⟶ C₁) (c : C₁ ⟶ E) (d : A ⟶ E) :
    ((𝟙 _ ≫ F.map a) ≫ 𝟙 _ ≫ F.map b ≫ 𝟙 _) ≫ 𝟙 _ ≫ F.map c =
      𝟙 _ ≫ F.map d := by
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

private lemma mate_openCoverComparison_inv {A B : Scheme.{u}}
    (f : B ⟶ A) (U : A.OpenCover.{u}) (a : U.I₀) :
    conjugateEquiv
      ((pullbackPushforwardAdjunction (U.f a)).comp
        (pullbackPushforwardAdjunction (U.pullbackHom f a)))
      ((Classical.choose (exists_tensorPullbackAdjunction f)).comp
        (pullbackPushforwardAdjunction ((U.pullback₁ f).f a)))
      (openCoverTensorPullbackComparison f U a).inv =
      (pushforwardComp (U.pullbackHom f a) (U.f a)).hom ≫
        (pushforwardCongr (U.pullbackHom_map f a)).hom ≫
          (pushforwardComp ((U.pullback₁ f).f a) f).inv := by
  have h : conjugateIsoEquiv
      ((Classical.choose (exists_tensorPullbackAdjunction f)).comp
        (pullbackPushforwardAdjunction ((U.pullback₁ f).f a)))
      ((pullbackPushforwardAdjunction (U.f a)).comp
        (pullbackPushforwardAdjunction (U.pullbackHom f a)))
      (openCoverTensorPullbackComparison f U a) =
      (pushforwardComp ((U.pullback₁ f).f a) f) ≪≫
        (pushforwardCongr (U.pullbackHom_map f a)).symm ≪≫
          (pushforwardComp (U.pullbackHom f a) (U.f a)).symm := by
    apply Iso.ext
    exact mate_openCoverComparison f U a
  simpa only [Iso.trans_inv, Iso.symm_inv, conjugateIsoEquiv_apply_inv, Category.assoc]
    using congrArg Iso.inv h

private lemma mate_unique {A B : Type*} [Category A] [Category B]
    {F G : A ⥤ B} {R : B ⥤ A} (a : F ⊣ R) (b : G ⊣ R) :
    conjugateEquiv b a (Adjunction.leftAdjointUniq a b).hom = 𝟙 R := by
  have hh : conjugateIsoEquiv a b (Adjunction.leftAdjointUniq a b).symm =
      Iso.refl R := by
    simp [Adjunction.leftAdjointUniq]
  exact congrArg Iso.inv hh

private lemma mate_pullbackCongr_inv {A B : Scheme.{u}} {f g : A ⟶ B} (w : f = g) :
    conjugateEquiv (pullbackPushforwardAdjunction f) (pullbackPushforwardAdjunction g)
      (pullbackCongr w).inv = (pushforwardCongr w).hom := by
  subst g
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_inv, conjugateEquiv_id]
  ext N V
  simp

/-- A single recovery comparison, followed by the inverse base-chart comparison,
is ordinary pullback along the total chart path preceded by the unique comparison
of left adjoints for the total base map.
Source: Stacks Project, Tags 0095 and 0096; step 1 of
lem-pc-open-cover-tensor-comparison-coherence.
(blueprint: lem-pc-open-cover-tensor-recovery-normalization).
Proof: Expand the recovery comparison as a composite of natural transformations
and compare its composite with the inverse base-chart comparison to the proposed
normal form before evaluating at M. Apply injectivity of the mate correspondence
under the tensor total-map adjunction and the three ordinary chart adjunctions.
Mates reverse composition and preserve whiskering and associators. The mate of the
unique comparison of left adjoints is the identity. The tensor composition mate is
pushforwardComp followed by pushforwardCongr, by its definition. For the chart
comparisons, expand their definitions and use conjugateEquiv_pullbackComp_inv and
the inverse mate formula for ordinary composition; equality transports give the
corresponding pushforward transports. On sections over each open, both resulting
composites are maps of the same module presheaf along paths between the same opens.
These paths are equal because the category of opens is thin. Thus the mates agree;
injectivity and evaluation at M give the required identity. The equality H supplies
the endpoints for the ordinary total chart path.
All constructions exist for arbitrary modules and charts, including empty charts
and the zero module, and no invertibility of the scheme maps is required. -/
theorem openCover_tensor_recovery_normalization
    {X Y W : Scheme.{u}} (q : Y ⟶ X) (p : W ⟶ Y) (h : W ⟶ X)
    (w : p ≫ q = h) (U : X.OpenCover.{u}) (a : U.I₀)
    (H : (Scheme.Cover.pullbackHom (U.pullback₁ q) p a ≫ U.pullbackHom q a) ≫ U.f a =
      ((U.pullback₁ q).pullback₁ p).f a ≫ h)
    (c : tensorPullback h ≅ pullback h)
    (hc : c = Adjunction.leftAdjointUniq
      (Classical.choose (exists_tensorPullbackAdjunction h)) (pullbackPushforwardAdjunction h))
    (t : pullback (U.f a) ⋙ pullback (U.pullbackHom q a) ≅
      tensorPullback q ⋙ pullback ((U.pullback₁ q).f a))
    (ht : t = openCoverTensorPullbackComparison q U a)
    (ck : tensorPullback h ⋙ pullback (((U.pullback₁ q).pullback₁ p).f a) ≅
      (tensorPullback q ⋙ pullback ((U.pullback₁ q).f a)) ⋙
        pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p a))
    (hck : ck = moduleRecoveryComparisonIso (tensorPullback h) (tensorPullback q)
      (tensorPullback p) (pullback ((U.pullback₁ q).f a))
      (pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p a))
      (pullback (((U.pullback₁ q).pullback₁ p).f a))
      (tensorPullbackCompositionIso p q h w)
      (openCoverTensorPullbackComparison p (U.pullback₁ q) a))
    (rho : pullback h ⋙ pullback (((U.pullback₁ q).pullback₁ p).f a) ≅
      (pullback (U.f a) ⋙ pullback (U.pullbackHom q a)) ⋙
        pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p a))
    (hrho : rho = pullbackComp (((U.pullback₁ q).pullback₁ p).f a) h ≪≫
      (pullbackCongr H).symm ≪≫
      (pullbackComp (Scheme.Cover.pullbackHom (U.pullback₁ q) p a ≫
        U.pullbackHom q a) (U.f a)).symm ≪≫
      Functor.isoWhiskerLeft (pullback (U.f a))
        (pullbackComp (Scheme.Cover.pullbackHom (U.pullback₁ q) p a)
          (U.pullbackHom q a)).symm ≪≫
      (Functor.associator (pullback (U.f a)) (pullback (U.pullbackHom q a))
        (pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p a))).symm)
    (M : X.Modules) :
    ck.hom.app M ≫ (pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p a)).map
        (t.inv.app M) =
      (pullback (((U.pullback₁ q).pullback₁ p).f a)).map (c.hom.app M) ≫
        rho.hom.app M := by
  subst c
  subst t
  subst ck
  subst rho
  let aq := Classical.choose (exists_tensorPullbackAdjunction q)
  let ap := Classical.choose (exists_tensorPullbackAdjunction p)
  let ah := Classical.choose (exists_tensorPullbackAdjunction h)
  let a₀ := pullbackPushforwardAdjunction (U.f a)
  let a₁ := pullbackPushforwardAdjunction (U.pullbackHom q a)
  let a₂ := pullbackPushforwardAdjunction
    (Scheme.Cover.pullbackHom (U.pullback₁ q) p a)
  let au := pullbackPushforwardAdjunction ((U.pullback₁ q).f a)
  let av := pullbackPushforwardAdjunction (((U.pullback₁ q).pullback₁ p).f a)
  let lhs := (moduleRecoveryComparisonIso (tensorPullback h) (tensorPullback q)
      (tensorPullback p) (pullback ((U.pullback₁ q).f a))
      (pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p a))
      (pullback (((U.pullback₁ q).pullback₁ p).f a))
      (tensorPullbackCompositionIso p q h w)
      (openCoverTensorPullbackComparison p (U.pullback₁ q) a)).hom ≫
    Functor.whiskerRight (openCoverTensorPullbackComparison q U a).inv
      (pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p a))
  let rho := pullbackComp (((U.pullback₁ q).pullback₁ p).f a) h ≪≫
      (pullbackCongr H).symm ≪≫
      (pullbackComp (Scheme.Cover.pullbackHom (U.pullback₁ q) p a ≫
        U.pullbackHom q a) (U.f a)).symm ≪≫
      Functor.isoWhiskerLeft (pullback (U.f a))
        (pullbackComp (Scheme.Cover.pullbackHom (U.pullback₁ q) p a)
          (U.pullbackHom q a)).symm ≪≫
      (Functor.associator (pullback (U.f a)) (pullback (U.pullbackHom q a))
        (pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p a))).symm
  let rhs := Functor.whiskerRight
    (Adjunction.leftAdjointUniq ah (pullbackPushforwardAdjunction h)).hom
    (pullback (((U.pullback₁ q).pullback₁ p).f a)) ≫ rho.hom
  have he : conjugateEquiv (aq.comp ap) ah
      (tensorPullbackCompositionIso p q h w).hom =
      (pushforwardComp p q).hom ≫ (pushforwardCongr w).hom := by
    unfold tensorPullbackCompositionIso
    exact Equiv.apply_symm_apply _ _
  have heq : lhs = rhs := by
    apply (conjugateEquiv ((a₀.comp a₁).comp a₂) (ah.comp av)).injective
    dsimp only [lhs, rhs, moduleRecoveryComparisonIso, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
    simp only [← Category.assoc]
    rw [← conjugateEquiv_comp _ ((aq.comp au).comp a₂),
      ← conjugateEquiv_comp _ (aq.comp (au.comp a₂)),
      ← conjugateEquiv_comp _ (aq.comp (ap.comp av)),
      ← conjugateEquiv_comp _ ((aq.comp ap).comp av)]
    simp only [conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft,
      mate_associator_inv, conjugateEquiv_associator_hom, he]
    dsimp only [rho, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom]
    simp only [← Category.assoc]
    rw [← conjugateEquiv_comp _ (a₀.comp (a₁.comp a₂)),
      ← conjugateEquiv_comp _ (a₀.comp (pullbackPushforwardAdjunction
        (Scheme.Cover.pullbackHom (U.pullback₁ q) p a ≫ U.pullbackHom q a))),
      ← conjugateEquiv_comp _ (pullbackPushforwardAdjunction
        ((Scheme.Cover.pullbackHom (U.pullback₁ q) p a ≫ U.pullbackHom q a) ≫ U.f a)),
      ← conjugateEquiv_comp _ (pullbackPushforwardAdjunction
        (((U.pullback₁ q).pullback₁ p).f a ≫ h)),
      ← conjugateEquiv_comp _ ((pullbackPushforwardAdjunction h).comp av)]
    simp only [conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft,
      mate_unique, mate_associator_inv]
    dsimp only [aq, ap, ah, a₀, a₁, a₂, au, av]
    simp only [mate_openCoverComparison_inv, conjugateEquiv_pullbackComp_inv,
      mate_pullbackComp_hom, mate_pullbackCongr_inv]
    apply NatTrans.ext
    funext N
    apply hom_ext
    intro O
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.map_comp, Hom.comp_app, pushforwardComp_hom_app_app,
      pushforwardComp_inv_app_app,
      pushforwardCongr_hom_app_app,
      pushforward_map_app, pushforward_obj_presheaf_map, Category.id_comp,
      Category.comp_id, Functor.whiskerLeft_id']
    exact mapped_path_triangle N.presheaf _ _ _ _
  have hm := congrArg (fun n ↦ n.app M) heq
  exact hm

end AlgebraicGeometry.Scheme.Modules
