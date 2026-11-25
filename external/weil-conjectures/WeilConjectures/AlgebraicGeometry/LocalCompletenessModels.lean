/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.LocalCoefficientLocalization
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedSiteCompleteElement
import WeilConjectures.CategoryTheory.SliceAwayLocalizationFreeResolution

/-! # Comparison of the two local completeness models -/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

private theorem telescope_isColimit
    {A : Type*} [Category A] [Preadditive A] [HasCoproducts A]
    (X : A) (f : X ⟶ X)
    (P L : A) (ι : ℕ → (X ⟶ P))
    (hP : IsColimit (Cofan.mk P (fun n : ULift.{u} ℕ ↦ ι n.down)))
    (d : P ⟶ P) (q : P ⟶ L) (hdq : d ≫ q = 0)
    (hq : IsColimit (CokernelCofork.ofπ q hdq))
    (hd : ∀ n, ι n ≫ d = ι n - f ≫ ι (n + 1)) :
    ∃ c : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ X) (fun _ ↦ f)),
      c.pt = L ∧ Nonempty (IsColimit c) := by
  have hcompat (n : ℕ) : f ≫ ι (n + 1) ≫ q = ι n ≫ q := by
    have h := congrArg (fun k ↦ ι n ≫ k) hdq
    rw [← Category.assoc, hd, Preadditive.sub_comp, Category.assoc] at h
    exact (sub_eq_zero.mp (by simpa only [comp_zero] using h)).symm
  let c : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ X) (fun _ ↦ f)) :=
    { pt := L
      ι := NatTrans.ofSequence (fun n ↦ ι n ≫ q) (by
        intro n
        simpa using hcompat n) }
  let b (s : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ X) (fun _ ↦ f))) : P ⟶ s.pt :=
    hP.desc (Cofan.mk s.pt (fun n : ULift.{u} ℕ ↦ s.ι.app n.down))
  have hb (s : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ X) (fun _ ↦ f)))
      (n : ℕ) : ι n ≫ b s = s.ι.app n :=
    hP.fac _ (Discrete.mk (ULift.up n))
  have hdb (s : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ X) (fun _ ↦ f))) :
      d ≫ b s = 0 := by
    apply hP.hom_ext
    rintro ⟨⟨n⟩⟩
    change ι n ≫ (d ≫ b s) = ι n ≫ 0
    rw [← Category.assoc, hd, Preadditive.sub_comp, Category.assoc, hb, hb, comp_zero]
    exact sub_eq_zero.mpr (by
      simpa using (s.w (homOfLE (Nat.le_succ n))).symm)
  refine ⟨c, rfl, ⟨?_⟩⟩
  refine { desc := fun s ↦ hq.desc (CokernelCofork.ofπ (b s) (hdb s))
           fac := ?_
           uniq := ?_ }
  · intro s n
    change (ι n ≫ q) ≫ _ = _
    rw [Category.assoc]
    have ht : q ≫ hq.desc (CokernelCofork.ofπ (b s) (hdb s)) = b s :=
      hq.fac _ WalkingParallelPair.one
    rw [ht]
    exact hb s n
  · intro s m hm
    have he : q ≫ m = b s := by
      apply hP.hom_ext
      rintro ⟨⟨n⟩⟩
      change ι n ≫ (q ≫ m) = ι n ≫ b s
      rw [hb, ← Category.assoc]
      exact hm n
    apply hq.hom_ext
    intro j
    cases j
    · change (d ≫ q) ≫ _ = (d ≫ q) ≫ _
      rw [hdq, zero_comp, zero_comp]
    · exact he.trans (show q ≫ hq.desc (CokernelCofork.ofπ (b s) (hdb s)) = b s
        from hq.fac _ WalkingParallelPair.one).symm

private theorem fraction_form {A : Type u} [CommRing A] (f : A)
    (z : Localization.Away f) :
    ∃ (a : A) (n : ℕ), z = algebraMap A _ a * IsLocalization.Away.invSelf f ^ n := by
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj f z
  have hi : (algebraMap A (Localization.Away f) f) ^ n *
      IsLocalization.Away.invSelf f ^ n = 1 := by
    rw [← mul_pow, IsLocalization.Away.mul_invSelf, one_pow]
  refine ⟨a, n, ?_⟩
  calc
    z = z * ((algebraMap A (Localization.Away f) f) ^ n *
        IsLocalization.Away.invSelf f ^ n) := by rw [hi, mul_one]
    _ = _ := by rw [← mul_assoc, h]

private theorem fraction_restriction
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (s : (R.obj ⋙ forget CommRingCat).sections)
    {V W : Cᵒᵖ} (g : V ⟶ W) (a : R.obj.obj V) (n : ℕ) :
    ringedSectionLocalizationMap R s g
      (algebraMap _ _ a * IsLocalization.Away.invSelf (R := R.obj.obj V) (s.val V) ^ n) =
      algebraMap _ _ (R.obj.map g a) *
        IsLocalization.Away.invSelf (R := R.obj.obj W) (s.val W) ^ n := by
  have hc (b : R.obj.obj V) :
      ringedSectionLocalizationMap R s g (algebraMap _ _ b) =
        algebraMap _ _ (R.obj.map g b) :=
    IsLocalization.Away.lift_eq (R := R.obj.obj V) (s.val V : R.obj.obj V)
      (ringedSectionLocalization_isUnit R s g) b
  have hi : ringedSectionLocalizationMap R s g
      (IsLocalization.Away.invSelf (R := R.obj.obj V) (s.val V)) =
        IsLocalization.Away.invSelf (R := R.obj.obj W) (s.val W) := by
    have hm := congrArg (ringedSectionLocalizationMap R s g)
      (IsLocalization.Away.mul_invSelf (R := R.obj.obj V)
        (S := ringedSectionLocalizationCarrier R s V) (s.val V : R.obj.obj V))
    have hs : R.obj.map g (s.val V : R.obj.obj V) = (s.val W : R.obj.obj W) :=
      s.property g
    rw [map_mul, map_one, hc, hs] at hm
    have hunit := IsLocalization.Away.mul_invSelf
      (R := R.obj.obj W) (S := ringedSectionLocalizationCarrier R s W) (s.val W : R.obj.obj W)
    calc
      _ = 1 * ringedSectionLocalizationMap R s g
          (IsLocalization.Away.invSelf (R := R.obj.obj V) (s.val V)) := (one_mul _).symm
      _ = (algebraMap (R.obj.obj W) (ringedSectionLocalizationCarrier R s W) (s.val W) *
          IsLocalization.Away.invSelf (R := R.obj.obj W) (s.val W)) *
          ringedSectionLocalizationMap R s g
            (IsLocalization.Away.invSelf (R := R.obj.obj V) (s.val V)) := by
        rw [hunit]
      _ = IsLocalization.Away.invSelf (R := R.obj.obj W) (s.val W) *
          (algebraMap (R.obj.obj W) (ringedSectionLocalizationCarrier R s W) (s.val W) *
            ringedSectionLocalizationMap R s g
              (IsLocalization.Away.invSelf (R := R.obj.obj V) (s.val V))) := by ring
      _ = _ := by rw [hm, mul_one]
  rw [map_mul, map_pow, hc, hi]

private noncomputable def slice_fraction_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (U : C) (f : R.obj.obj (op U))
    (L : SliceAwayLocalization.{u, u, u} R U f) :
    L.val ≅ ringedSectionLocalizationPresheaf (R.over U) (ringedSliceSection R U f) := by
  refine PresheafOfModules.isoMk (fun V ↦ (L.equiv V).toModuleIso) ?_
  intro V W g
  ext x
  change L.equiv W (L.val.map g x) =
    ringedSectionLocalizationMap (R.over U) (ringedSliceSection R U f) g (L.equiv V x)
  obtain ⟨a, n, hn⟩ := fraction_form (R.obj.map V.unop.hom.op f) (L.equiv V x)
  have hx : x = (L.equiv V).symm
      (algebraMap _ _ a * IsLocalization.Away.invSelf (R.obj.map V.unop.hom.op f) ^ n) := by
    rw [← hn, LinearEquiv.symm_apply_apply]
  rw [hx, L.restriction, LinearEquiv.apply_symm_apply]
  exact (fraction_restriction (R.over U) (ringedSliceSection R U f) g a n).symm

private theorem localization_sequences_eq
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (U : C) (f : R.obj.obj (op U)) :
    ringedSiteSectionLocalization (localCoefficientRings R) U f =
      localCoefficientLocalization R U f := by
  unfold ringedSiteSectionLocalization localCoefficientLocalization
  congr 2
  funext n
  ext V
  change (1 : R.obj.obj (op V.unop.left)) * R.obj.map V.unop.hom.op f =
    R.obj.map V.unop.hom.op f * 1
  exact mul_comm _ _

private theorem localization_models_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (U : C) (f : R.obj.obj (op U)) :
    Nonempty (ringedSiteSectionLocalization (localCoefficientRings R) U f ≅
      ringedSectionLocalization (R.over U) (ringedSliceSection R U f)) := by
  classical
  obtain ⟨L, d, q, ⟨hdq, hex⟩, hd, _⟩ := sliceAwayLocalization_free_resolution R U f
  let A := SheafOfModules.unit ((localCoefficientRings R).over U)
  let μ := localSectionMultiplication R U f A
  have hdm (n : ℕ) : SheafOfModules.ιFree (ULift.up n) ≫ d =
      SheafOfModules.ιFree (ULift.up n) - μ ≫ SheafOfModules.ιFree (ULift.up (n + 1)) := by
    ext V
    exact hd V n 1
  obtain ⟨c, hc, ⟨hcol⟩⟩ := telescope_isColimit A μ _ _
    (fun n ↦ SheafOfModules.ιFree (ULift.up n))
    (SheafOfModules.isColimitFreeCofan (ULift.{u} ℕ)) d q hdq hex.gIsCokernel hdm
  let h := colimit.isColimit (Functor.ofSequence (X := fun _ : ℕ ↦ A) (fun _ ↦ μ))
  let e := h.coconePointUniqueUpToIso hcol
  let F := PresheafOfModules.sheafification (𝟙 ((localCoefficientRings R).over U).obj)
  refine ⟨eqToIso (localization_sequences_eq R U f) ≪≫ e ≪≫ eqToIso hc ≪≫
    F.mapIso (slice_fraction_iso R U f L)⟩

private noncomputable def restriction_models_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (localCoefficientRings R))]
    [∀ U : C, HasDerivedCategory.{w}
      (ringedSiteModules.{u} ((localCoefficientRings R).over U))]
    (K : ringedSiteDerived R) (U : C) :
    (ringedDerivedRestriction R U).obj K ≅
      ringedSiteDerivedRestriction (localCoefficientRings R) U K :=
  ((ringedDerivedRestriction R U).mapIso (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
    (SheafOfModules.overFunctor.{u} (localCoefficientRings R) U).mapDerivedCategoryFactors.app
      (DerivedCategory.Q.objPreimage K)

/-- The fraction and sequential-colimit models of local completeness agree.
Source: Stacks Project, algebraization.tex, Tag 0997.
Proof: the maps sending the element a at stage n to a/f^n identify the sequential
colimit of the ring modules with the sheafification of sectionwise localization.
Exact slice restriction identifies its chosen-representative model with its descended
functor. Apply the derived internal-Hom functor to these two isomorphisms.
(auxiliary; not a blueprint node). -/
theorem localCompleteness_models_iff
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (localCoefficientRings R))]
    [∀ U : C, HasDerivedCategory.{w}
      (ringedSiteModules.{u} ((localCoefficientRings R).over U))]
    (K : ringedSiteDerived R) (U : C) (f : R.obj.obj (op U)) :
    IsZero ((derivedInternalHom (J.over U) (R.over U)).obj
      (op ((DerivedCategory.singleFunctor _ 0).obj
        (ringedSectionLocalization (R.over U) (ringedSliceSection R U f))),
        (ringedDerivedRestriction R U).obj K)) ↔
      IsRingedSiteCompleteElement J R K U f := by
  obtain ⟨e⟩ := localization_models_iso R U f
  let eL := (DerivedCategory.singleFunctor _ 0).mapIso e
  let eK := restriction_models_iso R K U
  let eH := (derivedInternalHom (J.over U) (R.over U)).mapIso (eL.op.prod eK)
  exact ⟨fun h ↦ h.of_iso eH.symm, fun h ↦ h.of_iso eH⟩

end CategoryTheory
