/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge

@[expose] public section

universe wA wB vA vB uA uB
open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem pro_preserves_at
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {E : Type*} [Category* E] {T : Type*} [Category* T]
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (Q : C ⥤ D) [Q.IsLocalization W] (F : C ⥤ E) (H : E ⥤ T) (X : C)
    (hc : ∃ Y, IsEssentiallyConstantProDiagram
      (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F) Y) :
    Q.HasPointwiseRightKanExtensionAt F (Q.obj X) ∧
      PreservesLimit (StructuredArrow.proj (Q.obj X) Q ⋙ F) H := by
  classical
  obtain ⟨Y, hY⟩ := hc
  obtain ⟨u, j₀, r, hr, hfactor⟩ := hY.2
  obtain ⟨hlim, π, ⟨hπ⟩, hden, _⟩ :=
    leftDerived_defined_pointwiseKan_bridge W Q F X Y hY u ⟨j₀, r, hr, hfactor⟩
  let u' : (Functor.const (W.Over ⊤ X)).obj (H.obj Y) ⟶
      MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ (F ⋙ H) :=
    { app := fun j ↦ H.map (u.app j)
      naturality := by
        intro i j f
        change 𝟙 _ ≫ H.map (u.app j) = H.map (u.app i) ≫ H.map (F.map f.left)
        rw [Category.id_comp, ← H.map_comp]
        exact H.congr_map (by simpa using u.naturality f) }
  have hr' : u'.app j₀ ≫ H.map r = 𝟙 (H.obj Y) := by
    change H.map (u.app j₀) ≫ H.map r = _
    rw [← H.map_comp, hr]
    exact H.map_id Y
  have hfactor' : ∀ j : W.Over ⊤ X, ∃ (k : W.Over ⊤ X) (a : k ⟶ j₀) (b : k ⟶ j),
      (F ⋙ H).map b.left = (F ⋙ H).map a.left ≫ H.map r ≫ u'.app j := by
    intro j
    obtain ⟨k, a, b, hab⟩ := hfactor j
    refine ⟨k, a, b, ?_⟩
    change H.map (F.map b.left) = _
    change F.map b.left = F.map a.left ≫ r ≫ u.app j at hab
    simp only [hab, H.map_comp]
    rfl
  have hY' : IsEssentiallyConstantProDiagram
      (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ (F ⋙ H)) (H.obj Y) :=
    ⟨hY.1, u', j₀, H.map r, hr', hfactor'⟩
  obtain ⟨_, π', ⟨hπ'⟩, hden', _⟩ :=
    leftDerived_defined_pointwiseKan_bridge W Q (F ⋙ H) X (H.obj Y) hY' u'
      ⟨j₀, H.map r, hr', hfactor'⟩
  have heq (j : StructuredArrow (Q.obj X) Q) : H.map (π.app j) = π'.app j := by
    obtain ⟨a, ha⟩ := Localization.exists_rightFraction Q W j.hom
    let s : W.Over ⊤ X := ⟨Over.mk a.s, a.hs⟩
    let i := StructuredArrow.mk (Localization.isoOfHom Q W s.hom s.prop).inv
    let f : i ⟶ j := StructuredArrow.homMk a.f ha.symm
    have hn := π.naturality f
    have hn' := π'.naturality f
    change 𝟙 Y ≫ π.app j = π.app i ≫ F.map a.f at hn
    change 𝟙 (H.obj Y) ≫ π'.app j = π'.app i ≫ (F ⋙ H).map a.f at hn'
    rw [Category.id_comp] at hn hn'
    rw [hn, hn', H.map_comp, hden s, hden' s]
    rfl
  have hiso : Cone.mk (H.obj Y) π' ≅ H.mapCone (Cone.mk Y π) :=
    Cone.ext (Iso.refl _) (fun j ↦ by simpa using (heq j).symm)
  exact ⟨hlim, preservesLimit_of_preserves_limit_cone hπ
    (IsLimit.ofIsoLimit hπ' hiso)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def denominatorToCostructuredArrow
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    (W : MorphismProperty C) (Q : C ⥤ D) [Q.IsLocalization W] (X : C) :
    W.Under ⊤ X ⥤ CostructuredArrow Q (Q.obj X) where
  obj s := CostructuredArrow.mk (Localization.isoOfHom Q W s.hom s.prop).inv
  map {s t} f := CostructuredArrow.homMk f.right (by
    apply (cancel_epi (Localization.isoOfHom Q W s.hom s.prop).hom).mp
    simp only [Localization.isoOfHom_hom, CostructuredArrow.mk_hom_eq_self]
    rw [← Category.assoc, ← Q.map_comp, MorphismProperty.Under.w f]
    simp only [Localization.isoOfHom_hom_inv_id])
  map_id s := by ext; rfl
  map_comp f g := by ext; rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem ind_fraction_leg_eq
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {E : Type*} [Category* E]
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
    (Q : C ⥤ D) [Q.IsLocalization W] (F : C ⥤ E) (X : C) (Y : E)
    (p : MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F ⟶
      (Functor.const (W.Under ⊤ X)).obj Y)
    {N : C} (a b : W.LeftFraction N X)
    (h : a.map Q (Localization.inverts Q W) = b.map Q (Localization.inverts Q W)) :
    F.map a.f ≫ p.app (⟨Under.mk a.s, a.hs⟩ : W.Under ⊤ X) =
      F.map b.f ≫ p.app (⟨Under.mk b.s, b.hs⟩ : W.Under ⊤ X) := by
  obtain ⟨Z, t₁, t₂, hs, hf, ht⟩ :=
    (MorphismProperty.LeftFraction.map_eq_iff Q W a b).mp h
  let k : W.Under ⊤ X := ⟨Under.mk (a.s ≫ t₁), ht⟩
  let f₁ : (⟨Under.mk a.s, a.hs⟩ : W.Under ⊤ X) ⟶ k :=
    ⟨Under.homMk t₁, trivial, trivial⟩
  let f₂ : (⟨Under.mk b.s, b.hs⟩ : W.Under ⊤ X) ⟶ k :=
    ⟨Under.homMk t₂ hs.symm, trivial, trivial⟩
  have h₁ := p.naturality f₁
  have h₂ := p.naturality f₂
  dsimp at h₁ h₂
  simp only [Category.comp_id] at h₁ h₂
  change F.map t₁ ≫ p.app k = p.app (⟨Under.mk a.s, a.hs⟩ : W.Under ⊤ X) at h₁
  change F.map t₂ ≫ p.app k = p.app (⟨Under.mk b.s, b.hs⟩ : W.Under ⊤ X) at h₂
  rw [← h₁, ← h₂, ← Category.assoc, ← Category.assoc, ← F.map_comp, ← F.map_comp, hf]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem ind_pointwise_bridge
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {E : Type*} [Category* E]
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
    (Q : C ⥤ D) [Q.IsLocalization W] (F : C ⥤ E) (X : C) (Y : E)
    (p : MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F ⟶
      (Functor.const (W.Under ⊤ X)).obj Y)
    (hp : ∃ (j₀ : W.Under ⊤ X) (r : Y ⟶ F.obj j₀.right),
      r ≫ p.app j₀ = 𝟙 Y ∧
        ∀ j : W.Under ⊤ X, ∃ (k : W.Under ⊤ X) (a : j₀ ⟶ k) (b : j ⟶ k),
          F.map b.right = p.app j ≫ r ≫ F.map a.right) :
    ∃ (π : CostructuredArrow.proj Q (Q.obj X) ⋙ F ⟶
        (Functor.const (CostructuredArrow Q (Q.obj X))).obj Y),
      Nonempty (IsColimit (Cocone.mk Y π)) ∧
        ∀ s : W.Under ⊤ X,
          π.app (CostructuredArrow.mk (Localization.isoOfHom Q W s.hom s.prop).inv) =
            p.app s := by
  classical
  let z := fun j : CostructuredArrow Q (Q.obj X) ↦
    (Localization.exists_leftFraction Q W j.hom).choose
  have hz (j : CostructuredArrow Q (Q.obj X)) :
      (z j).map Q (Localization.inverts Q W) = j.hom :=
    (Localization.exists_leftFraction Q W j.hom).choose_spec.symm
  let leg : ∀ j : CostructuredArrow Q (Q.obj X), F.obj j.left ⟶ Y := fun j ↦
    F.map (z j).f ≫ p.app (⟨Under.mk (z j).s, (z j).hs⟩ : W.Under ⊤ X)
  have hleg (j : CostructuredArrow Q (Q.obj X)) (a : W.LeftFraction j.left X)
      (ha : a.map Q (Localization.inverts Q W) = j.hom) :
      leg j = F.map a.f ≫ p.app (⟨Under.mk a.s, a.hs⟩ : W.Under ⊤ X) :=
    ind_fraction_leg_eq W Q F X Y p (z j) a ((hz j).trans ha.symm)
  let π : CostructuredArrow.proj Q (Q.obj X) ⋙ F ⟶
      (Functor.const (CostructuredArrow Q (Q.obj X))).obj Y :=
    { app := leg
      naturality := by
        intro i j f
        change F.map f.left ≫ leg j = leg i ≫ 𝟙 Y
        erw [Category.comp_id]
        let a : W.LeftFraction i.left X :=
          .mk (f.left ≫ (z j).f) (z j).s (z j).hs
        have ha : a.map Q (Localization.inverts Q W) = i.hom := by
          change Q.map (f.left ≫ (z j).f) ≫ inv (Q.map (z j).s) = i.hom
          rw [Q.map_comp, Category.assoc]
          change Q.map f.left ≫ (z j).map Q (Localization.inverts Q W) = i.hom
          rw [hz j, CostructuredArrow.w f]
        rw [hleg i a ha]
        dsimp [leg, a]
        simp only [Functor.map_comp, Category.assoc] }
  have hden (s : W.Under ⊤ X) :
      π.app (CostructuredArrow.mk (Localization.isoOfHom Q W s.hom s.prop).inv) =
        p.app s := by
    change leg (CostructuredArrow.mk
      (Localization.isoOfHom Q W s.hom s.prop).inv) = p.app s
    rw [hleg (CostructuredArrow.mk
      (Localization.isoOfHom Q W s.hom s.prop).inv)
      (MorphismProperty.LeftFraction.ofInv (show X ⟶ s.right from s.hom) s.prop) (by
        simp [MorphismProperty.LeftFraction.map, MorphismProperty.LeftFraction.ofInv,
          Localization.isoOfHom])]
    cases s with
    | mk s hs =>
      cases s with
      | mk l r h =>
        cases l
        change F.map (𝟙 r) ≫ p.app (⟨Under.mk h, hs⟩ : W.Under ⊤ X) = _
        erw [F.map_id, Category.id_comp]
        congr 1
  obtain ⟨j₀, r, hr, hfactor⟩ := hp
  let G := MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F
  let c : Cocone G := Cocone.mk Y p
  have hc : IsColimit c :=
    { desc := fun v ↦ r ≫ v.ι.app j₀
      fac := by
        intro v j
        obtain ⟨k, a, b, hab⟩ := hfactor j
        calc
          p.app j ≫ (r ≫ v.ι.app j₀) =
              p.app j ≫ r ≫ (F.map a.right ≫ v.ι.app k) := by
                rw [← v.w a]
                rfl
          _ = F.map b.right ≫ v.ι.app k := by
            erw [hab]
            simp only [Category.assoc]
          _ = v.ι.app j := v.w b
      uniq := by
        intro v m hm
        calc
          m = (r ≫ p.app j₀) ≫ m := by rw [hr, Category.id_comp]
          _ = r ≫ v.ι.app j₀ := by rw [Category.assoc, hm j₀] }
  let d : Cocone (CostructuredArrow.proj Q (Q.obj X) ⋙ F) := Cocone.mk Y π
  let I := denominatorToCostructuredArrow W Q X
  have hd : IsColimit d :=
    { desc := fun v ↦ hc.desc (v.whisker I)
      fac := by
        intro v j
        let a := z j
        let s : W.Under ⊤ X := ⟨Under.mk a.s, a.hs⟩
        let f : j ⟶ I.obj s := CostructuredArrow.homMk a.f (hz j)
        change leg j ≫ hc.desc (v.whisker I) = v.ι.app j
        rw [hleg j a (hz j), Category.assoc]
        change F.map a.f ≫ (c.ι.app s ≫ hc.desc (v.whisker I)) = v.ι.app j
        rw [hc.fac (v.whisker I) s]
        exact v.w f
      uniq := by
        intro v m hm
        apply hc.uniq (v.whisker I) m
        intro s
        change p.app s ≫ m = v.ι.app (I.obj s)
        rw [← hden s]
        exact hm (I.obj s) }
  exact ⟨π, ⟨hd⟩, hden⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem ind_preserves_at
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {E : Type*} [Category* E] {T : Type*} [Category* T]
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
    (Q : C ⥤ D) [Q.IsLocalization W] (F : C ⥤ E) (H : E ⥤ T) (X : C)
    (hc : ∃ Y, IsEssentiallyConstantIndDiagram
      (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F) Y) :
    Q.HasPointwiseLeftKanExtensionAt F (Q.obj X) ∧
      PreservesColimit (CostructuredArrow.proj Q (Q.obj X) ⋙ F) H := by
  classical
  obtain ⟨Y, hY⟩ := hc
  obtain ⟨p, j₀, r, hr, hfactor⟩ := hY.2
  obtain ⟨π, ⟨hπ⟩, hden⟩ := ind_pointwise_bridge W Q F X Y p ⟨j₀, r, hr, hfactor⟩
  let p' : MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ (F ⋙ H) ⟶
      (Functor.const (W.Under ⊤ X)).obj (H.obj Y) :=
    { app := fun j ↦ H.map (p.app j)
      naturality := by
        intro i j f
        change H.map (F.map f.right) ≫ H.map (p.app j) = H.map (p.app i) ≫ 𝟙 _
        rw [Category.comp_id, ← H.map_comp]
        exact H.congr_map (by simpa using p.naturality f) }
  have hr' : H.map r ≫ p'.app j₀ = 𝟙 (H.obj Y) := by
    change H.map r ≫ H.map (p.app j₀) = _
    rw [← H.map_comp, hr]
    exact H.map_id Y
  have hfactor' : ∀ j : W.Under ⊤ X,
      ∃ (k : W.Under ⊤ X) (a : j₀ ⟶ k) (b : j ⟶ k),
        (F ⋙ H).map b.right = p'.app j ≫ H.map r ≫ (F ⋙ H).map a.right := by
    intro j
    obtain ⟨k, a, b, hab⟩ := hfactor j
    refine ⟨k, a, b, ?_⟩
    change H.map (F.map b.right) = _
    change F.map b.right = p.app j ≫ r ≫ F.map a.right at hab
    simp only [hab, H.map_comp]
    rfl
  obtain ⟨π', ⟨hπ'⟩, hden'⟩ := ind_pointwise_bridge W Q (F ⋙ H) X (H.obj Y) p'
    ⟨j₀, H.map r, hr', hfactor'⟩
  have heq (j : CostructuredArrow Q (Q.obj X)) : H.map (π.app j) = π'.app j := by
    obtain ⟨a, ha⟩ := Localization.exists_leftFraction Q W j.hom
    let s : W.Under ⊤ X := ⟨Under.mk a.s, a.hs⟩
    let i : CostructuredArrow Q (Q.obj X) :=
      CostructuredArrow.mk (Localization.isoOfHom Q W s.hom s.prop).inv
    let f : j ⟶ i := CostructuredArrow.homMk a.f ha.symm
    have hn := π.naturality f
    have hn' := π'.naturality f
    change F.map a.f ≫ π.app i = π.app j ≫ 𝟙 Y at hn
    change (F ⋙ H).map a.f ≫ π'.app i = π'.app j ≫ 𝟙 (H.obj Y) at hn'
    erw [Category.comp_id] at hn hn'
    rw [← hn, ← hn', H.map_comp, hden s, hden' s]
    rfl
  have hiso : Cocone.mk (H.obj Y) π' ≅ H.mapCocone (Cocone.mk Y π) :=
    Cocone.ext (Iso.refl _) (fun j ↦ by simpa using (heq j).symm)
  exact ⟨⟨⟨_, hπ⟩⟩, preservesColimit_of_preserves_colimit_cocone hπ
    (IsColimit.ofIsoColimit hπ' hiso)⟩

private theorem pro_absolute
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {E : Type*} [Category* E] {T : Type*} [Category* T]
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (Q : C ⥤ D) [Q.IsLocalization W] (F : C ⥤ E) (H : E ⥤ T)
    (hc : ∀ X, ∃ Y, IsEssentiallyConstantProDiagram
      (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F) Y) :
    H.PreservesRightKanExtension F Q := by
  classical
  have h (X : C) := pro_preserves_at W Q F H X (hc X)
  have : Q.EssSurj := Localization.essSurj Q W
  have : Q.HasPointwiseRightKanExtension F := fun Y ↦
    (Functor.hasPointwiseRightKanExtensionAt_iff_of_iso Q F
      (Q.objObjPreimageIso Y)).1 (h (Q.objPreimage Y)).1
  apply Functor.PreservesRightKanExtension.mk' H F Q
  intro E hE
  have : E.left.IsRightKanExtension E.hom := ⟨⟨hE⟩⟩
  let hp := Functor.isPointwiseRightKanExtensionOfIsRightKanExtension E.left E.hom
  refine ⟨Functor.RightExtension.IsPointwiseRightKanExtension.isUniversal ?_⟩
  intro Y
  have : PreservesLimit (StructuredArrow.proj (Q.obj (Q.objPreimage Y)) Q ⋙ F) H :=
    (h (Q.objPreimage Y)).2
  exact Functor.RightExtension.isPointwiseRightKanExtensionAtOfIso'
    ((Functor.RightExtension.postcompose₂ Q F H).obj E)
    ((hp _).postcompose H) (Q.objObjPreimageIso Y)

private theorem ind_absolute
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {E : Type*} [Category* E] {T : Type*} [Category* T]
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
    (Q : C ⥤ D) [Q.IsLocalization W] (F : C ⥤ E) (H : E ⥤ T)
    (hc : ∀ X, ∃ Y, IsEssentiallyConstantIndDiagram
      (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F) Y) :
    H.PreservesLeftKanExtension F Q := by
  classical
  have h (X : C) := ind_preserves_at W Q F H X (hc X)
  have : Q.EssSurj := Localization.essSurj Q W
  have : Q.HasPointwiseLeftKanExtension F := fun Y ↦
    (Functor.hasPointwiseLeftKanExtensionAt_iff_of_iso Q F
      (Q.objObjPreimageIso Y)).1 (h (Q.objPreimage Y)).1
  apply Functor.PreservesLeftKanExtension.mk' H F Q
  intro E hE
  have : E.right.IsLeftKanExtension E.hom := ⟨⟨hE⟩⟩
  let hp := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension E.right E.hom
  refine ⟨Functor.LeftExtension.IsPointwiseLeftKanExtension.isUniversal ?_⟩
  intro Y
  have : PreservesColimit (CostructuredArrow.proj Q (Q.obj (Q.objPreimage Y)) ⋙ F) H :=
    (h (Q.objPreimage Y)).2
  exact Functor.LeftExtension.isPointwiseLeftKanExtensionAtOfIso'
    ((Functor.LeftExtension.postcompose₂ Q F H).obj E)
    ((hp _).postcompose H) (Q.objObjPreimageIso Y)

/-- The pointwise pre-derived Hom equivalences assemble to a compatible adjunction
provided the two systems are essentially constant and the supplied comparison maps
are derived-functor comparisons.
Source: Stacks Project, Derived Categories, Lemma 09T5 from Lemma 0DVC.
(auxiliary; not a blueprint node)

Apply the pre-derived adjunction theorem at every pair of complexes and use its
bifunctoriality to obtain the natural Hom equivalence. The essential-constancy
hypotheses and the derived-functor comparison properties identify the supplied
maps with the canonical maps, giving the displayed representative formula. -/
theorem exists_derived_adjunction_compatibility
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive] (adj : G ⊣ F)
    (hR : ∀ K : HomotopyCategory A (ComplexShape.up ℤ),
      let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
      let D := MorphismProperty.Under.forget W ⊤ K ⋙ Under.forget K ⋙
        F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
      ∃ X : DerivedCategory B, IsEssentiallyConstantIndDiagram D X)
    (hL : ∀ M : HomotopyCategory B (ComplexShape.up ℤ),
      let W := HomotopyCategory.quasiIso B (ComplexShape.up ℤ)
      let D := MorphismProperty.Over.forget W ⊤ M ⋙ Over.forget M ⋙
        G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
      ∃ X : DerivedCategory A, IsEssentiallyConstantProDiagram D X)
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (LG : DerivedCategory B ⥤ DerivedCategory A)
    (β : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (α : DerivedCategory.Qh ⋙ LG ⟶
      G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hRF : RF.IsRightDerivedFunctor β (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hLG : LG.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))) :
    ∃ d : LG ⊣ RF,
      ∀ (M : HomotopyCategory B (ComplexShape.up ℤ))
        (K : HomotopyCategory A (ComplexShape.up ℤ))
        (f : (G.mapHomotopyCategory (ComplexShape.up ℤ)).obj M ⟶ K),
        d.homEquiv (DerivedCategory.Qh.obj M) (DerivedCategory.Qh.obj K)
            (α.app M ≫ DerivedCategory.Qh.map f) =
          DerivedCategory.Qh.map ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).homEquiv M K f)
            ≫ β.app K := by
  classical
  let WA := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  let WB := HomotopyCategory.quasiIso B (ComplexShape.up ℤ)
  let QA := DerivedCategory.Qh (C := A)
  let QB := DerivedCategory.Qh (C := B)
  let Fh := F.mapHomotopyCategory (ComplexShape.up ℤ)
  let Gh := G.mapHomotopyCategory (ComplexShape.up ℤ)
  let ah := adj.mapHomotopyCategory (ComplexShape.up ℤ)
  let := hRF
  let := hLG
  have : RF.PreservesRightKanExtension (Gh ⋙ QA) QB := pro_absolute WB QB (Gh ⋙ QA) RF hL
  have : LG.PreservesLeftKanExtension (Fh ⋙ QB) QA := ind_absolute WA QA (Fh ⋙ QB) LG hR
  have : LG.IsRightKanExtension α := hLG.isRightKanExtension
  have : RF.IsLeftKanExtension β := hRF.isLeftKanExtension
  have : (LG ⋙ RF).IsLeftDerivedFunctor
      ((Functor.associator QB LG RF).inv ≫ Functor.whiskerRight α RF) WB := ⟨inferInstance⟩
  have : (RF ⋙ LG).IsRightDerivedFunctor
      (Functor.whiskerRight β LG ≫ (Functor.associator QA RF LG).hom) WA := ⟨inferInstance⟩
  let d := ah.derived WB WA α β
  refine ⟨d, ?_⟩
  intro M K f
  change d.unit.app (QB.obj M) ≫ RF.map (α.app M ≫ QA.map f) = _
  rw [RF.map_comp, ← Category.assoc]
  have hη := ah.derivedη_fac_app WB α β M
  change d.unit.app (QB.obj M) ≫ RF.map (α.app M) = _ at hη
  rw [hη, Category.assoc]
  have hn := β.naturality f
  change QB.map (Fh.map f) ≫ β.app K = β.app (Gh.obj M) ≫ RF.map (QA.map f) at hn
  rw [← hn, ← QB.map_comp_assoc]
  rfl

end
