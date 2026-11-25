/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement
import Mathlib.Data.Int.Init
import Mathlib.CategoryTheory.InducedCategory

/-! # Extension of invertible translations to twisted presheaves

Source: original twisted-site step 3, motivated by Stacks Tag 00W0.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits Opposite Functor

namespace CategoryTheory.TwistedActionRingedSite

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (s : C ≌ C) [s.functor.IsContinuous J J] [s.inverse.IsContinuous J J]
    (R : Sheaf J CommRingCat.{u})
    (a : (s.inverse.sheafPushforwardContinuous CommRingCat.{u} J J).obj R ≅ R)

-- Unit laws of the chosen power comparisons come from the site identity laws.
omit [s.functor.IsContinuous J J] in
private theorem powerComp_zero (S : Site J s R a) (n : ℤ) (X : C) :
    (S.powerComp n 0).hom.app X =
      eqToHom (congrArg (fun t : ℤ ↦ (s ^ t).functor.obj X) (add_zero n).symm) := by
  let := S.category
  have h := S.arrows_comp ((s ^ n).functor.obj X) X X n 0 (𝟙 _) (𝟙 _)
  rw [← S.arrows_id X, Equiv.symm_apply_apply, Category.comp_id,
    Equiv.apply_symm_apply] at h
  simp only [Functor.map_id, Category.id_comp] at h
  exact eq_of_heq ((Sigma.mk.inj h).2.symm.trans (eqToHom_heq_id_dom _ _ _).symm)

omit [s.functor.IsContinuous J J] in
private theorem powerComp_zero_left (S : Site J s R a) (n : ℤ) (X : C) :
    (S.powerComp 0 n).hom.app X =
      eqToHom (congrArg (fun t : ℤ ↦ (s ^ t).functor.obj X) (zero_add n).symm) := by
  let := S.category
  have h := S.arrows_comp ((s ^ n).functor.obj X) ((s ^ n).functor.obj X) X
    0 n (𝟙 _) (𝟙 _)
  rw [← S.arrows_id ((s ^ n).functor.obj X), Equiv.symm_apply_apply,
    Category.id_comp, Equiv.apply_symm_apply] at h
  simp only [Functor.map_id, Category.id_comp] at h
  exact eq_of_heq ((Sigma.mk.inj h).2.symm.trans (eqToHom_heq_id_dom _ _ _).symm)

-- Associativity of pure power arrows supplies the pentagon.
omit [s.functor.IsContinuous J J] in
private theorem powerComp_assoc (S : Site J s R a) (n m k : ℤ) (X : C) :
    (s ^ n).functor.map ((S.powerComp m k).hom.app X) ≫
        (S.powerComp n (m + k)).hom.app X =
      (S.powerComp n m).hom.app ((s ^ k).functor.obj X) ≫
        (S.powerComp (n + m) k).hom.app X ≫
          eqToHom (congrArg (fun t : ℤ ↦ (s ^ t).functor.obj X) (add_assoc n m k)) := by
  let := S.category
  let A := (s ^ n).functor.obj ((s ^ m).functor.obj ((s ^ k).functor.obj X))
  let B := (s ^ m).functor.obj ((s ^ k).functor.obj X)
  let D := (s ^ k).functor.obj X
  let f := (S.arrows A B).symm ⟨n, 𝟙 _⟩
  let g := (S.arrows B D).symm ⟨m, 𝟙 _⟩
  let h := (S.arrows D X).symm ⟨k, 𝟙 _⟩
  have hfg : f ≫ g =
      (S.arrows A D).symm ⟨n + m, (S.powerComp n m).hom.app D⟩ := by
    apply (S.arrows A D).injective
    simp [f, g, S.arrows_comp]
  have hgh : g ≫ h =
      (S.arrows B X).symm ⟨m + k, (S.powerComp m k).hom.app X⟩ := by
    apply (S.arrows B X).injective
    simp [g, h, S.arrows_comp]
  have hh := congrArg (S.arrows A X) (Category.assoc f g h)
  rw [hfg, hgh] at hh
  simp only [f, h, S.arrows_comp, Functor.map_id, Category.id_comp] at hh
  have he := (Sigma.mk.inj hh).2
  have hc := (conj_eqToHom_iff_heq'
    ((s ^ n).functor.map ((S.powerComp m k).hom.app X) ≫
      (S.powerComp n (m + k)).hom.app X)
    ((S.powerComp n m).hom.app ((s ^ k).functor.obj X) ≫
      (S.powerComp (n + m) k).hom.app X)
    rfl (congrArg (fun t : ℤ ↦ (s ^ t).functor.obj X) (add_assoc n m k))).2 he.symm
  simpa only [eqToHom_refl, Category.id_comp, Category.assoc] using hc

private def powerComparison (S : Site J s R a) (n m k : ℤ) (h : n + m = k) :
    (s ^ m).functor ⋙ (s ^ n).functor ≅ (s ^ k).functor :=
  S.powerComp n m ≪≫ eqToIso (congrArg (fun t : ℤ ↦ (s ^ t).functor) h)

omit [s.functor.IsContinuous J J] in
private theorem powerComparison_zero (S : Site J s R a) (n : ℤ) :
    powerComparison J s R a S n 0 n (add_zero n) = Iso.refl (s ^ n).functor := by
  apply Iso.ext
  ext X
  simp [powerComparison, powerComp_zero]

omit [s.functor.IsContinuous J J] in
private theorem powerComparison_zero_left (S : Site J s R a) (n : ℤ) :
    powerComparison J s R a S 0 n n (zero_add n) = Iso.refl (s ^ n).functor := by
  apply Iso.ext
  ext X
  simp [powerComparison, powerComp_zero_left]

omit [s.functor.IsContinuous J J] in
private theorem powerComparison_assoc (S : Site J s R a) (n m k a' b t : ℤ)
    (ha : n + m = a') (hb : m + k = b) (ht : a' + k = t) (ht' : n + b = t) :
    isoWhiskerLeft (s ^ k).functor (powerComparison J s R a S n m a' ha) ≪≫
        powerComparison J s R a S a' k t ht =
      isoWhiskerRight (powerComparison J s R a S m k b hb) (s ^ n).functor ≪≫
        powerComparison J s R a S n b t ht' := by
  subst a'
  subst b
  rcases ht' with rfl
  apply Iso.ext
  ext X
  simpa [powerComparison, Category.assoc] using (powerComp_assoc J s R a S n m k X).symm

private abbrev presheafPower (F : Cᵒᵖ ⥤ Type u) (n : ℤ) : Cᵒᵖ ⥤ Type u :=
  (s ^ n).functor.op ⋙ F

-- Use the specified comparisons, with explicit source and target integer labels.
private def presheafStep (S : Site J s R a) (F : Cᵒᵖ ⥤ Type u)
    (τ : s.inverse.op ⋙ F ≅ F) (n k : ℤ) (h : n - 1 = k) :
    presheafPower s F n ≅ presheafPower s F k := by
  let t : (s ^ (-1 : ℤ)).functor.op ⋙ F ≅ F := by
    simpa only [Equivalence.pow_neg_one, Equivalence.symm] using τ
  exact isoWhiskerLeft (s ^ n).functor.op t.symm ≪≫
    isoWhiskerRight (NatIso.op (powerComparison J s R a S (-1) n k (by omega)).symm) F

private def presheafMultiply (S : Site J s R a) (F : Cᵒᵖ ⥤ Type u)
    (n m k : ℤ) (h : n + m = k) :
    (s ^ m).functor.op ⋙ presheafPower s F n ≅ presheafPower s F k :=
  isoWhiskerRight (NatIso.op (powerComparison J s R a S n m k h).symm) F

omit [s.functor.IsContinuous J J] in
private theorem presheafStep_comp (S : Site J s R a) (F : Cᵒᵖ ⥤ Type u)
    (τ : s.inverse.op ⋙ F ≅ F) (n n' m k k' : ℤ)
    (hn : n - 1 = n') (h : n + m = k) (hk : k - 1 = k') :
    presheafMultiply J s R a S F n m k h ≪≫ presheafStep J s R a S F τ k k' hk =
      isoWhiskerLeft (s ^ m).functor.op (presheafStep J s R a S F τ n n' hn) ≪≫
        presheafMultiply J s R a S F n' m k' (by omega) := by
  let t : (s ^ (-1 : ℤ)).functor.op ⋙ F ≅ F := by
    simpa only [Equivalence.pow_neg_one, Equivalence.symm] using τ
  have hp := powerComparison_assoc J s R a S (-1) n m n' k k'
    (by omega) h (by omega) (by omega)
  have hp' := congrArg (fun i ↦ isoWhiskerRight (NatIso.op i.symm) F) hp
  simp only [Iso.trans_symm, NatIso.op_trans, isoWhiskerRight_trans,
    isoWhiskerLeft_symm, isoWhiskerRight_symm] at hp'
  change
    isoWhiskerLeft (s ^ m).functor.op
        (isoWhiskerRight
          (NatIso.op (powerComparison J s R a S (-1) n n' (by omega)).symm) F) ≪≫
      presheafMultiply J s R a S F n' m k' (by omega) =
    isoWhiskerRight (NatIso.op (powerComparison J s R a S n m k h).symm)
        ((s ^ (-1 : ℤ)).functor.op ⋙ F) ≪≫
      isoWhiskerRight
        (NatIso.op (powerComparison J s R a S (-1) k k' (by omega)).symm) F at hp'
  change presheafMultiply J s R a S F n m k h ≪≫
      (isoWhiskerLeft (s ^ k).functor.op t.symm ≪≫
        isoWhiskerRight
          (NatIso.op (powerComparison J s R a S (-1) k k' (by omega)).symm) F) = _
  dsimp only [presheafMultiply]
  rw [← Iso.trans_assoc,
    ← isoWhiskerLeft_trans_isoWhiskerRight
      (NatIso.op (powerComparison J s R a S n m k h).symm) t.symm]
  simp only [Iso.trans_assoc]
  rw [← hp']
  rfl

private def presheafIterate (S : Site J s R a) (F : Cᵒᵖ ⥤ Type u)
    (τ : s.inverse.op ⋙ F ≅ F) (n : ℤ) : F ≅ presheafPower s F n :=
  Int.inductionOn' n 0 (Iso.refl F)
    (fun k _ e ↦ e ≪≫ (presheafStep J s R a S F τ (k + 1) k (by omega)).symm)
    (fun k _ e ↦ e ≪≫ presheafStep J s R a S F τ k (k - 1) rfl)

omit [s.functor.IsContinuous J J] in
private theorem presheafIterate_zero (S : Site J s R a) (F : Cᵒᵖ ⥤ Type u)
    (τ : s.inverse.op ⋙ F ≅ F) : presheafIterate J s R a S F τ 0 = Iso.refl F := by
  exact Int.inductionOn'_self ..

omit [s.functor.IsContinuous J J] in
private theorem presheafIterate_pred (S : Site J s R a) (F : Cᵒᵖ ⥤ Type u)
    (τ : s.inverse.op ⋙ F ≅ F) (n k : ℤ) (h : n - 1 = k) :
    presheafIterate J s R a S F τ k =
      presheafIterate J s R a S F τ n ≪≫ presheafStep J s R a S F τ n k h := by
  subst k
  by_cases hn : n ≤ 0
  · unfold presheafIterate
    rw [Int.inductionOn'_sub_one hn]
  · have hn' : 0 ≤ n - 1 := by omega
    have hs := Int.inductionOn'_add_one
      (motive := fun k ↦ F ≅ presheafPower s F k) (z := n - 1) (b := 0)
      (zero := Iso.refl F)
      (succ := fun k _ e ↦ e ≪≫ (presheafStep J s R a S F τ (k + 1) k (by omega)).symm)
      (pred := fun k _ e ↦ e ≪≫ presheafStep J s R a S F τ k (k - 1) rfl) hn'
    rw! [sub_add_cancel] at hs
    change presheafIterate J s R a S F τ n =
      presheafIterate J s R a S F τ (n - 1) ≪≫
        (presheafStep J s R a S F τ n (n - 1) rfl).symm at hs
    rw [hs]
    simp

omit [s.functor.IsContinuous J J] in
private theorem presheafIterate_neg_one (S : Site J s R a) (F : Cᵒᵖ ⥤ Type u)
    (τ : s.inverse.op ⋙ F ≅ F) : presheafIterate J s R a S F τ (-1) = τ.symm := by
  rw [presheafIterate_pred J s R a S F τ 0 (-1) rfl, presheafIterate_zero]
  apply Iso.ext
  ext X x
  simp [presheafStep, powerComparison_zero, isoWhiskerLeft, isoWhiskerRight,
    NatIso.op, Functor.op]

-- Multiplicativity follows in both integer directions from the same one-step identity.
omit [s.functor.IsContinuous J J] in
private theorem presheafIterate_mul (S : Site J s R a) (F : Cᵒᵖ ⥤ Type u)
    (τ : s.inverse.op ⋙ F ≅ F) (n : ℤ) :
    ∀ (m k : ℤ) (h : n + m = k),
      presheafIterate J s R a S F τ k = presheafIterate J s R a S F τ m ≪≫
        isoWhiskerLeft (s ^ m).functor.op (presheafIterate J s R a S F τ n) ≪≫
          presheafMultiply J s R a S F n m k h := by
  induction n using Int.induction_on with
  | zero =>
    intro m k h
    rcases (show k = m by omega) with rfl
    simp only [presheafIterate_zero]
    apply Iso.ext
    ext X x
    simp [presheafMultiply, powerComparison_zero_left]
  | succ n ih =>
    intro m k h
    have hi := ih m (k - 1) (by omega)
    have hr := presheafIterate_pred J s R a S F τ ((n : ℤ) + 1) n (by omega)
    have hk := presheafIterate_pred J s R a S F τ k (k - 1) rfl
    rw [hr, hk] at hi
    have hc := presheafStep_comp J s R a S F τ ((n : ℤ) + 1) n m k (k - 1)
      (by omega) h rfl
    rw [isoWhiskerLeft_trans] at hi
    simp only [Iso.trans_assoc] at hi
    rw [← hc] at hi
    apply Iso.ext
    apply (cancel_mono (presheafStep J s R a S F τ k (k - 1) rfl).hom).mp
    exact congrArg Iso.hom hi
  | pred n ih =>
    intro m k h
    have hi := ih m (k + 1) (by omega)
    have hk := presheafIterate_pred J s R a S F τ (k + 1) k (by omega)
    rw [hk, hi]
    simp only [Iso.trans_assoc]
    rw [presheafStep_comp J s R a S F τ (-↑n) (-↑n - 1) m (k + 1) k
      rfl (by omega) (by omega)]
    rw [presheafIterate_pred J s R a S F τ (-↑n) (-↑n - 1) rfl, isoWhiskerLeft_trans]
    simp only [Iso.trans_assoc]

omit [s.functor.IsContinuous J J] in
private theorem presheafIterate_comp (S : Site J s R a) (F : Cᵒᵖ ⥤ Type u)
    (τ : s.inverse.op ⋙ F ≅ F) (n m : ℤ) (X : C) :
    (presheafIterate J s R a S F τ (n + m)).hom.app (op X) ≫
        F.map ((S.powerComp n m).hom.app X).op =
      (presheafIterate J s R a S F τ m).hom.app (op X) ≫
        (presheafIterate J s R a S F τ n).hom.app (op ((s ^ m).functor.obj X)) := by
  rw [presheafIterate_mul J s R a S F τ n m (n + m) rfl]
  simp [presheafMultiply, powerComparison, Category.assoc, ← F.map_comp, ← op_comp]

-- Restriction along a labelled arrow: translate, then apply the base restriction.
private def labelMap (S : Site J s R a) (F : Cᵒᵖ ⥤ Type u)
    (τ : s.inverse.op ⋙ F ≅ F) :
    letI := S.category
    ∀ {X Y : C}, (S.inclusion.obj X ⟶ S.inclusion.obj Y) →
      (F.obj (op Y) ⟶ F.obj (op X)) := by
  letI := S.category
  intro X Y f
  let p := S.arrows X Y f
  exact (presheafIterate J s R a S F τ p.1).hom.app (op Y) ≫ F.map p.2.op

omit [s.functor.IsContinuous J J] in
private theorem labelMap_id (S : Site J s R a) (F : Cᵒᵖ ⥤ Type u)
    (τ : s.inverse.op ⋙ F ≅ F) (X : C) :
    letI := S.category
    labelMap J s R a S F τ (𝟙 (S.inclusion.obj X)) = 𝟙 _ := by
  let := S.category
  dsimp only [labelMap]
  rw [S.arrows_id]
  simp [presheafIterate_zero]

omit [s.functor.IsContinuous J J] in
private theorem labelMap_inclusion (S : Site J s R a) (F : Cᵒᵖ ⥤ Type u)
    (τ : s.inverse.op ⋙ F ≅ F) {X Y : C} (f : X ⟶ Y) :
    letI := S.category
    labelMap J s R a S F τ (S.inclusion.map f) = F.map f.op := by
  let := S.category
  dsimp only [labelMap]
  rw [S.arrows_inclusion]
  simp [presheafIterate_zero]

omit [s.functor.IsContinuous J J] in
private theorem labelMap_comp (S : Site J s R a) (F : Cᵒᵖ ⥤ Type u)
    (τ : s.inverse.op ⋙ F ≅ F) :
    letI := S.category
    ∀ {X Y Z : C} (f : S.inclusion.obj X ⟶ S.inclusion.obj Y)
      (g : S.inclusion.obj Y ⟶ S.inclusion.obj Z),
    labelMap J s R a S F τ (f ≫ g) =
      labelMap J s R a S F τ g ≫ labelMap J s R a S F τ f := by
  let := S.category
  intro X Y Z f g
  obtain ⟨⟨n, f⟩, rfl⟩ := (S.arrows X Y).symm.surjective f
  obtain ⟨⟨m, g⟩, rfl⟩ := (S.arrows Y Z).symm.surjective g
  dsimp only [labelMap]
  rw [S.arrows_comp]
  rw! [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rw [op_comp, op_comp, F.map_comp, F.map_comp]
  simp only [← Category.assoc]
  rw [presheafIterate_comp]
  simp only [Category.assoc]
  congr 1
  have hn := (presheafIterate J s R a S F τ n).hom.naturality g.op
  dsimp at hn
  rw [← Category.assoc, ← hn, Category.assoc]

omit [s.functor.IsContinuous J J] in
private theorem labelMap_generator (S : Site J s R a) (F : Cᵒᵖ ⥤ Type u)
    (τ : s.inverse.op ⋙ F ≅ F) (X : C) :
    letI := S.category
    labelMap J s R a S F τ
        ((S.arrows (s.inverse.obj X) X).symm ⟨-1, 𝟙 _⟩) = τ.inv.app (op X) := by
  let := S.category
  dsimp only [labelMap]
  rw [Equiv.apply_symm_apply]
  simp [presheafIterate_neg_one]

/-- An invertible presheaf translation extends to the integer-labelled category.

Source: the presheaf-extension part of original step 3 of the agent twisted variant
of Stacks Tag 00W0, `sites.tex`, proposition-sheaves-on-group
(blueprint: lem-sf-twisted-action-presheaf-extension).

Proof: assign F(X) to the copied object X. Give a minus-one generator the restriction
map τ.inv at X. For an arrow labelled n, first restrict along its base arrow and
then along n generators. For negative n use successive τ.inv components; for
positive n use τ and the unit and counit of s to change the base objects. Insert
the displayed power comparisons when reassociating iterates. Apply the arrow
bijection to associativity of three pure power arrows to obtain the pentagon for
these comparisons, and to the identity laws to obtain their unit relations.
Naturality of τ moves each base restriction past a generator. Cancelling adjacent
opposite generators uses τ.hom_inv_id and τ.inv_hom_id. Induction in both integer
directions therefore gives the presheaf identity and composition laws. On degree
zero the resulting presheaf is F, up to the object-copy identification, so these
identifications give c. Its minus-one formula is the initial assignment of τ.inv.
No topology or gluing assertion is used. The construction applies to an empty C,
an empty value F(X), and the identity autoequivalence. -/
theorem twistedPresheafExtension (S : Site J s R a) (F : Cᵒᵖ ⥤ Type u)
    (τ : s.inverse.op ⋙ F ≅ F) :
    letI := S.category
    ∃ (G : (Object C)ᵒᵖ ⥤ Type u) (c : S.inclusion.op ⋙ G ≅ F),
      ∀ X : C,
        G.map ((S.arrows (s.inverse.obj X) X).symm ⟨-1, 𝟙 _⟩).op ≫
            c.hom.app (op (s.inverse.obj X)) =
          c.hom.app (op X) ≫ τ.inv.app (op X) := by
  have _hforward : s.functor.IsContinuous J J := inferInstance
  let := S.category
  let D := InducedCategory (Object C) S.inclusion.obj
  let L : D ⥤ Object C := inducedFunctor S.inclusion.obj
  have : L.EssSurj := L.essSurj_of_surj (by
    intro X
    exact ⟨X.base, S.inclusion_obj X.base⟩)
  let : L.IsEquivalence := {}
  let e : D ≌ Object C := L.asEquivalence
  let H : Dᵒᵖ ⥤ Type u :=
    { obj := fun X ↦ F.obj (op X.unop)
      map := fun f ↦ labelMap J s R a S F τ f.unop.hom
      map_id := fun X ↦ labelMap_id J s R a S F τ X.unop
      map_comp := fun f g ↦ labelMap_comp J s R a S F τ g.unop.hom f.unop.hom }
  let j : C ⥤ D :=
    { obj := fun X ↦ X
      map := fun f ↦ InducedCategory.homMk (S.inclusion.map f)
      map_id := fun X ↦ by ext; exact S.inclusion.map_id X
      map_comp := fun f g ↦ by ext; exact S.inclusion.map_comp f g }
  let b : j.op ⋙ H ≅ F := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    dsimp only [Functor.comp_map, Functor.op_map, j, H]
    simpa using labelMap_inclusion J s R a S F τ f.unop)
  let G := e.inverse.op ⋙ H
  let d : e.functor.op ⋙ G ≅ H := e.op.funInvIdAssoc H
  have hi : j ⋙ e.functor = S.inclusion := by
    rfl
  let c : S.inclusion.op ⋙ G ≅ F :=
    eqToIso (show S.inclusion.op ⋙ G = j.op ⋙ (e.functor.op ⋙ G) by
      exact (congrArg (fun K : C ⥤ Object C ↦ K.op ⋙ G) hi).symm) ≪≫ isoWhiskerLeft j.op d ≪≫ b
  refine ⟨G, c, ?_⟩
  intro X
  let γ : j.obj (s.inverse.obj X) ⟶ j.obj X :=
    InducedCategory.homMk ((S.arrows (s.inverse.obj X) X).symm ⟨-1, 𝟙 _⟩)
  have hd := d.hom.naturality γ.op
  have hg : H.map γ.op = τ.inv.app (op X) := labelMap_generator J s R a S F τ X
  change G.map ((S.arrows (s.inverse.obj X) X).symm ⟨-1, 𝟙 _⟩).op ≫
      d.hom.app (op (j.obj (s.inverse.obj X))) =
    d.hom.app (op (j.obj X)) ≫ τ.inv.app (op X)
  change G.map ((S.arrows (s.inverse.obj X) X).symm ⟨-1, 𝟙 _⟩).op ≫
      d.hom.app (op (j.obj (s.inverse.obj X))) =
    d.hom.app (op (j.obj X)) ≫ H.map γ.op at hd
  rw [hg] at hd
  exact hd

end CategoryTheory.TwistedActionRingedSite
