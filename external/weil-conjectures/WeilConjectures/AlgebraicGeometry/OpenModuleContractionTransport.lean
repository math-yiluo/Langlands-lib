/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-! # Transport of a module contraction on an open subscheme

Source: Stacks Project, Tags 08DL, 08DQ and 03EO; the sectionwise
open-site reindexing construction of `Scheme.Modules.overEquiv`.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace SheafOfModules
attribute [local instance] monoidalCategory symmetricCategory
variable {C : Type u} [Category.{u} C] [Quiver.IsThin C]
  {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})
set_option quotPrecheck false in
set_option hygiene false in
local notation "Q" => (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
set_option quotPrecheck false in
set_option hygiene false in
local notation "Mod" => SheafOfModules.{u} Q

-- Free representables provide local sections and embed in the unit on a thin site.
private abbrev freeAt (V : C) : PresheafOfModules.{u} (Q).obj :=
  PresheafOfModules.freeObj (yoneda.obj V)

private def freeAtDesc (V : C) (B : Mod) (b : B.val.obj (op V)) :
    freeAt R V ⟶ B.val :=
  PresheafOfModules.freeObjDesc (yonedaEquiv.symm b)

private theorem freeDesc_one_injective {S : Type u} [CommRing S]
    {I : Type u} [Subsingleton I] :
    Function.Injective (ModuleCat.freeDesc
      (M := ModuleCat.of S S) (↾fun _ : I ↦ (1 : S))) := by
  classical
  intro x y hxy
  change I →₀ S at x y
  by_cases hh : Nonempty I
  · obtain ⟨i⟩ := hh
    have hv (z : I →₀ S) :
        ModuleCat.freeDesc (M := ModuleCat.of S S) (↾fun _ : I ↦ (1 : S)) z = z i := by
      have hz : z = Finsupp.single i (z i) := by
        ext j
        have hj : j = i := Subsingleton.elim _ _
        subst j
        simp
      rw [hz]
      change Finsupp.lift S S I (fun _ : I ↦ (1 : S))
        (Finsupp.single i (z i)) = (Finsupp.single i (z i)) i
      simp [Finsupp.lift_apply]
    rw [hv x, hv y] at hxy
    apply Finsupp.ext
    intro j
    have hj : j = i := Subsingleton.elim _ _
    subst j
    exact hxy
  · apply Finsupp.ext
    intro i
    exact (hh ⟨i⟩).elim

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}] in
private theorem freeAtDesc_mono (V : C) :
    Mono (freeAtDesc R V (unit Q) (1 : R.obj.obj (op V))) := by
  apply PresheafOfModules.mono_of_injective
  intro W
  have he : (freeAtDesc R V (unit Q) (1 : R.obj.obj (op V))).app W =
      ModuleCat.freeDesc (M := ModuleCat.of (R.obj.obj W) (R.obj.obj W))
        (↾fun _ : W.unop ⟶ V ↦ (1 : R.obj.obj W)) := by
    change ModuleCat.freeDesc (((yonedaEquiv
      (F := (unit Q).val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat)).symm
        (1 : R.obj.obj (op V))).app W) = _
    congr 1
    ext h
    change R.obj.map h.op (1 : R.obj.obj (op V)) = 1
    exact map_one _
  rw [he]
  exact freeDesc_one_injective

private theorem local_section_subobject_unit (V : C) (B : Mod) (b : B.val.obj (op V)) :
    ∃ (G : Mod) (d : G ⟶ unit Q) (_ : Mono d) (p : G ⟶ B)
      (s : G.val.obj (op V)), p.val.app (op V) s = b := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (Q).obj)
  let P := freeAt R V
  let S := PresheafOfModules.sheafification (𝟙 (Q).obj)
  let G := S.obj P
  let d₀ := freeAtDesc R V (unit Q) (1 : R.obj.obj (op V))
  let p₀ := freeAtDesc R V B b
  let d : G ⟶ unit Q := S.map d₀ ≫ adj.counit.app (unit Q)
  let p : G ⟶ B := (adj.homEquiv P B).symm p₀
  have : Mono d₀ := freeAtDesc_mono R V
  have : Mono d := inferInstance
  let s := (adj.unit.app P).app (op V)
    (ModuleCat.freeMk (𝟙 V) : P.obj (op V))
  refine ⟨G, d, inferInstance, p, s, ?_⟩
  have hp := (adj.homEquiv P B).apply_symm_apply p₀
  have h := congrArg
    (fun q : P ⟶ B.val ↦ q.app (op V) (ModuleCat.freeMk (𝟙 V))) hp
  change p.val.app (op V) s = _ at h
  refine h.trans ?_
  change ModuleCat.freeDesc (((yonedaEquiv
    (F := B.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat)).symm b).app (op V))
    (ModuleCat.freeMk (𝟙 V)) = b
  erw [ModuleCat.freeDesc_apply]
  change B.val.map (𝟙 V).op b = b
  rw [op_id, PresheafOfModules.map_id]
  rfl

-- Maps out of a sheaf tensor product are determined by the presheaf tensor.
private def tensorSection (A B : Mod) : A.val ⊗ B.val ⟶ (A ⊗ B).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (Q).obj)).unit.app (A.val ⊗ B.val) ≫
    (tensorObjIsoSheafification (R := R) A B).inv.val

omit [Quiver.IsThin C] in
private theorem tensorSection_natural {A B : Mod} (p : A ⟶ B) (T : Mod) :
    (p.val ▷ T.val) ≫ tensorSection R B T =
      tensorSection R A T ≫ (p ▷ T).val := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (Q).obj)
  have he : (tensorObjIsoSheafification (R := R) A T).inv ≫ (p ▷ T) =
      (PresheafOfModules.sheafification (𝟙 (Q).obj)).map (p.val ▷ T.val) ≫
        (tensorObjIsoSheafification (R := R) B T).inv := by
    apply (cancel_mono (tensorObjIsoSheafification (R := R) B T).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [whiskerRight_tensorObjIsoSheafification_hom]
    simp
  have hev := congrArg Hom.val he
  simp only [comp_val] at hev
  have hn := adj.unit.naturality (p.val ▷ T.val)
  change (p.val ▷ T.val) ≫ adj.unit.app (B.val ⊗ T.val) =
    adj.unit.app (A.val ⊗ T.val) ≫
      ((PresheafOfModules.sheafification (𝟙 (Q).obj)).map (p.val ▷ T.val)).val at hn
  change (p.val ▷ T.val) ≫
      (adj.unit.app (B.val ⊗ T.val) ≫ (tensorObjIsoSheafification (R := R) B T).inv.val) =
    (adj.unit.app (A.val ⊗ T.val) ≫ (tensorObjIsoSheafification (R := R) A T).inv.val) ≫
      (p ▷ T).val
  calc
    _ = ((p.val ▷ T.val) ≫ adj.unit.app (B.val ⊗ T.val)) ≫
        (tensorObjIsoSheafification (R := R) B T).inv.val := (Category.assoc ..).symm
    _ = (adj.unit.app (A.val ⊗ T.val) ≫
        ((PresheafOfModules.sheafification (𝟙 (Q).obj)).map (p.val ▷ T.val)).val) ≫
          (tensorObjIsoSheafification (R := R) B T).inv.val := by rw [hn]
    _ = _ := by rw [Category.assoc, ← hev, Category.assoc]

omit [Quiver.IsThin C] in
private theorem tensorSection_ext (A B N : Mod) (f g : A ⊗ B ⟶ N)
    (h : tensorSection R A B ≫ f.val = tensorSection R A B ≫ g.val) : f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (Q).obj)
  apply (cancel_epi (tensorObjIsoSheafification (R := R) A B).inv).1
  apply (adj.homEquiv _ N).injective
  exact h

-- Subobjects of the unit determine the whole natural family.
private theorem tensor_natTrans_ext (T : Mod) (H : Mod ⥤ Mod)
    [H.PreservesMonomorphisms] (f g : tensorRight T ⟶ H)
    (hu : f.app (unit Q) = g.app (unit Q)) : f = g := by
  apply NatTrans.ext
  funext B
  apply tensorSection_ext R B T (H.obj B)
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro b t
  obtain ⟨G, d, hd, p, s, hp⟩ := local_section_subobject_unit R W.unop B b
  have hg : f.app G = g.app G := by
    apply (cancel_mono (H.map d)).1
    rw [← f.naturality d, ← g.naturality d, hu]
  have hn : (p ▷ T) ≫ f.app B = (p ▷ T) ≫ g.app B := by
    change (tensorRight T).map p ≫ f.app B = (tensorRight T).map p ≫ g.app B
    rw [f.naturality, g.naturality, hg]
  have hnv := congrArg Hom.val hn
  simp only [comp_val] at hnv
  have ht : (p.val ▷ T.val) ≫ tensorSection R B T ≫ (f.app B).val =
      (p.val ▷ T.val) ≫ tensorSection R B T ≫ (g.app B).val := by
    calc
      _ = tensorSection R G T ≫ (p ▷ T).val ≫ (f.app B).val := by
        rw [← Category.assoc, tensorSection_natural, Category.assoc]
      _ = tensorSection R G T ≫ (p ▷ T).val ≫ (g.app B).val := by rw [hnv]
      _ = _ := by rw [← Category.assoc, ← tensorSection_natural, Category.assoc]
  have h := congrArg
    (fun q : G.val ⊗ T.val ⟶ (H.obj B).val ↦
      q.app W (s ⊗ₜ[R.obj.obj W] t)) ht
  change (f.app B).val.app W ((tensorSection R B T).app W
      (p.val.app W s ⊗ₜ[R.obj.obj W] t)) =
    (g.app B).val.app W ((tensorSection R B T).app W
      (p.val.app W s ⊗ₜ[R.obj.obj W] t)) at h
  rw [hp] at h
  exact h

omit [Quiver.IsThin C] in
private def contraction (A B V : Mod) (v : V ⟶ homObj (R := R) A (𝟙_ Mod)) :
    B ⊗ V ⟶ homObj (R := R) A B :=
  tensorHomEquiv A _ B
    ((β_ A (B ⊗ V)).hom ≫ (α_ B V A).hom ≫
      B ◁ ((β_ V A).hom ≫ (tensorHomEquiv A V (𝟙_ Mod)).symm v) ≫ (ρ_ B).hom)

omit [Quiver.IsThin C] in
private theorem contraction_output (A B V B' : Mod)
    (v : V ⟶ homObj (R := R) A (𝟙_ Mod)) (k : B ⟶ B') :
    tensorHomEquiv A _ B'
      ((β_ A (B ⊗ V)).hom ≫ (α_ B V A).hom ≫
        B ◁ ((β_ V A).hom ≫ (tensorHomEquiv A V (𝟙_ Mod)).symm v) ≫
          (ρ_ B).hom ≫ k) =
      contraction R A B V v ≫ homObjMap (R := R) (𝟙 A) k := by
  unfold contraction
  rw [← tensorHomEquiv_comp_homObjMap]
  congr 1

omit [Quiver.IsThin C] in
private theorem contraction_natural_target (A V : Mod)
    (v : V ⟶ homObj (R := R) A (𝟙_ Mod)) {B B' : Mod} (p : B ⟶ B') :
    (p ▷ V) ≫ contraction R A B' V v =
      contraction R A B V v ≫ homObjMap (R := R) (𝟙 A) p := by
  unfold contraction
  rw [← tensorHomEquiv_whiskerLeft_comp, ← tensorHomEquiv_comp_homObjMap]
  apply (tensorHomEquiv A _ B').congr_arg
  rw [BraidedCategory.braiding_naturality_right_assoc,
    associator_naturality_left_assoc, ← whisker_exchange_assoc, rightUnitor_naturality]
  simp only [Category.assoc]

omit [Quiver.IsThin C] in
private theorem uncurry_comp (A : Mod) {V W N : Mod}
    (h : W ⟶ V) (v : V ⟶ homObj (R := R) A N) :
    (tensorHomEquiv A W N).symm (h ≫ v) =
      A ◁ h ≫ (tensorHomEquiv A V N).symm v := by
  apply (tensorHomEquiv A W N).injective
  simp only [Equiv.apply_symm_apply, tensorHomEquiv_whiskerLeft_comp]

omit [Quiver.IsThin C] in
private theorem contraction_natural_input (A B : Mod) {V W : Mod}
    (h : W ⟶ V) (v : V ⟶ homObj (R := R) A (𝟙_ Mod)) :
    (B ◁ h) ≫ contraction R A B V v = contraction R A B W (h ≫ v) := by
  unfold contraction
  rw [← tensorHomEquiv_whiskerLeft_comp]
  apply (tensorHomEquiv A _ B).congr_arg
  rw [uncurry_comp, BraidedCategory.braiding_naturality_right_assoc,
    associator_naturality_middle_assoc, ← whiskerLeft_comp_assoc,
    BraidedCategory.braiding_naturality_left_assoc]

omit [Quiver.IsThin C] in
private theorem unit_contraction (A V : Mod)
    (v : V ⟶ homObj (R := R) A (𝟙_ Mod)) :
    contraction R A (𝟙_ Mod) V v = (λ_ V).hom ≫ v := by
  unfold contraction
  apply (tensorHomEquiv A _ (𝟙_ Mod)).symm.injective
  rw [Equiv.symm_apply_apply, uncurry_comp]
  rw [← unitors_equal, leftUnitor_naturality]
  rw [← Category.assoc, leftUnitor_tensor_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← BraidedCategory.braiding_naturality_right_assoc,
    SymmetricCategory.symmetry_assoc]

variable {D : Type u} [Category.{u} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  (S : Sheaf K CommRingCat.{u})
set_option quotPrecheck false in
set_option hygiene false in
local notation "ModD" => SheafOfModules.{u}
  ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)

-- Compare the two natural families after pulling back through the fully faithful functor.
set_option synthInstance.maxSize 128 in
private theorem contraction_core (L : Mod ⥤ ModD) [L.Full] [L.Faithful]
    (e : ∀ A B : Mod, L.obj (homObj (R := R) A B) ≅
      homObj (R := S) (L.obj A) (L.obj B))
    (he : ∀ (A A' B B' : Mod) (f : A' ⟶ A) (g : B ⟶ B'),
      L.map (homObjMap (R := R) f g) ≫ (e A' B').hom =
        (e A B).hom ≫ homObjMap (R := S) (L.map f) (L.map g))
    (m : L.CoreMonoidal) (A B V : Mod) (v : V ⟶ homObj (R := R) A (𝟙_ Mod)) :
    (m.μIso B V).hom ≫ L.map (contraction R A B V v) ≫ (e A B).hom =
      contraction S (L.obj A) (L.obj B) (L.obj V)
        (L.map v ≫ (e A (𝟙_ Mod)).hom ≫ homObjMap (R := S) (𝟙 (L.obj A)) m.εIso.inv)
    := by
  let H := (SheafOfModules.homFunctor R).obj (op A)
  let : H.IsRightAdjoint :=
    (SheafOfModules.tensorHomAdjunction R A).isRightAdjoint
  let w := L.map v ≫ (e A (𝟙_ (Mod))).hom ≫
    SheafOfModules.homObjMap (R := S) (𝟙 (L.obj A)) m.εIso.inv
  let f : tensorRight V ⟶ H :=
    { app := fun B ↦ SheafOfModules.contraction R A B V v
      naturality := fun _ _ p ↦
        SheafOfModules.contraction_natural_target R A V v p }
  have hμ {B B' : Mod} (p : B ⟶ B') :
      L.map (p ▷ V) ≫ (m.μIso B' V).inv =
        (m.μIso B V).inv ≫ (L.map p ▷ L.obj V) := by
    apply (cancel_mono (m.μIso B' V).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [m.μIso_hom_natural_left]
    simp
  have hei {B B' : Mod} (p : B ⟶ B') :
      (e A B).inv ≫ L.map (SheafOfModules.homObjMap (R := R) (𝟙 A) p) =
        SheafOfModules.homObjMap (R := S) (𝟙 (L.obj A)) (L.map p) ≫
          (e A B').inv := by
    apply (cancel_mono (e A B').hom).1
    have hn := he A A B B' (𝟙 A) p
    rw [L.map_id] at hn
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hn]
    simp
  let g : tensorRight V ⟶ H :=
    { app := fun B ↦ L.preimage ((m.μIso B V).inv ≫
        SheafOfModules.contraction S (L.obj A) (L.obj B) (L.obj V) w ≫
          (e A B).inv)
      naturality := by
        intro B B' p
        apply L.map_injective
        simp only [Functor.map_comp, Functor.map_preimage]
        change L.map (p ▷ V) ≫ (m.μIso B' V).inv ≫
            contraction S (L.obj A) (L.obj B') (L.obj V) w ≫ (e A B').inv =
          ((m.μIso B V).inv ≫ contraction S (L.obj A) (L.obj B) (L.obj V) w ≫
            (e A B).inv) ≫ L.map (homObjMap (R := R) (𝟙 A) p)
        rw [← Category.assoc (L.map (p ▷ V)), hμ]
        simp only [Category.assoc]
        rw [← Category.assoc (L.map p ▷ L.obj V),
          contraction_natural_target]
        simp only [Category.assoc]
        rw [← hei] }
  have hu : f.app (𝟙_ (Mod)) =
      g.app (𝟙_ (Mod)) := by
    apply L.map_injective
    dsimp only [f, g]
    rw [Functor.map_preimage]
    apply (cancel_epi (m.μIso (𝟙_ (Mod)) V).hom).1
    apply (cancel_mono (e A (𝟙_ (Mod))).hom).1
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
    have : IsIso (SheafOfModules.homObjMap (R := S)
        (𝟙 (L.obj A)) m.εIso.inv) :=
      inferInstanceAs (IsIso
        (((SheafOfModules.homFunctor S).obj (op (L.obj A))).map m.εIso.inv))
    apply (cancel_mono (SheafOfModules.homObjMap (R := S)
      (𝟙 (L.obj A)) m.εIso.inv)).1
    rw [← SheafOfModules.contraction_natural_target, SheafOfModules.unit_contraction,
      SheafOfModules.unit_contraction, Functor.map_comp]
    have hm : (m.μIso (𝟙_ (Mod)) V).hom ≫
        L.map (λ_ V).hom = m.εIso.inv ▷ L.obj V ≫ (λ_ (L.obj V)).hom := by
      apply (cancel_epi (m.εIso.hom ▷ L.obj V)).1
      rw [← Category.assoc, ← comp_whiskerRight_assoc, Iso.hom_inv_id,
        id_whiskerRight, Category.id_comp]
      exact (m.left_unitality V).symm
    dsimp only [w]
    simp only [Category.assoc]
    rw [← Category.assoc _ (L.map (λ_ V).hom), hm]
    simp only [Category.assoc]
  have hfg := SheafOfModules.tensor_natTrans_ext R V H f g hu
  have hb := congrArg L.map (NatTrans.congr_app hfg B)
  dsimp only [f, g] at hb
  rw [Functor.map_preimage] at hb
  rw [hb]
  simp only [w, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]

set_option synthInstance.maxSize 128 in
private theorem contraction_transport (L : Mod ⥤ ModD) [L.Full] [L.Faithful]
    (e : ∀ A B : Mod, L.obj (homObj (R := R) A B) ≅
      homObj (R := S) (L.obj A) (L.obj B))
    (he : ∀ (A A' B B' : Mod) (f : A' ⟶ A) (g : B ⟶ B'),
      L.map (homObjMap (R := R) f g) ≫ (e A' B').hom =
        (e A B).hom ≫ homObjMap (R := S) (L.map f) (L.map g))
    (m : L.CoreMonoidal) (i : (𝟙_ ModD) ≅ L.obj (𝟙_ Mod)) (hi : m.εIso = i)
    (A B V B' : Mod) (W : ModD) (h : W ⟶ L.obj V)
    (v : V ⟶ homObj (R := R) A (𝟙_ Mod)) (k : B ⟶ B')
    (v' : W ⟶ homObj (R := S) (L.obj A) (𝟙_ ModD)) (k' : L.obj B ⟶ L.obj B')
    (hv : h ≫ L.map v ≫ (e A (𝟙_ Mod)).hom ≫
      homObjMap (R := S) (𝟙 (L.obj A)) i.inv = v')
    (hk : L.map k = k') :
    (𝟙 (L.obj B) ⊗ₘ h) ≫ (m.μIso B V).hom ≫
      L.map (tensorHomEquiv (R := R) A _ _
        ((β_ A (B ⊗ V)).hom ≫ (α_ B V A).hom ≫
          B ◁ ((β_ V A).hom ≫ (tensorHomEquiv (R := R) A V (𝟙_ Mod)).symm v) ≫
            (ρ_ B).hom ≫ k)) ≫ (e A B').hom =
      tensorHomEquiv (R := S) (L.obj A) _ _
        ((β_ (L.obj A) (L.obj B ⊗ W)).hom ≫ (α_ (L.obj B) W (L.obj A)).hom ≫
          L.obj B ◁ ((β_ W (L.obj A)).hom ≫
            (tensorHomEquiv (R := S) (L.obj A) W (𝟙_ ModD)).symm v') ≫
              (ρ_ (L.obj B)).hom ≫ k') := by
  rw [contraction_output R, contraction_output S, id_tensorHom, L.map_comp]
  have hb := contraction_core R S L e he m A B V v
  rw [hi] at hb
  have hn := he A A B B' (𝟙 A) k
  rw [L.map_id, hk] at hn
  simp only [Category.assoc]
  rw [hn]
  have hc : (L.obj B ◁ h) ≫ (m.μIso B V).hom ≫
      L.map (contraction R A B V v) ≫ (e A B).hom =
      contraction S (L.obj A) (L.obj B) W v' := by
    rw [hb, contraction_natural_input S]
    simp only [hv]
  simpa only [Category.assoc] using congrArg
    (fun z ↦ z ≫ homObjMap (R := S) (𝟙 (L.obj A)) k') hc

end SheafOfModules

namespace AlgebraicGeometry
attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

private theorem openModuleOver_isThin (X : Scheme.{u}) (U : X.Opens) :
    Quiver.IsThin (Over U) := fun _ _ ↦ ⟨fun f g ↦ by
  ext
  exact Subsingleton.elim _ _⟩

attribute [local instance] openModuleOver_isThin

attribute [local irreducible] Scheme.Modules.overEquiv
attribute [local irreducible] SheafOfModules.tensorHomEquiv

-- Preserve the established names of the nondependent forall hypotheses.
set_option linter.unusedVariables false in
/-- Open-site transport of contraction by an arbitrary module-valued dual input.
Source: Stacks Project, Tags 08DL and 08DQ (restriction and evaluation),
and Tag 03EO (tensor-Hom adjunction).
(blueprint: lem-pc-open-module-contraction-transport).

Proof: on the thin localized open site, sheafify the free module on each
representable. Sending its generator to 1 embeds it in the tensor unit, since
representable section sets are empty or singletons and sheafification preserves
monomorphisms. Every local section of a module is the image of the distinguished
section of one of these subobjects. Consequently, natural transformations from
tensoring with V to a monomorphism-preserving functor are determined at the unit:
use naturality into the unit to compare on the subobjects, then naturality into
an arbitrary module and extensionality on local pure tensors.

Apply this to internal Hom from A, a right adjoint. Pull the target contraction
back through the inverse tensorator and inverse e, using fullness of L.
Naturality of e and the tensorator makes this a natural family in the output
module. At the unit both contractions are the left unitor followed by the dual
input; monoidal unit coherence proves their equality. The preceding determination
by the unit gives transport for every output module. Naturality in the dual input
and output, followed by hunit, hv and hk, gives the displayed equation.
All local section arguments include the zero ring and empty opens. -/
theorem openModule_contraction_transport (X : Scheme.{u}) (U : X.Opens) :
    let L := Equivalence.functor
      (C := localEvaluationModules X U)
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
    ∀ (e : ∀ A B : localEvaluationModules X U,
      L.obj (SheafOfModules.homObj (R := X.sheaf.over U) A B) ≅
        SheafOfModules.homObj (R := U.toScheme.sheaf) (L.obj A) (L.obj B))
    (he : ∀ (A A' B B' : localEvaluationModules X U) (f : A' ⟶ A) (g : B ⟶ B'),
      L.map (SheafOfModules.homObjMap (R := X.sheaf.over U) f g) ≫ (e A' B').hom =
        (e A B).hom ≫
          SheafOfModules.homObjMap (R := U.toScheme.sheaf) (L.map f) (L.map g))
    (m : L.CoreMonoidal)
    (hunit : m.εIso = Scheme.Modules.overEquivFunctorObjUnitIso U)
    (hsymm : ∀ A B : localEvaluationModules X U,
      L.map (β_ A B).hom ≫ (m.μIso B A).inv =
        (m.μIso A B).inv ≫ (β_ (L.obj A) (L.obj B)).hom)
    (A B V B' : localEvaluationModules X U)
    (W : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
    (h : W ⟶ L.obj V)
    (v : V ⟶ SheafOfModules.homObj (R := X.sheaf.over U) A
      (𝟙_ (localEvaluationModules X U))) (k : B ⟶ B')
    (v' : W ⟶ SheafOfModules.homObj (R := U.toScheme.sheaf) (L.obj A)
      (𝟙_ (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))))
    (k' : L.obj B ⟶ L.obj B')
    (hv : h ≫ L.map v ≫ (e A (𝟙_ (localEvaluationModules X U))).hom ≫
      SheafOfModules.homObjMap (R := U.toScheme.sheaf) (𝟙 (L.obj A))
        (Scheme.Modules.overEquivFunctorObjUnitIso U).inv = v')
    (hk : L.map k = k'),
    (𝟙 (L.obj B) ⊗ₘ h) ≫ (m.μIso B V).hom ≫
      L.map (SheafOfModules.tensorHomEquiv (R := X.sheaf.over U) A _ _
        ((β_ A (B ⊗ V)).hom ≫ (α_ B V A).hom ≫
          B ◁ ((β_ V A).hom ≫
            (SheafOfModules.tensorHomEquiv (R := X.sheaf.over U) A V
              (𝟙_ (localEvaluationModules X U))).symm v) ≫ (ρ_ B).hom ≫ k)) ≫
        (e A B').hom =
      SheafOfModules.tensorHomEquiv (R := U.toScheme.sheaf) (L.obj A) _ _
        ((β_ (L.obj A) (L.obj B ⊗ W)).hom ≫ (α_ (L.obj B) W (L.obj A)).hom ≫
          L.obj B ◁ ((β_ W (L.obj A)).hom ≫
            (SheafOfModules.tensorHomEquiv (R := U.toScheme.sheaf) (L.obj A) W
              (𝟙_ (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)))).symm
                v') ≫
          (ρ_ (L.obj B)).hom ≫ k') := by
  intro L e he m hunit _ A B V B' W h v k v' k' hv hk
  let : Quiver.IsThin (Over U) := openModuleOver_isThin X U
  let : L.Full := (Scheme.Modules.overEquiv U).full_functor
  let : L.Faithful := (Scheme.Modules.overEquiv U).faithful_functor
  have ht := SheafOfModules.contraction_transport
    (C := Over U) (J := (Opens.grothendieckTopology X).over U)
    (D := TopologicalSpace.Opens U.toScheme.toRingedSpace)
    (K := Opens.grothendieckTopology U.toScheme.toRingedSpace)
    (X.sheaf.over U) U.toScheme.toRingedSpace.sheaf L e he m
    (Scheme.Modules.overEquivFunctorObjUnitIso U) hunit A B V B' W h v k v' k' hv hk
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  convert ht using 1

end AlgebraicGeometry
