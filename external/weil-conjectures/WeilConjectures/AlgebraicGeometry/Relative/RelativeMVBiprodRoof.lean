/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps

/-! # Additive biproduct comparisons for localized row roofs -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry
/-- A roof whose three comparisons are diagonal decomposes into the two component roofs. -/
theorem relativeMV_roof_pair
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (R : D ⥤ C) [R.Additive] [PreservesBinaryBiproducts R]
    {X X₁ X₂ Z Z₁ Z₂ T T₁ T₂ : C} {Y Y₁ Y₂ : D}
    (i : X ≅ X₁ ⊞ X₂) (j : Y ≅ Y₁ ⊞ Y₂) (z : Z ≅ Z₁ ⊞ Z₂)
    (t : T ≅ T₁ ⊞ T₂)
    (a : T ⟶ R.obj Y) (a₁ : T₁ ⟶ R.obj Y₁) (a₂ : T₂ ⟶ R.obj Y₂)
    (p : X ⟶ Z) (p₁ : X₁ ⟶ Z₁) (p₂ : X₂ ⟶ Z₂)
    (q : T ⟶ Z) (q₁ : T₁ ⟶ Z₁) (q₂ : T₂ ⟶ Z₂)
    [IsIso q] [IsIso q₁] [IsIso q₂]
    (hp : p ≫ z.hom = i.hom ≫ biprod.map p₁ p₂)
    (hq : q ≫ z.hom = t.hom ≫ biprod.map q₁ q₂)
    (ha : a ≫ R.map j.hom ≫ (R.mapBiprod Y₁ Y₂).hom =
      t.hom ≫ biprod.map a₁ a₂) :
    p ≫ inv q ≫ a ≫ R.map j.hom ≫ (R.mapBiprod Y₁ Y₂).hom =
      i.hom ≫ biprod.map (p₁ ≫ inv q₁ ≫ a₁) (p₂ ≫ inv q₂ ≫ a₂) := by
  have hqi : inv q ≫ t.hom = z.hom ≫ biprod.map (inv q₁) (inv q₂) := by
    apply (cancel_epi q).mp
    simp only [IsIso.hom_inv_id_assoc]
    have hqid : biprod.map q₁ q₂ ≫ biprod.map (inv q₁) (inv q₂) = 𝟙 _ :=
      (biprod.mapIso (asIso q₁) (asIso q₂)).hom_inv_id
    rw [← Category.assoc, hq, Category.assoc, hqid, Category.comp_id]
  calc
    _ = p ≫ inv q ≫ t.hom ≫ biprod.map a₁ a₂ := by rw [ha]
    _ = p ≫ z.hom ≫ biprod.map (inv q₁) (inv q₂) ≫ biprod.map a₁ a₂ := by
      rw [← Category.assoc (inv q), hqi]
      simp only [Category.assoc]
    _ = i.hom ≫ biprod.map p₁ p₂ ≫ biprod.map (inv q₁) (inv q₂) ≫
        biprod.map a₁ a₂ := by
      rw [← Category.assoc p, hp, Category.assoc]
    _ = _ := by
      apply biprod.hom_ext
      · simp only [Category.assoc, biprod.map_fst, biprod.map_fst_assoc]
      · simp only [Category.assoc, biprod.map_snd, biprod.map_snd_assoc]

/-- The adjunction transpose of a diagonal map is the diagonal pair of transposes. -/
theorem relativeMV_pair_mates
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesBinaryBiproducts L] [PreservesBinaryBiproducts R]
    (a : L ⊣ R) {X X₁ X₂ : C} {Y Y₁ Y₂ A₁ A₂ B₁ B₂ : D}
    (i : X ≅ X₁ ⊞ X₂) (j : Y ≅ Y₁ ⊞ Y₂)
    (e₁ : L.obj X₁ ≅ A₁) (e₂ : L.obj X₂ ≅ A₂)
    (e₁' : Y₁ ≅ B₁) (e₂' : Y₂ ≅ B₂)
    (b₁ : A₁ ⟶ B₁) (b₂ : A₂ ⟶ B₂) :
    let e := L.mapIso i ≪≫ L.mapBiprod X₁ X₂ ≪≫ biprod.mapIso e₁ e₂
    let e' := j ≪≫ biprod.mapIso e₁' e₂'
    (a.homEquiv _ _) (e.hom ≫ biprod.map b₁ b₂ ≫ e'.inv) ≫ R.map j.hom ≫
        (R.mapBiprod Y₁ Y₂).hom =
      i.hom ≫ biprod.map
        ((a.homEquiv _ _) (e₁.hom ≫ b₁ ≫ e₁'.inv))
        ((a.homEquiv _ _) (e₂.hom ≫ b₂ ≫ e₂'.inv)) := by
  intro e e'
  apply biprod.hom_ext
  · simp only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_fst,
      biprod.map_fst]
    rw [← R.map_comp, ← a.homEquiv_naturality_right]
    simp only [e, e', Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
      biprod.mapIso_hom, biprod.mapIso_inv, Category.assoc,
      Iso.inv_hom_id_assoc, biprod.map_fst_assoc, biprod.map_fst,
      Functor.mapBiprod_hom, biprod.lift_fst_assoc]
    rw [← L.map_comp_assoc, a.homEquiv_naturality_left]
    simp only [Category.assoc]
  · simp only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_snd,
      biprod.map_snd]
    rw [← R.map_comp, ← a.homEquiv_naturality_right]
    simp only [e, e', Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
      biprod.mapIso_hom, biprod.mapIso_inv, Category.assoc,
      Iso.inv_hom_id_assoc, biprod.map_snd_assoc, biprod.map_snd,
      Functor.mapBiprod_hom, biprod.lift_snd_assoc]
    rw [← L.map_comp_assoc, a.homEquiv_naturality_left]
    simp only [Category.assoc]
/-- Each component of an invertible diagonal biproduct map is invertible. -/
theorem relativeMV_biprod_components_isIso
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {A₁ A₂ B₁ B₂ : C} (f : A₁ ⟶ B₁) (g : A₂ ⟶ B₂)
    [IsIso (biprod.map f g)] : IsIso f ∧ IsIso g := by
  constructor
  · refine ⟨⟨biprod.inl ≫ inv (biprod.map f g) ≫ biprod.fst, ?_, ?_⟩⟩
    · rw [← Category.assoc f biprod.inl, ← biprod.inl_map f g,
        Category.assoc, IsIso.hom_inv_id_assoc, biprod.inl_fst]
    · simp only [Category.assoc]
      rw [← biprod.map_fst f g, IsIso.inv_hom_id_assoc, biprod.inl_fst]
  · refine ⟨⟨biprod.inr ≫ inv (biprod.map f g) ≫ biprod.snd, ?_, ?_⟩⟩
    · rw [← Category.assoc g biprod.inr, ← biprod.inr_map f g,
        Category.assoc, IsIso.hom_inv_id_assoc, biprod.inr_snd]
    · simp only [Category.assoc]
      rw [← biprod.map_snd f g, IsIso.inv_hom_id_assoc, biprod.inr_snd]

section
variable {E D C : Type*} [Category E] [Category D] [Category C]
  [Preadditive E] [Preadditive D] [Preadditive C]
  [HasBinaryBiproducts E] [HasBinaryBiproducts D] [HasBinaryBiproducts C]
  (H : E ⥤ C) (T : D ⥤ C) (G : D ⥤ E)
  [H.Additive] [T.Additive] [G.Additive]
  [PreservesBinaryBiproducts H] [PreservesBinaryBiproducts T]
  (c : T ⟶ G ⋙ H)
  {A₁ A₂ Z₁ Z₂ : E} {B₁ B₂ : D}
  (r₁ : A₁ ⟶ Z₁) (r₂ : A₂ ⟶ Z₂)
  (s₁ : G.obj B₁ ⟶ Z₁) (s₂ : G.obj B₂ ⟶ Z₂)

omit [HasBinaryBiproducts C] in
/-- An additive functor carries a diagonal numerator to its diagonal component maps. -/
theorem relativeMV_roof_numerator_pair :
    H.map (biprod.map r₁ r₂) ≫ (H.mapBiprod Z₁ Z₂).hom =
      (H.mapBiprod A₁ A₂).hom ≫ biprod.map (H.map r₁) (H.map r₂) := by
  apply biprod.hom_ext <;>
    simp only [Functor.mapBiprod_hom, Category.assoc, biprod.lift_fst,
      biprod.lift_snd, biprod.map_fst, biprod.map_snd, biprod.lift_fst_assoc,
      biprod.lift_snd_assoc, ← H.map_comp]

omit [HasBinaryBiproducts C] [G.Additive] in
/-- Naturality identifies a comparison denominator with its two diagonal components. -/
theorem relativeMV_roof_denominator_pair :
    (c.app (B₁ ⊞ B₂) ≫ H.map (biprod.lift
      (G.map biprod.fst ≫ s₁) (G.map biprod.snd ≫ s₂))) ≫
        (H.mapBiprod Z₁ Z₂).hom =
      (T.mapBiprod B₁ B₂).hom ≫ biprod.map
        (c.app B₁ ≫ H.map s₁) (c.app B₂ ≫ H.map s₂) := by
  apply biprod.hom_ext
  · simp only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_fst,
      biprod.map_fst, biprod.lift_fst_assoc]
    rw [← H.map_comp, biprod.lift_fst, H.map_comp,
      ← Category.assoc]
    simpa only [Functor.comp_map, Category.assoc] using
      congrArg (fun t ↦ t ≫ H.map s₁) (c.naturality (biprod.fst : B₁ ⊞ B₂ ⟶ B₁)).symm
  · simp only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_snd,
      biprod.map_snd, biprod.lift_snd_assoc]
    rw [← H.map_comp, biprod.lift_snd, H.map_comp,
      ← Category.assoc]
    simpa only [Functor.comp_map, Category.assoc] using
      congrArg (fun t ↦ t ≫ H.map s₂) (c.naturality (biprod.snd : B₁ ⊞ B₂ ⟶ B₂)).symm
end

/-- A natural transformation commutes with the canonical additive biproduct comparisons. -/
theorem relativeMV_roof_unit_pair
    {E C D : Type*} [Category E] [Category C] [Category D]
    [Preadditive E] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts E] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (T : E ⥤ C) (J : E ⥤ D) (R : D ⥤ C)
    [T.Additive] [J.Additive] [R.Additive]
    [PreservesBinaryBiproducts T] [PreservesBinaryBiproducts J]
    [PreservesBinaryBiproducts R]
    (η : T ⟶ J ⋙ R) (B₁ B₂ : E) :
    η.app (B₁ ⊞ B₂) ≫ R.map (J.mapBiprod B₁ B₂).hom ≫
      (R.mapBiprod (J.obj B₁) (J.obj B₂)).hom =
    (T.mapBiprod B₁ B₂).hom ≫ biprod.map (η.app B₁) (η.app B₂) := by
  apply biprod.hom_ext
  · simp only [Category.assoc]
    change η.app (B₁ ⊞ B₂) ≫ R.map (J.mapBiprod B₁ B₂).hom ≫
        (R.mapBiprod (J.obj B₁) (J.obj B₂)).hom ≫ biprod.fst =
      (T.mapBiprod B₁ B₂).hom ≫ biprod.map (η.app B₁) (η.app B₂) ≫ biprod.fst
    rw [Functor.mapBiprod_hom R, biprod.lift_fst,
      ← R.map_comp, Functor.mapBiprod_hom J, biprod.lift_fst]
    rw [biprod.map_fst, Functor.mapBiprod_hom T, biprod.lift_fst_assoc]
    exact (η.naturality (biprod.fst : B₁ ⊞ B₂ ⟶ B₁)).symm
  · simp only [Category.assoc]
    change η.app (B₁ ⊞ B₂) ≫ R.map (J.mapBiprod B₁ B₂).hom ≫
        (R.mapBiprod (J.obj B₁) (J.obj B₂)).hom ≫ biprod.snd =
      (T.mapBiprod B₁ B₂).hom ≫ biprod.map (η.app B₁) (η.app B₂) ≫ biprod.snd
    rw [Functor.mapBiprod_hom R, biprod.lift_snd,
      ← R.map_comp, Functor.mapBiprod_hom J, biprod.lift_snd]
    rw [biprod.map_snd, Functor.mapBiprod_hom T, biprod.lift_snd_assoc]
    exact (η.naturality (biprod.snd : B₁ ⊞ B₂ ⟶ B₂)).symm
end AlgebraicGeometry
