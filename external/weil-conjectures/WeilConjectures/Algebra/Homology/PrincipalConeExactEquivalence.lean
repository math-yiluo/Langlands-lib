/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.PrincipalConeTower
import all WeilConjectures.AlgebraicGeometry.IntegralDerivedOperationsOnSlices
/-! # Exact equivalences preserve principal cone completion and its unit
Source: Stacks Tags 0941 and 0A0E.
(auxiliary; not a blueprint node). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option linter.privateModule false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainComplex CochainComplex.HomComplex
namespace CochainComplex
variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  (H : A ⥤ B) [H.Additive]
private theorem mapCone_inl {X Y : CochainComplex A ℤ}
    (f : X ⟶ Y) (p q : ℤ) (hpq : p + -1 = q) :
    H.map ((mappingCone.inl f).v p q hpq) ≫
      (mappingCone.mapHomologicalComplexIso f H).hom.f q =
        (mappingCone.inl ((H.mapHomologicalComplex (.up ℤ)).map f)).v p q hpq := by
  change H.map ((mappingCone.inl f).v p q hpq) ≫
    (mappingCone.mapHomologicalComplexXIso f H q).hom = _
  rw [mappingCone.mapHomologicalComplexXIso_eq f H q p (by omega)]
  simp only [mappingCone.mapHomologicalComplexXIso'_hom, Preadditive.comp_add,
    ← H.map_comp_assoc, mappingCone.inl_v_fst_v, mappingCone.inl_v_snd_v,
    H.map_id, H.map_zero, Category.id_comp, Limits.zero_comp, add_zero]

private theorem mapCone_ext {X Y : CochainComplex A ℤ} (f : X ⟶ Y) (n : ℤ)
    {Z : B} (a b : H.obj ((mappingCone f).X n) ⟶ Z)
    (h₁ : H.map ((mappingCone.inl f).v (n + 1) n (by omega)) ≫ a =
      H.map ((mappingCone.inl f).v (n + 1) n (by omega)) ≫ b)
    (h₂ : H.map ((mappingCone.inr f).f n) ≫ a =
      H.map ((mappingCone.inr f).f n) ≫ b) : a = b := by
  have hid := congrArg H.map (mappingCone.id_X f n (n + 1) rfl)
  simp only [H.map_add, H.map_comp, H.map_id] at hid
  calc
    a = (H.map ((mappingCone.fst f).1.v n (n + 1) rfl) ≫
        H.map ((mappingCone.inl f).v (n + 1) n (by omega)) +
      H.map ((mappingCone.snd f).v n n (add_zero n)) ≫
        H.map ((mappingCone.inr f).f n)) ≫ a := by rw [hid, Category.id_comp]
    _ = _ := by rw [Preadditive.add_comp, Category.assoc, Category.assoc, h₁, h₂]
    _ = b := by rw [← Category.assoc, ← Category.assoc, ← Preadditive.add_comp,
      hid, Category.id_comp]

private theorem mapCone_natural {X Y X' Y' : CochainComplex A ℤ}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) :
    let G := H.mapHomologicalComplex (.up ℤ)
    G.map (mappingCone.map f g a b h) ≫ (mappingCone.mapHomologicalComplexIso g H).hom =
      (mappingCone.mapHomologicalComplexIso f H).hom ≫
        mappingCone.map (G.map f) (G.map g) (G.map a) (G.map b)
          (by rw [← G.map_comp, ← G.map_comp, h]) := by
  dsimp only
  ext n
  apply mapCone_ext H f n
  · simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      ← H.map_comp_assoc]
    simp only [Int.reduceNeg, mappingCone.map, mappingCone.inl_v_desc_f,
      Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Functor.map_comp,
      Functor.mapHomologicalComplex_obj_X, ← Category.assoc, mapCone_inl,
      Functor.mapHomologicalComplex_map_f]
    rw [Category.assoc, mapCone_inl]
  · simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      ← H.map_comp_assoc]
    have hf := congrArg (fun z ↦ z.f n) (mappingCone.map_inr f H)
    have hg := congrArg (fun z ↦ z.f n) (mappingCone.map_inr g H)
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] at hf hg
    simp only [mappingCone.map, Int.reduceNeg, mappingCone.inr_f_desc_f, comp_f,
      Functor.map_comp, Functor.mapHomologicalComplex_obj_X, ← Category.assoc, hf,
      Functor.mapHomologicalComplex_map_f]
    rw [Category.assoc, hg]

private def mapCoconeIso {X Y : CochainComplex A ℤ} (f : X ⟶ Y) :
    (H.mapHomologicalComplex (.up ℤ)).obj (mappingCocone f) ≅
      mappingCocone ((H.mapHomologicalComplex (.up ℤ)).map f) :=
  ((H.mapHomologicalComplex (.up ℤ)).commShiftIso (-1)).app _ ≪≫
    (shiftFunctor _ (-1)).mapIso (mappingCone.mapHomologicalComplexIso f H)

private theorem mapCoconeIso_inl {X Y : CochainComplex A ℤ} (f : X ⟶ Y) (n : ℤ) :
    H.map ((mappingCocone.inl f).v n n (add_zero n)) ≫
      (mapCoconeIso H f).hom.f n =
        (mappingCocone.inl ((H.mapHomologicalComplex (.up ℤ)).map f)).v n n
          (add_zero n) := by
  simp only [mapCoconeIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom,
    HomologicalComplex.comp_f]
  rw [Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
  change H.map ((mappingCocone.inl f).v n n (add_zero n)) ≫
    (𝟙 _) ≫ (mappingCone.mapHomologicalComplexXIso f H (n + -1)).hom = _
  erw [Category.id_comp]
  simp only [mappingCocone.inl, Cochain.rightShift_v,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv, Category.comp_id]
  rw [mappingCone.mapHomologicalComplexXIso_eq f H (n + -1) n (by omega)]
  simp only [mappingCone.mapHomologicalComplexXIso'_hom, Preadditive.comp_add,
    ← H.map_comp_assoc, mappingCone.inl_v_fst_v, mappingCone.inl_v_snd_v,
    H.map_id, H.map_zero, Category.id_comp, Limits.zero_comp, add_zero]

private theorem mapCoconeIso_lift {X Y P : CochainComplex A ℤ}
    (f : X ⟶ Y) (u : P ⟶ X) (h : u ≫ f = 0) :
    (H.mapHomologicalComplex (.up ℤ)).map
        (mappingCocone.lift f u 0 (by simp [h])) ≫
      (mapCoconeIso H f).hom =
    mappingCocone.lift ((H.mapHomologicalComplex (.up ℤ)).map f)
      ((H.mapHomologicalComplex (.up ℤ)).map u) 0
        (by simp [← Functor.map_comp, h]) := by
  ext n
  rw [HomologicalComplex.comp_f,
    completedCoconeLift_f]
  · change H.map ((mappingCocone.lift f u 0 _).f n) ≫ _ = _
    rw [completedCoconeLift_f, H.map_comp, Category.assoc, mapCoconeIso_inl]
    · rfl
    · exact h
  · simp [← Functor.map_comp, h]
private def coneSquareIso {X Y X' Y' : CochainComplex B ℤ}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ≅ X') (b : Y ≅ Y')
    (h : f ≫ b.hom = a.hom ≫ g) : mappingCone f ≅ mappingCone g where
  hom := mappingCone.map f g a.hom b.hom h
  inv := mappingCone.map g f a.inv b.inv (by
    rw [← cancel_epi a.hom, ← cancel_mono b.hom]
    simp only [Iso.hom_inv_id_assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, h])
  hom_inv_id := by
    rw [← mappingCone.map_comp]
    simp only [Iso.hom_inv_id]
    exact mappingCone.map_id f
  inv_hom_id := by
    rw [← mappingCone.map_comp]
    simp only [Iso.inv_hom_id]
    exact mappingCone.map_id g

private theorem mapTowerCoconeComparison [HasCountableProducts A] [HasCountableProducts B]
    [H.IsEquivalence]
    (K : ℕ → CochainComplex A ℤ) (L : ℕ → CochainComplex B ℤ)
    (f : ∀ n, K (n + 1) ⟶ K n) (g : ∀ n, L (n + 1) ⟶ L n)
    (e : ∀ n, (H.mapHomologicalComplex (.up ℤ)).obj (K n) ≅ L n)
    (he : ∀ n, (H.mapHomologicalComplex (.up ℤ)).map (f n) ≫ (e n).hom =
      (e (n + 1)).hom ≫ g n)
    {P : CochainComplex A ℤ} (u : ∀ n, P ⟶ K n)
    (v : ∀ n, (H.mapHomologicalComplex (.up ℤ)).obj P ⟶ L n)
    (hu : ∀ n, (H.mapHomologicalComplex (.up ℤ)).map (u n) ≫ (e n).hom = v n)
    (hz : Pi.lift u ≫ towerTransitionEndomorphism f = 0)
    (hw : Pi.lift v ≫ towerTransitionEndomorphism g = 0) :
    ∃ i : (H.mapHomologicalComplex (.up ℤ)).obj
          (mappingCocone (towerTransitionEndomorphism f)) ≅
        mappingCocone (towerTransitionEndomorphism g),
      (H.mapHomologicalComplex (.up ℤ)).map
          (mappingCocone.lift _ (Pi.lift u) 0 (by simp [hz])) ≫ i.hom =
        mappingCocone.lift _ (Pi.lift v) 0 (by simp [hw]) := by
  classical
  let G := H.mapHomologicalComplex (.up ℤ)
  let p : G.obj (∏ᶜ K) ≅ ∏ᶜ L :=
    PreservesProduct.iso G K ≪≫ Pi.mapIso e
  have hp (n : ℕ) : p.hom ≫ Pi.π L n = G.map (Pi.π K n) ≫ (e n).hom := by
    simp [p, PreservesProduct.iso_hom, Category.assoc]
  have hsq : G.map (towerTransitionEndomorphism f) ≫ p.hom =
      p.hom ≫ towerTransitionEndomorphism g := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, hp]
    rw [← G.map_comp_assoc]
    simp only [towerTransitionEndomorphism, Preadditive.sub_comp,
      Category.id_comp, towerProductShift, Pi.lift_comp_π, G.map_sub,
      Preadditive.sub_comp, G.map_comp, Category.assoc,
      Preadditive.comp_sub, Category.comp_id, hp]
    rw [← Category.assoc p.hom, hp, Category.assoc, he]
  have hunit : G.map (Pi.lift u) ≫ p.hom = Pi.lift v := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, hp, ← G.map_comp_assoc, Pi.lift_comp_π, Pi.lift_comp_π]
    exact hu n
  let c := coneSquareIso (G.map (towerTransitionEndomorphism f))
    (towerTransitionEndomorphism g) p p hsq
  let i := mapCoconeIso H (towerTransitionEndomorphism f) ≪≫
    (shiftFunctor _ (-1 : ℤ)).mapIso c
  refine ⟨i, ?_⟩
  change G.map _ ≫ (mapCoconeIso H _).hom ≫ _ = _
  rw [← Category.assoc, mapCoconeIso_lift H _ _ hz]
  have hz' : G.map (Pi.lift u) ≫ G.map (towerTransitionEndomorphism f) = 0 := by
    rw [← G.map_comp, hz, G.map_zero]
  have hn : (𝟙 (G.obj P)) ≫ Pi.lift v = G.map (Pi.lift u) ≫ p.hom := by
    simpa only [Category.id_comp] using hunit.symm
  exact (completedCoconeLift_natural B _ _ p.hom p.hom hsq (𝟙 _)
    (G.map (Pi.lift u)) (Pi.lift v) hz' hw hn).symm.trans (Category.id_comp _)
private theorem mapPow {P : CochainComplex A ℤ} (μ : End P) (n : ℕ) :
    (H.mapHomologicalComplex (.up ℤ)).map (μ ^ n).asHom =
      (End.of ((H.mapHomologicalComplex (.up ℤ)).map μ.asHom) ^ n).asHom :=
  congrArg End.asHom (map_pow ((H.mapHomologicalComplex (.up ℤ)).mapEnd P) μ n)

private def principalLevelIso {P : CochainComplex A ℤ} (μ : End P) (n : ℕ) :
    (H.mapHomologicalComplex (.up ℤ)).obj (PrincipalCone.level μ n) ≅
      PrincipalCone.level (End.of ((H.mapHomologicalComplex (.up ℤ)).map μ.asHom)) n :=
  mappingCone.mapHomologicalComplexIso _ H ≪≫
    coneSquareIso ((H.mapHomologicalComplex (.up ℤ)).map (μ ^ (n + 1)).asHom)
      (End.of ((H.mapHomologicalComplex (.up ℤ)).map μ.asHom) ^ (n + 1)).asHom
      (Iso.refl _) (Iso.refl _) (by simpa using mapPow H μ (n + 1))

private theorem principalLevelIso_inr {P : CochainComplex A ℤ} (μ : End P) (n : ℕ) :
    (H.mapHomologicalComplex (.up ℤ)).map (mappingCone.inr (μ ^ (n + 1)).asHom) ≫
        (principalLevelIso H μ n).hom =
      mappingCone.inr
        (End.of ((H.mapHomologicalComplex (.up ℤ)).map μ.asHom) ^ (n + 1)).asHom := by
  simp only [principalLevelIso, Iso.trans_hom]
  rw [← Category.assoc, mappingCone.map_inr]
  simp [coneSquareIso, mappingCone.map]

private theorem principalLevelIso_step {P : CochainComplex A ℤ} (μ : End P) (n : ℕ) :
    (H.mapHomologicalComplex (.up ℤ)).map (PrincipalCone.step μ n) ≫
        (principalLevelIso H μ n).hom =
      (principalLevelIso H μ (n + 1)).hom ≫
        PrincipalCone.step (End.of ((H.mapHomologicalComplex (.up ℤ)).map μ.asHom)) n := by
  simp only [principalLevelIso, Iso.trans_hom, Category.assoc, PrincipalCone.step]
  rw [← Category.assoc, mapCone_natural H]
  simp only [Category.assoc]
  congr 1
  unfold coneSquareIso
  rw [← mappingCone.map_comp, ← mappingCone.map_comp]
  simp only [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

/-- An additive equivalence preserves the principal completion and its specified unit.
Source: Stacks Tags 0941 and 0A0E.
(auxiliary; not a blueprint node).
Proof: identify each finite mapping cone with the cone of the image endomorphism.
The comparison preserves its two inclusions, hence the transition squares and the
augmentation. The product comparison intertwines one minus the transition shift.
Mapping the final cocone and using the shift comparison gives the completion
isomorphism. Its equality on the normalized lift follows degree by degree from
preservation of the cocone inclusion and the zero homotopy. -/
theorem principalCompletionMap [HasCountableProducts A] [HasCountableProducts B]
    [H.IsEquivalence] {P : CochainComplex A ℤ} (μ : End P) :
    ∃ i : (H.mapHomologicalComplex (.up ℤ)).obj (PrincipalCone.completion μ) ≅
        PrincipalCone.completion (End.of ((H.mapHomologicalComplex (.up ℤ)).map μ.asHom)),
      (H.mapHomologicalComplex (.up ℤ)).map (PrincipalCone.unit μ) ≫ i.hom =
        PrincipalCone.unit (End.of ((H.mapHomologicalComplex (.up ℤ)).map μ.asHom)) := by
  exact mapTowerCoconeComparison H _ _ (PrincipalCone.step μ)
    (PrincipalCone.step _) (principalLevelIso H μ) (principalLevelIso_step H μ)
    (fun n ↦ mappingCone.inr (μ ^ (n + 1)).asHom)
    (fun n ↦ mappingCone.inr
      (End.of ((H.mapHomologicalComplex (.up ℤ)).map μ.asHom) ^ (n + 1)).asHom)
    (principalLevelIso_inr H μ) (PrincipalCone.productUnit_comp μ)
    (PrincipalCone.productUnit_comp _)

end CochainComplex
