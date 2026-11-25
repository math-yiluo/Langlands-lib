/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Rationalization

/-!
# Functoriality of the rationalization

Let `M` be a submonoid of a commutative ring `R` and `C` an `R`-linear triangulated category.
The morphisms of the rationalization `Rationalization M C` are fractions with denominators in
`M`: every morphism `Q X ⟶ Q Y` becomes of the form `Q f` after multiplication by some `m ∈ M`
(`CategoryTheory.Rationalization.exists_smul_eq_map`), and `Q f = Q g` if and only if
`m • f = m • g` for some `m ∈ M` (`CategoryTheory.Rationalization.map_eq_map_iff`). Both follow
from the observation that a morphism `s` with `M`-torsion mapping cone has an inverse up to
multiplication by an element of `M` (`CategoryTheory.Rationalization.exists_comp_eq_smul_id`).

An `R`-linear triangulated functor `F : C ⥤ D` induces a functor
`CategoryTheory.Rationalization.map M F` between the rationalizations, and this functor is
fully faithful when `F` is (`CategoryTheory.Rationalization.full_map`,
`CategoryTheory.Rationalization.faithful_map`): on `Hom` groups it is the localization at `M`
of the bijection induced by `F`.

More generally, a triangulated functor `F : C ⥤ D` which is linear along a ring morphism
`ψ : R ⟶ R'` carrying `M` into `M'` induces a triangulated functor
`CategoryTheory.Rationalization.mapOfRingHom ψ hM F hF : Rationalization M C ⥤ Rationalization M' D`
(`CategoryTheory.Rationalization.isTriangulated_mapOfRingHom`).
-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

open CategoryTheory Category Limits Pretriangulated

namespace CategoryTheory.Rationalization

variable {R : Type w} [CommRing R] (M : Submonoid R)
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [Pretriangulated C] [IsTriangulated C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [∀ n : ℤ, (shiftFunctor D n).Linear R]
  [Pretriangulated D] [IsTriangulated D]

variable {M}

omit [IsTriangulated C] in
/-- A morphism with `M`-torsion mapping cone is invertible up to multiplication by an element of
`M`: for `s : Y ⟶ Z` in `W M C` there are `m ∈ M` and `t : Z ⟶ Y` with `s ≫ t = m • 𝟙 Y`. -/
lemma exists_comp_eq_smul_id {Y Z : C} {s : Y ⟶ Z} (hs : W M C s) :
    ∃ m ∈ M, ∃ t : Z ⟶ Y, s ≫ t = m • 𝟙 Y := by
  rw [W, ObjectProperty.trW_iff'] at hs
  obtain ⟨X, f, h, hT, m, hm, hX⟩ := hs
  obtain ⟨t, ht⟩ := Triangle.yoneda_exact₂ _ hT (m • 𝟙 Y) (by
    change f ≫ (m • 𝟙 Y) = 0
    rw [Linear.comp_smul, comp_id, ← id_comp f, ← Linear.smul_comp, hX, zero_comp])
  exact ⟨m, hm, t, ht.symm⟩

/-- Two morphisms of `C` become equal in the rationalization if and only if they agree after
multiplication by an element of `M`. -/
lemma map_eq_map_iff {X Y : C} (f g : X ⟶ Y) :
    (Q M C).map f = (Q M C).map g ↔ ∃ m ∈ M, m • f = m • g := by
  constructor
  · intro h
    obtain ⟨Z, s, hs, hfs⟩ := (MorphismProperty.map_eq_iff_postcomp (Q M C) (W M C) f g).1 h
    obtain ⟨m, hm, t, ht⟩ := exists_comp_eq_smul_id hs
    refine ⟨m, hm, ?_⟩
    rw [← comp_id f, ← comp_id g, ← Linear.comp_smul, ← Linear.comp_smul, ← ht,
      ← assoc, hfs, assoc]
  · rintro ⟨m, hm, h⟩
    have := isIso_smul_id hm ((Q M C).obj X)
    rw [← cancel_epi (m • 𝟙 ((Q M C).obj X)), Linear.smul_comp, Linear.smul_comp, id_comp,
      id_comp, ← Functor.map_smul, ← Functor.map_smul, h]

/-- For a localization functor `L` at the morphisms with `M`-torsion mapping cone, every morphism
`L X ⟶ L Y` becomes the image of a morphism `X ⟶ Y` after multiplication by an element of `M`. -/
lemma exists_smul_eq_map_of_isLocalization {D' : Type*} [Category* D'] [Preadditive D']
    [Linear R D'] (L : C ⥤ D') [L.IsLocalization (W M C)] [L.Linear R] {X Y : C}
    (φ : L.obj X ⟶ L.obj Y) :
    ∃ m ∈ M, ∃ f : X ⟶ Y, m • φ = L.map f := by
  obtain ⟨ψ, rfl⟩ := Localization.exists_leftFraction L (W M C) φ
  obtain ⟨m, hm, t, ht⟩ := exists_comp_eq_smul_id ψ.hs
  refine ⟨m, hm, ψ.f ≫ t, ?_⟩
  rw [L.map_comp, ← MorphismProperty.LeftFraction.map_comp_map_s, assoc,
    ← L.map_comp, ht, Functor.map_smul, L.map_id, Linear.comp_smul, comp_id]

/-- Every morphism of the rationalization between objects of `C` becomes the image of a morphism
of `C` after multiplication by an element of `M`. -/
lemma exists_smul_eq_map {X Y : C} (φ : (Q M C).obj X ⟶ (Q M C).obj Y) :
    ∃ m ∈ M, ∃ f : X ⟶ Y, m • φ = (Q M C).map f :=
  exists_smul_eq_map_of_isLocalization (Q M C) φ

/-- In the rationalization, multiplication by an element of `M` is injective on morphisms. -/
lemma smul_left_injective {m : R} (hm : m ∈ M) {A B : Rationalization M C} :
    Function.Injective (fun φ : A ⟶ B ↦ m • φ) := fun φ₁ φ₂ h ↦ by
  have := isIso_smul_id hm A
  rw [← cancel_epi (m • 𝟙 A)]
  simpa using h

variable (M) (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R]

omit [IsTriangulated C] [IsTriangulated D] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [∀ n : ℤ, (shiftFunctor D n).Linear R] in
/-- An `R`-linear triangulated functor preserves the morphisms with `M`-torsion mapping cone. -/
lemma W_map {X Y : C} {s : X ⟶ Y} (hs : W M C s) : W M D (F.map s) := by
  obtain ⟨Z, g, h, hT, m, hm, hZ⟩ := hs
  exact ObjectProperty.trW.mk _ (F.map_distinguished _ hT)
    ⟨m, hm, by
      change m • 𝟙 (F.obj Z) = 0
      rw [← F.map_id, ← F.map_smul, hZ, F.map_zero]⟩

/-- The functor `Rationalization M C ⥤ Rationalization M D` induced by an `R`-linear
triangulated functor `F : C ⥤ D`. -/
noncomputable def map : Rationalization M C ⥤ Rationalization M D :=
  Localization.lift (F ⋙ Q M D)
    (fun _ _ _ hs ↦ Localization.inverts (Q M D) (W M D) _ (W_map M F hs)) (Q M C)

/-- The induced functor on rationalizations is compatible with the localization functors. -/
noncomputable def mapFac : Q M C ⋙ map M F ≅ F ⋙ Q M D :=
  Localization.fac _ _ _

noncomputable instance : Localization.Lifting (Q M C) (W M C) (F ⋙ Q M D) (map M F) :=
  ⟨mapFac M F⟩

/-- The induced functor on rationalizations is `R`-linear. -/
instance : (map M F).Linear R :=
  (Localization.functor_linear_iff (Q M C) (W M C) R (F ⋙ Q M D) (map M F)).1 inferInstance

variable {M}

/-- The action of the induced functor on morphisms between objects of `C`, transported along
`CategoryTheory.Rationalization.mapFac`. -/
noncomputable def mapHom {X Y : C} (φ : (Q M C).obj X ⟶ (Q M C).obj Y) :
    (Q M D).obj (F.obj X) ⟶ (Q M D).obj (F.obj Y) :=
  (mapFac M F).inv.app X ≫ (map M F).map φ ≫ (mapFac M F).hom.app Y

omit [IsTriangulated C] [IsTriangulated D] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [∀ n : ℤ, (shiftFunctor D n).Linear R] in
lemma mapHom_map {X Y : C} (f : X ⟶ Y) : mapHom F ((Q M C).map f) = (Q M D).map (F.map f) := by
  simp [mapHom, ← Functor.comp_map, (mapFac M F).hom.naturality f]

omit [IsTriangulated C] [IsTriangulated D] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [∀ n : ℤ, (shiftFunctor D n).Linear R] in
lemma mapHom_comp {X Y Z : C} (φ : (Q M C).obj X ⟶ (Q M C).obj Y)
    (ψ : (Q M C).obj Y ⟶ (Q M C).obj Z) : mapHom F (φ ≫ ψ) = mapHom F φ ≫ mapHom F ψ := by
  simp [mapHom]

omit [IsTriangulated C] [IsTriangulated D] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [∀ n : ℤ, (shiftFunctor D n).Linear R] in
@[simp]
lemma mapHom_id (X : C) : mapHom F (𝟙 ((Q M C).obj X)) = 𝟙 _ := by
  simp [mapHom]

lemma mapHom_smul {X Y : C} (r : R) (φ : (Q M C).obj X ⟶ (Q M C).obj Y) :
    mapHom F (r • φ) = r • mapHom F φ := by
  simp [mapHom]

variable [F.Full] [F.Faithful]

lemma mapHom_bijective (X Y : C) :
    Function.Bijective (mapHom F : ((Q M C).obj X ⟶ (Q M C).obj Y) → _) := by
  constructor
  · intro φ₁ φ₂ h
    obtain ⟨m₁, hm₁, f₁, h₁⟩ := exists_smul_eq_map φ₁
    obtain ⟨m₂, hm₂, f₂, h₂⟩ := exists_smul_eq_map φ₂
    have e₁ : (m₁ * m₂) • φ₁ = (Q M C).map (m₂ • f₁) := by
      rw [mul_comm, mul_smul, h₁, Functor.map_smul]
    have e₂ : (m₁ * m₂) • φ₂ = (Q M C).map (m₁ • f₂) := by
      rw [mul_smul, h₂, Functor.map_smul]
    have h₁₂ : (Q M D).map (F.map (m₂ • f₁)) = (Q M D).map (F.map (m₁ • f₂)) := by
      rw [← mapHom_map, ← mapHom_map, ← e₁, ← e₂, mapHom_smul, mapHom_smul, h]
    obtain ⟨m, hm, h'⟩ := (map_eq_map_iff _ _).1 h₁₂
    rw [← F.map_smul, ← F.map_smul, F.map_injective.eq_iff] at h'
    refine smul_left_injective (M.mul_mem hm (M.mul_mem hm₁ hm₂)) ?_
    dsimp only
    rw [mul_smul, mul_smul m, e₁, e₂, ← Functor.map_smul, ← Functor.map_smul, h']
  · intro ψ
    obtain ⟨m, hm, g, hg⟩ := exists_smul_eq_map ψ
    obtain ⟨f, rfl⟩ := F.map_surjective g
    have := isIso_smul_id hm ((Q M C).obj X)
    have := isIso_smul_id hm ((Q M D).obj (F.obj X))
    refine ⟨inv (m • 𝟙 ((Q M C).obj X)) ≫ (Q M C).map f, ?_⟩
    have hinv : mapHom F (inv (m • 𝟙 ((Q M C).obj X))) =
        inv (m • 𝟙 ((Q M D).obj (F.obj X))) := by
      refine (IsIso.inv_eq_of_hom_inv_id ?_).symm
      rw [← mapHom_id F X, ← mapHom_smul, ← mapHom_comp, IsIso.hom_inv_id, mapHom_id]
    rw [mapHom_comp, hinv, mapHom_map, ← hg, IsIso.inv_comp_eq, Linear.smul_comp, id_comp]

/-- The functor induced on rationalizations by a fully faithful `R`-linear triangulated functor
is full. -/
instance full_map : (map M F).Full := by
  have := Localization.essSurj (Q M C) (W M C)
  refine ⟨fun {A B} ψ ↦ ?_⟩
  let eA := (Q M C).objObjPreimageIso A
  let eB := (Q M C).objObjPreimageIso B
  obtain ⟨φ, hφ⟩ := (mapHom_bijective F _ _).2
    ((mapFac M F).inv.app _ ≫ (map M F).map eA.hom ≫ ψ ≫ (map M F).map eB.inv ≫
      (mapFac M F).hom.app _)
  have h : (map M F).map φ = (map M F).map eA.hom ≫ ψ ≫ (map M F).map eB.inv := by
    rw [← cancel_mono ((mapFac M F).hom.app _)]
    simpa [mapHom] using hφ
  refine ⟨eA.inv ≫ φ ≫ eB.hom, ?_⟩
  rw [Functor.map_comp, Functor.map_comp, h]
  simp only [assoc, ← Functor.map_comp_assoc, eA.inv_hom_id, ← Functor.map_comp, eB.inv_hom_id,
    Functor.map_id, id_comp, comp_id]

/-- The functor induced on rationalizations by a fully faithful `R`-linear triangulated functor
is faithful. -/
instance faithful_map : (map M F).Faithful := by
  have := Localization.essSurj (Q M C) (W M C)
  refine ⟨fun {A B} φ₁ φ₂ h ↦ ?_⟩
  let eA := (Q M C).objObjPreimageIso A
  let eB := (Q M C).objObjPreimageIso B
  have : eA.hom ≫ φ₁ ≫ eB.inv = eA.hom ≫ φ₂ ≫ eB.inv :=
    (mapHom_bijective F _ _).1 (by simp [mapHom, h])
  simpa using this


section RingHom

variable {R R' : Type*} [CommRing R] [CommRing R'] (ψ : R →+* R') {M : Submonoid R}
  {M' : Submonoid R'} (hM : M ≤ M'.comap ψ)
  {C : Type*} [Category C] [Preadditive C] [Linear R C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [Pretriangulated C] [IsTriangulated C]
  {D : Type*} [Category D] [Preadditive D] [Linear R' D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [∀ n : ℤ, (shiftFunctor D n).Linear R']
  [Pretriangulated D] [IsTriangulated D]
  (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
  (hF : ∀ (r : R) {X Y : C} (f : X ⟶ Y), F.map (r • f) = ψ r • F.map f)

omit [∀ n : ℤ, (shiftFunctor C n).Linear R] [IsTriangulated C]
  [∀ n : ℤ, (shiftFunctor D n).Linear R'] [IsTriangulated D] in
include hM hF in
/-- A triangulated functor which is linear along a ring morphism `ψ : R ⟶ R'` carrying `M` into
`M'` preserves the morphisms with torsion mapping cone. -/
lemma W_map_of_ringHom {X Y : C} {s : X ⟶ Y} (hs : W M C s) : W M' D (F.map s) := by
  obtain ⟨Z, g, h, hT, m, hm, hZ⟩ := hs
  exact ObjectProperty.trW.mk _ (F.map_distinguished _ hT)
    ⟨ψ m, hM hm, by
      change ψ m • 𝟙 (F.obj Z) = 0
      rw [← F.map_id, ← hF, hZ, F.map_zero]⟩

/-- The functor `Rationalization M C ⥤ Rationalization M' D` induced by a triangulated functor
which is linear along a ring morphism `ψ : R ⟶ R'` carrying `M` into `M'`. -/
noncomputable def mapOfRingHom : Rationalization M C ⥤ Rationalization M' D :=
  Localization.lift (F ⋙ Q M' D)
    (fun _ _ _ hs ↦ Localization.inverts (Q M' D) (W M' D) _ (W_map_of_ringHom ψ hM F hF hs))
    (Q M C)

noncomputable instance : Localization.Lifting (Q M C) (W M C) (F ⋙ Q M' D)
    (mapOfRingHom ψ hM F hF) :=
  ⟨Localization.fac _ _ _⟩

noncomputable instance : (mapOfRingHom ψ hM F hF).CommShift ℤ :=
  Functor.commShiftOfLocalization (Q M C) (W M C) ℤ (F ⋙ Q M' D) (mapOfRingHom ψ hM F hF)

/-- The functor induced on rationalizations by a triangulated functor linear along a ring
morphism is triangulated: a distinguished triangle of the rationalization is isomorphic to the
image of a distinguished triangle of `C`. -/
instance isTriangulated_mapOfRingHom : (mapOfRingHom ψ hM F hF).IsTriangulated := by
  have := Localization.essSurj_mapArrow (Q M C) (W M C)
  refine ⟨fun T hT ↦ ?_⟩
  obtain ⟨T₀, e, hT₀⟩ := (Functor.distTriang_iff (Q M C) T).1 hT
  let G := mapOfRingHom ψ hM F hF
  exact Pretriangulated.isomorphic_distinguished _ ((F ⋙ Q M' D).map_distinguished _ hT₀) _
    (G.mapTriangle.mapIso e ≪≫ (Functor.mapTriangleCompIso (Q M C) G).symm.app T₀ ≪≫
      (Functor.mapTriangleIso (Localization.Lifting.iso (Q M C) (W M C) (F ⋙ Q M' D) G)).app T₀)

end RingHom

end CategoryTheory.Rationalization
