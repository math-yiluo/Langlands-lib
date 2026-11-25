/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap

/-!

# Rationalizations of triangulated subcategories from integral models

Let `ℓ` be a natural number, `C` a triangulated category with a triangulated subcategory `P`,
and `L : C ⥤ D` a triangulated functor to a pretriangulated category on which multiplication by
`ℓ` is invertible, restricting to a functor `F : P ⥤ Q` to a full subcategory `Q` of `D`. If every
object of `Q` comes from `P` and the maps of `L` on morphisms become bijective after inverting `ℓ`,
then `F` exhibits `Q` as the rationalization of `P` at the powers of `ℓ`
(`CategoryTheory.Rationalization.isLocalization_of_models`): it is a localization functor for
the class `CategoryTheory.Rationalization.W (Submonoid.powers ℓ) P` of morphisms whose mapping
cone is killed by a power of `ℓ`.

-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

open CategoryTheory.Category

private theorem essSurj_of_subcategory_models
    {C D : Type*} [Category C] [Category D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (L : C ⥤ D)
    (F : P.FullSubcategory ⥤ Q.FullSubcategory) (e : F ⋙ Q.ι ≅ P.ι ⋙ L)
    (h : ∀ K : Q.FullSubcategory, ∃ M : P.FullSubcategory,
      Nonempty (L.obj M.obj ≅ K.obj)) : F.EssSurj := ⟨fun K ↦ by
  obtain ⟨M, ⟨eM⟩⟩ := h K
  exact ⟨M, ⟨Q.isoMk (e.app M ≪≫ eM)⟩⟩⟩

private theorem scalar_power_isIso
    {R C : Type*} [CommRing R] [Category C] [Preadditive C] [Linear R C]
    (p : R) (Y : C) [IsIso (p • 𝟙 Y)] (n : ℕ) : IsIso (p ^ n • 𝟙 Y) := by
  induction n with
  | zero => simpa using (inferInstance : IsIso (𝟙 Y))
  | succ n ih =>
    have h : p ^ (n + 1) • 𝟙 Y = (p ^ n • 𝟙 Y) ≫ (p • 𝟙 Y) := by
      simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, pow_succ, mul_smul]
      exact smul_comm _ _ _
    rw [h]
    infer_instance

private theorem rationalization_inverts_of_scalar
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (M : Submonoid ℤ) (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (hUnits : ∀ m ∈ M, ∀ Y : D, IsIso (m • 𝟙 Y)) :
    (Rationalization.W M C).IsInvertedBy F := by
  rintro A B f ⟨Z, g, h, hT, m, hm, hZ⟩
  have : IsIso (m • 𝟙 (F.obj Z)) := hUnits m hm _
  have he : m • 𝟙 (F.obj Z) = 0 := by
    simpa only [F.map_zsmul, F.map_id, F.map_zero] using congrArg F.map hZ
  have hz : IsZero (F.obj Z) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply (cancel_epi (m • 𝟙 (F.obj Z))).1
    simp only [Category.comp_id, Limits.comp_zero, he]
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁
    (F.mapTriangle.obj (Pretriangulated.Triangle.mk f g h))
    (F.map_distinguished _ hT)).1 hz

-- Clear scalar fractions to prove that the functor induced on the rationalization is
-- fully faithful, then use essential surjectivity and uniqueness of localization.
private theorem rationalization_localization_of_hom
    {R : Type*} [CommRing R]
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [Linear R C] [Linear R D]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor C n).Linear R]
    [Pretriangulated C] [IsTriangulated C]
    (M : Submonoid R) (F : C ⥤ D) [F.Additive] [F.Linear R] [F.EssSurj]
    (hInv : (Rationalization.W M C).IsInvertedBy F)
    (hUnits : ∀ m ∈ M, ∀ Y : D, IsIso (m • 𝟙 Y))
    (hSurj : ∀ (X Y : C) (f : F.obj X ⟶ F.obj Y),
      ∃ m ∈ M, ∃ g : X ⟶ Y, m • f = F.map g)
    (hEq : ∀ (X Y : C) (f g : X ⟶ Y), F.map f = F.map g →
      ∃ m ∈ M, m • f = m • g) :
    F.IsLocalization (Rationalization.W M C) := by
  let Q := Rationalization.Q M C
  let W := Rationalization.W M C
  let G := Localization.lift F hInv Q
  let e : Q ⋙ G ≅ F := Localization.fac F hInv Q
  have : (Q ⋙ G).Additive := Functor.additive_of_iso e.symm
  have : G.Additive := (Localization.functor_additive_iff Q W G).2 inferInstance
  let : Localization.Lifting Q W F G := ⟨e⟩
  have : G.Linear R :=
    (Localization.functor_linear_iff Q W R F G).1 inferInstance
  let H (X Y : C) (f : Q.obj X ⟶ Q.obj Y) :=
    e.inv.app X ≫ G.map f ≫ e.hom.app Y
  have hMap (X Y : C) (f : X ⟶ Y) : H X Y (Q.map f) = F.map f := by
    simp only [H, ← Functor.comp_map, e.hom.naturality, Iso.inv_hom_id_app_assoc]
  have hSmul (X Y : C) (m : R) (f : Q.obj X ⟶ Q.obj Y) :
      H X Y (m • f) = m • H X Y f := by
    simp only [H, G.map_smul, Linear.comp_smul, Linear.smul_comp]
  have hBij (X Y : C) : Function.Bijective (H X Y) := by
    constructor
    · intro f g h
      obtain ⟨m₁, hm₁, f₁, hf₁⟩ := Rationalization.exists_smul_eq_map f
      obtain ⟨m₂, hm₂, f₂, hf₂⟩ := Rationalization.exists_smul_eq_map g
      have e₁ : (m₁ * m₂) • f = Q.map (m₂ • f₁) := by
        rw [mul_comm, mul_smul, hf₁, Q.map_smul]
      have e₂ : (m₁ * m₂) • g = Q.map (m₁ • f₂) := by
        rw [mul_smul, hf₂, Q.map_smul]
      have he : F.map (m₂ • f₁) = F.map (m₁ • f₂) := by
        rw [← hMap, ← hMap, ← e₁, ← e₂, hSmul, hSmul, h]
      apply Rationalization.smul_left_injective (M.mul_mem hm₁ hm₂)
      dsimp only
      rw [e₁, e₂]
      exact (Rationalization.map_eq_map_iff _ _).2 (hEq X Y _ _ he)
    · intro f
      obtain ⟨m, hm, g, hg⟩ := hSurj X Y f
      have : IsIso (m • 𝟙 (Q.obj X)) := Rationalization.isIso_smul_id hm _
      have : IsIso (m • 𝟙 (F.obj X)) := hUnits m hm _
      let g' := inv (m • 𝟙 (Q.obj X)) ≫ Q.map g
      have hg' : m • g' = Q.map g := by
        calc
          m • g' = (m • 𝟙 (Q.obj X)) ≫ g' := by simp
          _ = Q.map g := by dsimp only [g']; rw [IsIso.hom_inv_id_assoc]
      refine ⟨g', ?_⟩
      apply (cancel_epi (m • 𝟙 (F.obj X))).1
      simp only [Linear.smul_comp, Category.id_comp]
      rw [← hSmul, hg', hMap, hg]
  have : G.Full := ⟨fun {A B} f ↦ by
    let eA := Q.objObjPreimageIso A
    let eB := Q.objObjPreimageIso B
    obtain ⟨g, hg⟩ := (hBij _ _).2
      (e.inv.app _ ≫ G.map eA.hom ≫ f ≫ G.map eB.inv ≫ e.hom.app _)
    have h : G.map g = G.map eA.hom ≫ f ≫ G.map eB.inv := by
      rw [← cancel_mono (e.hom.app _)]
      simpa [H] using hg
    refine ⟨eA.inv ≫ g ≫ eB.hom, ?_⟩
    rw [G.map_comp, G.map_comp, h]
    simp only [Category.assoc, ← G.map_comp_assoc, eA.inv_hom_id,
      ← G.map_comp, eB.inv_hom_id, G.map_id, Category.id_comp, Category.comp_id]⟩
  have : G.Faithful := ⟨fun {A B} f g h ↦ by
    let eA := Q.objObjPreimageIso A
    let eB := Q.objObjPreimageIso B
    have he : eA.hom ≫ f ≫ eB.inv = eA.hom ≫ g ≫ eB.inv :=
      (hBij _ _).1 (by simp only [H, G.map_comp, Category.assoc, h])
    simpa using he⟩
  have : G.EssSurj := ⟨fun Y ↦
    ⟨Q.obj (F.objPreimage Y), ⟨e.app _ ≪≫ F.objObjPreimageIso Y⟩⟩⟩
  have : G.IsEquivalence := {}
  exact Functor.IsLocalization.of_equivalence_target Q W F G.asEquivalence e

/-- Let `P` be a triangulated subcategory of a triangulated category `C`, `Q` a full
subcategory of a pretriangulated category `D` on which multiplication by `ℓ` is invertible, and
`L : C ⥤ D` a triangulated functor restricting to `F : P ⥤ Q` (`e : F ⋙ Q.ι ≅ P.ι ⋙ L`). Suppose
that every object of `Q` is isomorphic to `L M` for some `M` in `P`, that every morphism
`L A ⟶ L B` becomes the image of a morphism `A ⟶ B` after multiplication by a power of `ℓ`, and
that two morphisms with the same image under `L` agree after multiplication by a power of `ℓ`.
Then `F` is a localization functor for the morphisms of `P` whose mapping cone is killed by a
power of `ℓ`.

Proof: `L` kills the `ℓ`-power torsion objects, so `F` inverts these morphisms. The functor
induced on the rationalization is essentially surjective by the first hypothesis, and fully
faithful because its maps on morphisms are the localizations at the powers of `ℓ` of the maps
of `L`, which the last two hypotheses make bijective. -/
theorem Rationalization.isLocalization_of_models
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D]
    (ℓ : ℕ) (P : ObjectProperty C) [P.IsTriangulated] (Q : ObjectProperty D)
    (L : C ⥤ D) [L.CommShift ℤ] [L.IsTriangulated]
    (F : P.FullSubcategory ⥤ Q.FullSubcategory)
    (e : F ⋙ Q.ι ≅ P.ι ⋙ L)
    (hmodels : ∀ K : Q.FullSubcategory, ∃ M : P.FullSubcategory,
      Nonempty (L.obj M.obj ≅ K.obj))
    (hUnits : ∀ Y : D, IsIso (ℓ • 𝟙 Y))
    (hSurj : ∀ (A B : P.FullSubcategory) (f : L.obj A.obj ⟶ L.obj B.obj),
      ∃ (n : ℕ) (g : A ⟶ B), ℓ ^ n • f = L.map g.hom)
    (hEq : ∀ (A B : P.FullSubcategory) (f g : A.obj ⟶ B.obj), L.map f = L.map g →
      ∃ n : ℕ, ℓ ^ n • f = ℓ ^ n • g) :
    F.IsLocalization (Rationalization.W (Submonoid.powers (ℓ : ℤ)) P.FullSubcategory) := by
  have : (F ⋙ Q.ι).Additive := Functor.additive_of_iso e.symm
  have : F.Additive := Functor.additive_of_comp_faithful F Q.ι
  have : F.EssSurj := essSurj_of_subcategory_models P Q L F e hmodels
  let T := P.ι ⋙ L
  let M := Submonoid.powers (ℓ : ℤ)
  have hu (m : ℤ) (hm : m ∈ M) (Y : D) : IsIso (m • 𝟙 Y) := by
    obtain ⟨n, rfl⟩ := hm
    have : IsIso ((ℓ : ℤ) • 𝟙 Y) := by
      simpa only [natCast_zsmul] using hUnits Y
    exact scalar_power_isIso (ℓ : ℤ) Y n
  have hInvT : (Rationalization.W M P.FullSubcategory).IsInvertedBy T :=
    rationalization_inverts_of_scalar M T hu
  have hInvComp : (Rationalization.W M P.FullSubcategory).IsInvertedBy (F ⋙ Q.ι) :=
    (MorphismProperty.IsInvertedBy.iff_of_iso _ e).2 hInvT
  have hInv : (Rationalization.W M P.FullSubcategory).IsInvertedBy F := by
    intro A B f hf
    have hi : IsIso ((F ⋙ Q.ι).map f) := hInvComp f hf
    change IsIso (Q.ι.map (F.map f)) at hi
    exact isIso_of_reflects_iso (F.map f) Q.ι
  have hU (m : ℤ) (hm : m ∈ M) (Y : Q.FullSubcategory) : IsIso (m • 𝟙 Y) := by
    have : IsIso (Q.ι.map (m • 𝟙 Y)) := by
      simpa only [Functor.map_zsmul, Functor.map_id] using hu m hm (Q.ι.obj Y)
    exact isIso_of_reflects_iso _ Q.ι
  let H (A B : P.FullSubcategory) (f : F.obj A ⟶ F.obj B) :=
    (e.app A).inv ≫ f.hom ≫ (e.app B).hom
  have hMap (A B : P.FullSubcategory) (g : A ⟶ B) :
      H A B (F.map g) = L.map g.hom := by
    change e.inv.app A ≫ (F ⋙ Q.ι).map g ≫ e.hom.app B = (P.ι ⋙ L).map g
    rw [e.hom.naturality, Iso.inv_hom_id_app_assoc]
  have hSmul (A B : P.FullSubcategory) (n : ℕ) (f : F.obj A ⟶ F.obj B) :
      H A B (n • f) = n • H A B f := by
    simp only [H, show (n • f).hom = n • f.hom from rfl,
      Preadditive.comp_nsmul, Preadditive.nsmul_comp]
  have hInj (A B : P.FullSubcategory) : Function.Injective (H A B) := by
    intro f g h
    apply Q.ι.map_injective
    exact (cancel_mono (e.app B).hom).1 ((cancel_epi (e.app A).inv).1 h)
  apply rationalization_localization_of_hom M F hInv hU
  · intro A B f
    obtain ⟨n, g, hg⟩ := hSurj A B (H A B f)
    refine ⟨(ℓ : ℤ) ^ n, ⟨n, rfl⟩, g, ?_⟩
    apply hInj A B
    simpa only [← Int.natCast_pow, natCast_zsmul, hSmul, hMap] using hg
  · intro A B f g hfg
    have he : L.map f.hom = L.map g.hom := by rw [← hMap, ← hMap, hfg]
    obtain ⟨n, hn⟩ := hEq A B f.hom g.hom he
    refine ⟨(ℓ : ℤ) ^ n, ⟨n, rfl⟩, ?_⟩
    apply P.ι.map_injective
    rw [Functor.map_zsmul, Functor.map_zsmul]
    change (ℓ : ℤ) ^ n • f.hom = (ℓ : ℤ) ^ n • g.hom
    simpa only [← Int.natCast_pow, natCast_zsmul] using hn

end CategoryTheory
