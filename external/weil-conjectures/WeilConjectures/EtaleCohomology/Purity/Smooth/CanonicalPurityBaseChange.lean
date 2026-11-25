/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientation
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductAppend
public import WeilConjectures.EtaleCohomology.Purity.Smooth.WeilEquivariance
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekTensorMapUnit
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChangeMapComparison

/-!
# Compatibility of the canonical purity map with base change

For `f : X ⟶ Y` smooth separated of relative dimension `d`, the *canonical purity map*
`γ_f(K) : Lf^* K(d)[2d] ⟶ Rf^! K` (`AlgebraicGeometry.Etale.canonicalSmoothPurityMap`) is the
composite of the twist reassociation, the inverse of the canonical orientation
`θ_f : ω_f ≅ Λ_X(d)[2d]` (`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso`), the symmetry
and the canonical tensor map `ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K`
(`AlgebraicGeometry.Etale.dualizingComplexTensorMap`). Blueprint
`proposition-compatibility-purity-base-change` asserts `g'^* γ_f(K) = γ_{f'}(g^* K)` for a
cartesian square (`AlgebraicGeometry.Etale.canonicalSmoothPurityMap_baseChange`). This file
states it and derives from it, at `K = Λ_Y`, the compatibility of the canonical orientation with
base change (`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso_baseChange`).

## Main statements

- `AlgebraicGeometry.Etale.canonicalSmoothPurityMap_baseChange`
  (`proposition-compatibility-purity-base-change`).
- `AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso_baseChange`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor

-- The instances of `WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientation`.
attribute [local instance high] SymmetricCategory.toBraidedCategory

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ]

omit [CommRing Λ] [Finite Λ] [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] in
/-- The monoidal computation behind `AlgebraicGeometry.Etale.canonicalSmoothPurityMap_unit`. -/
private lemma unit_aux {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
    {A W O T : C} (e : A ⟶ 𝟙_ C) (ψ : T ⟶ A ⊗ W) (ψ₁ : W ⟶ 𝟙_ C ⊗ W) (t : T ⟶ W)
    (φ : W ⟶ O) (hn : t ≫ ψ₁ = ψ ≫ e ▷ W) (h₁ : ψ₁ ≫ (λ_ W).hom = 𝟙 _) :
    ψ ≫ A ◁ φ ≫ (β_ A O).hom ≫ O ◁ e ≫ (ρ_ O).hom = t ≫ φ := by
  rw [← BraidedCategory.braiding_naturality_left_assoc, braiding_rightUnitor,
    whisker_exchange_assoc, leftUnitor_naturality, ← reassoc_of% hn, reassoc_of% h₁]

omit [CommRing Λ] [Finite Λ] [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] in
/-- The monoidal computation behind
`AlgebraicGeometry.Etale.canonicalSmoothPurityMap_naturality`. -/
private lemma nat_aux {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
    {A A' W O T T' R R' : C} (v : A ⟶ A') (ψ : T ⟶ A ⊗ W) (ψ' : T' ⟶ A' ⊗ W) (t : T ⟶ T')
    (φ : W ⟶ O) (τ : O ⊗ A ⟶ R) (τ' : O ⊗ A' ⟶ R') (r : R ⟶ R')
    (hn : t ≫ ψ' = ψ ≫ v ▷ W) (hτ : τ ≫ r = O ◁ v ≫ τ') :
    (ψ ≫ A ◁ φ ≫ (β_ A O).hom ≫ τ) ≫ r = t ≫ ψ' ≫ A' ◁ φ ≫ (β_ A' O).hom ≫ τ' := by
  rw [reassoc_of% hn, Category.assoc, Category.assoc, Category.assoc, hτ,
    ← BraidedCategory.braiding_naturality_left_assoc, whisker_exchange_assoc]

section Map

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f] [IsSeparated f]
  [HasCompactification f] [HasInvertibleExponent Λ X] {k : Type u} [Field k]
  (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]

/-- The canonical purity map `γ_f(K) : Lf^* K(d)[2d] ⟶ Rf^! K`:
`Lf^* K(d)[2d] ≅ Lf^* K ⊗ᴸ Λ_X(d)[2d] ≅ Lf^* K ⊗ᴸ ω_f ≅ ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K`, through the
canonical orientation `θ_f` (`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso`) and the
canonical tensor map (`AlgebraicGeometry.Etale.dualizingComplexTensorMap`). -/
noncomputable def canonicalSmoothPurityMap
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) ⟶ (R(f)^![Λ]).obj K :=
  (twistShiftObjIso Λ X d _).hom ≫
    ((derivedTensor _ X).obj _).map (dualizingComplexTwistShiftIso Λ f d aY).inv ≫
      (derivedTensorBraidingIso _ X _ _).hom ≫ dualizingComplexTensorMap Λ f K

/-- At `K = Λ_Y`, the canonical purity map is the inverse of the canonical orientation, read
through `Lf^* Λ_Y ≅ Λ_X`. -/
lemma canonicalSmoothPurityMap_unit :
    canonicalSmoothPurityMap Λ f d aY (𝟙_ _) =
      (twistShift Λ X d).map (leftDerivedUpperStarUnitIso _ f).hom ≫
        (dualizingComplexTwistShiftIso Λ f d aY).inv := by
  let := _root_.DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  have hT : dualizingComplexTensorMap Λ f (𝟙_ _) =
      dualizingComplex Λ f ◁ (leftDerivedUpperStarUnitIso _ f).hom ≫ (ρ_ _).hom :=
    lowerShriekRightAdjointUnitTensorMap_unit (rightDerivedUpperShriekAdjunction Λ f)
  have hβ (M N : DerivedCategoryModule Λ X) :
      (derivedTensorBraidingIso _ X M N).hom = (β_ M N).hom := rfl
  -- `Λ_X(d)[2d] ≅ Λ_X ⊗ᴸ Λ_X(d)[2d] ⟶ Λ_X(d)[2d]` is the identity
  have h1 : (twistShiftObjIso Λ X d (𝟙_ _)).hom ≫ (λ_ _).hom = 𝟙 _ := by
    have hc := derivedTensorLeftUnitor_commShift (A := ModuleCat.{u + 1} Λ) (X := X)
      (tateObject Λ X d) (2 * d)
    simp only [twistShiftObjIso, twistShiftConstantComplexIso, Iso.trans_hom, Iso.symm_hom,
      Iso.app_inv, Category.assoc]
    change _ ≫ 𝟙_ _ ◁ ((λ_ (tateObject Λ X d)).inv)⟦2 * (d : ℤ)⟧' ≫ _ = _
    rw [leftUnitor_naturality]
    erw [← reassoc_of% hc]
    rw [Iso.inv_hom_id_app_assoc, ← Functor.map_comp]
    erw [Iso.hom_inv_id, CategoryTheory.Functor.map_id]
    rfl
  have hn := twistShiftObjIso_hom_naturality Λ (d : ℤ) (leftDerivedUpperStarUnitIso _ f).hom
  rw [canonicalSmoothPurityMap, hT, hβ]
  change _ ≫ _ ◁ _ ≫ _ = _
  exact unit_aux (leftDerivedUpperStarUnitIso _ f).hom (twistShiftObjIso Λ X d _).hom
    (twistShiftObjIso Λ X d (𝟙_ _)).hom
    ((twistShift Λ X d).map (leftDerivedUpperStarUnitIso _ f).hom)
    (dualizingComplexTwistShiftIso Λ f d aY).inv hn h1

/-- The canonical purity map is natural in `K`. -/
lemma canonicalSmoothPurityMap_naturality
    {K K' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ K') :
    canonicalSmoothPurityMap Λ f d aY K ≫ (R(f)^![Λ]).map φ =
      (twistShift Λ X d).map ((L((f)^*[ModuleCat.{u + 1} Λ])).map φ) ≫
        canonicalSmoothPurityMap Λ f d aY K' := by
  let := _root_.DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  have hT :=
    lowerShriekRightAdjointUnitTensorMap_naturality (rightDerivedUpperShriekAdjunction Λ f) φ
  have hn := twistShiftObjIso_hom_naturality Λ (d : ℤ) ((L((f)^*[ModuleCat.{u + 1} Λ])).map φ)
  exact nat_aux _ _ _ _ _ _ _ _ hn hT

end Map

section TwistShift

variable {X Y : Scheme.{u}} [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]

omit [Finite Λ] [HasKummerClass.IsNormalized Λ] in
/-- The identification `Lf^*(K(m)[2m]) ≅ (Lf^* K)(m)[2m]`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarTwistShiftIso`) is natural in `K`. -/
@[reassoc]
lemma leftDerivedUpperStarTwistShiftIso_hom_naturality (f : X ⟶ Y) (m : ℤ)
    {K K' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (v : K ⟶ K') :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map ((twistShift Λ Y m).map v) ≫
        (leftDerivedUpperStarTwistShiftIso Λ f m K').hom =
      (leftDerivedUpperStarTwistShiftIso Λ f m K).hom ≫
        (twistShift Λ X m).map ((L((f)^*[ModuleCat.{u + 1} Λ])).map v) := by
  simp only [leftDerivedUpperStarTwistShiftIso, twistShift, tateTwist, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, Functor.comp_map, Functor.flip_obj_map, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  rw [reassoc_of% leftDerivedUpperStarTensorIso_hom_naturality_left, Category.assoc,
    NatTrans.naturality]

end TwistShift

section BaseChange

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (d : ℕ) [SmoothOfRelativeDimension d f]
  [SmoothOfRelativeDimension d f'] [IsSeparated f] [IsSeparated f'] [HasCompactification f]
  [HasCompactification f'] [QuasiCompact f'] [HasInvertibleExponent Λ X]
  [HasInvertibleExponent Λ X'] {k k' : Type u} [Field k] [Field k']

/-- Blueprint `proposition-compatibility-purity-base-change` (formerly
`proposition-compatibility-purity-base-change`, `chap-Smooth-purity`): compatibility of purity with
base change.

For a cartesian square `g' ≫ f = f' ≫ g` with `f` and `f'` smooth separated of relative
dimension `d` and `K ∈ D(Y_ét, Λ)`, identify the sources of the canonical purity maps by
`Lg'^* Lf^* ≅ Lf'^* Lg^*` (`AlgebraicGeometry.Etale.leftDerivedUpperStarTwistShiftBaseChangeIso`)
and the targets by the exceptional base change map
(`AlgebraicGeometry.Etale.upperShriekBaseChangeMap`). Then `g'^* γ_f(K) = γ_{f'}(g^* K)`. -/
theorem canonicalSmoothPurityMap_baseChange (sq : IsPullback g' f' f g)
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    (aY' : Y' ⟶ Spec (.of k')) [IsSeparated aY'] [LocallyOfFiniteType aY']
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((g')^*[ModuleCat.{u + 1} Λ])).map (canonicalSmoothPurityMap Λ f d aY K) ≫
        (upperShriekBaseChangeMap Λ sq).app K =
      (leftDerivedUpperStarTwistShiftBaseChangeIso Λ d f sq.toCommSq K).hom ≫
        canonicalSmoothPurityMap Λ f' d aY' ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K) :=
  sorry

/-- Blueprint `proposition-compatibility-purity-base-change`, the orientation part: the canonical
orientations `θ_f : Rf^! Λ_Y ≅ Λ_X(d)[2d]` and `θ_{f'}`
(`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso`) are compatible with the exceptional base
change `Lg'^* Rf^! ⟶ Rf'^! Lg^*` and the pullback of the Tate twist. This is the case
`K = Λ_Y` of `AlgebraicGeometry.Etale.canonicalSmoothPurityMap_baseChange`. -/
theorem dualizingComplexTwistShiftIso_baseChange (sq : IsPullback g' f' f g)
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    (aY' : Y' ⟶ Spec (.of k')) [IsSeparated aY'] [LocallyOfFiniteType aY'] :
    (upperShriekBaseChangeMap Λ sq).app (constantComplex Λ Y) ≫
        (R(f')^![Λ]).map (leftDerivedUpperStarUnitIso _ g).hom ≫
          (dualizingComplexTwistShiftIso Λ f' d aY').hom =
      (L((g')^*[ModuleCat.{u + 1} Λ])).map (dualizingComplexTwistShiftIso Λ f d aY).hom ≫
        (leftDerivedUpperStarTwistShiftIso Λ g' d (constantComplex Λ X)).hom ≫
          (twistShift Λ X' d).map (leftDerivedUpperStarUnitIso _ g').hom := by
  -- the units of the two factorizations of `g' ≫ f = f' ≫ g`
  have hε : (L((g')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarUnitIso _ f).hom ≫
      (leftDerivedUpperStarUnitIso _ g').hom =
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) g' f (g' ≫ f) rfl).inv.app _ ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f' g (g' ≫ f) sq.w).hom.app _) ≫
          (L((f')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarUnitIso _ g).hom ≫
            (leftDerivedUpperStarUnitIso _ f').hom := by
    have h₁ := congrArg Iso.hom (leftDerivedUpperStarConstantComplexIso_comp Λ g' f _ rfl)
    have h₂ := congrArg Iso.hom (leftDerivedUpperStarConstantComplexIso_comp Λ f' g _ sq.w)
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at h₁ h₂
    have hu {S T : Scheme.{u}} (h : S ⟶ T) : (leftDerivedUpperStarUnitIso _ h).hom =
        (leftDerivedUpperStarConstantComplexIso Λ h).hom :=
      leftDerivedUpperStarUnitIso_hom_eq_η h
    rw [hu, hu, hu, hu, Category.assoc]
    erw [← h₂, h₁, Iso.inv_hom_id_app_assoc]
  have hnode := canonicalSmoothPurityMap_baseChange Λ d sq aY aY' (𝟙_ _)
  have hnat := canonicalSmoothPurityMap_naturality Λ f' d aY' (leftDerivedUpperStarUnitIso _ g).hom
  have htsi := leftDerivedUpperStarTwistShiftIso_hom_naturality Λ g' d
    (leftDerivedUpperStarUnitIso _ f).hom
  rw [canonicalSmoothPurityMap_unit] at hnode hnat
  rw [← cancel_epi ((L((g')^*[ModuleCat.{u + 1} Λ])).map ((twistShift Λ X d).map
    (leftDerivedUpperStarUnitIso _ f).hom ≫ (dualizingComplexTwistShiftIso Λ f d aY).inv))]
  erw [reassoc_of% hnode]
  rw [reassoc_of% hnat, Iso.inv_hom_id, Category.comp_id, Functor.map_comp, Category.assoc,
    ← Functor.map_comp_assoc (L((g')^*[ModuleCat.{u + 1} Λ]))
      (dualizingComplexTwistShiftIso Λ f d aY).inv, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [reassoc_of% htsi]
  simp only [leftDerivedUpperStarTwistShiftBaseChangeIso, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc, ← Functor.map_comp]
  rw [hε]
  simp only [Iso.app_hom, Iso.symm_hom, Iso.app_inv, Category.assoc]

end BaseChange

end AlgebraicGeometry.Etale
