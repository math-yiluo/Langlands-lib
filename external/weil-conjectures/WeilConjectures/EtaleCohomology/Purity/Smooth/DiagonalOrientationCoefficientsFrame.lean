/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationCoefficientsTensor
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsAssoc

/-!
# Frame classes under a change of coefficients

Let `Ψ : D(X_ét, Λ) ⥤ D(X_ét, Λ')` be a change of coefficients with its comparisons with `Le^*`,
`Ri_!` and `Ri^!` (`AlgebraicGeometry.Etale.SupportedCoefficientChange`). The compatibility of
the fundamental class, of the purity isomorphism of a section and of the canonical orientation
with `Ψ` (`SupportedCoefficientChange.mapSupportedClass_thomFundamentalClass` and its
consequences, blueprint `proposition-compatibility-purity-change-coefficients`) assume the
hypothesis `hframe`: `Ψ` carries the frame class `∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_c)` over `Λ`
(`AlgebraicGeometry.Etale.frameClass`) of every frame to the frame class over `Λ'`.

This file reduces `hframe` to compatibilities of `Ψ` with the three operations out of which the
frame classes are built (`AlgebraicGeometry.Etale.kummerBoundaryProduct`):

* the unit class `Λ_U ≅ Λ_U(0)[0]` supported everywhere;
* the Kummer boundaries `∂κ(f) ∈ H²_{V(f)}(U, Λ(1))`;
* the cup product with supports `AlgebraicGeometry.Etale.cupWithSupportsTateObject`.

These are bundled in `SupportedCoefficientChange.PreservesKummerBoundaries`, and
`SupportedCoefficientChange.PreservesKummerBoundaries.mapSupportedClass_frameClass` is `hframe`.
The last two compatibilities are in turn reduced to more basic ones:

* the Kummer boundary `∂κ(f)` is the boundary of the supported localization triangle of
  `V(f) ⊂ U` applied to the Kummer class `κ(f) ∈ H¹(U_f, Λ(1))`
  (`AlgebraicGeometry.Etale.localizationBoundaryClass`); so `Ψ` preserves Kummer boundaries as
  soon as it commutes with these boundaries and preserves the Kummer classes, i.e. carries the
  Kummer datum of `Λ` to that of `Λ'`
  (`SupportedCoefficientChange.mapSupportedClass_kummerBoundary`). For the reduction
  `𝒪_E/ℓ^{n+1} ⟶ 𝒪_E/ℓⁿ` with the canonical Kummer classes this is the compatibility of the
  Kummer sequences under `μ_{ℓ^{n+1}} ⟶ μ_{ℓⁿ}`;
* for a monoidal change of coefficients (`MonoidalSupportedCoefficientChange`) the cup product
  with supports is preserved as soon as the diagonal `Λ_U ⟶ Λ_U ⊗ᴸ Λ_U` and
  the multiplication `Λ(m)[2m] ⊗ᴸ Λ(m')[2m'] ≅ Λ(m + m')[2(m + m')]` of the twists are
  (`MonoidalSupportedCoefficientChange.mapSupportedClass_cupWithSupportsTateObject`).

## Main definitions

- `AlgebraicGeometry.Etale.localizationBoundaryClass`: the boundary
  `H¹(U_f, Λ(1)) ⟶ H²_{V(f)}(U, Λ(1))` of the supported localization triangle, on classes.
- `AlgebraicGeometry.Etale.SupportedCoefficientChange.PreservesKummerBoundaries`: the
  compatibilities of a change of coefficients with the constituents of the frame classes.

## Main statements

In the namespace `AlgebraicGeometry.Etale`:

- `SupportedCoefficientChange.PreservesKummerBoundaries.mapSupportedClass_kummerBoundaryProduct`,
  `SupportedCoefficientChange.PreservesKummerBoundaries.mapSupportedClass_frameClass`: the change
  of coefficients carries the frame classes over `Λ` to the frame classes over `Λ'`.
- `MonoidalSupportedCoefficientChange.preservesKummerBoundaries`: a monoidal change of
  coefficients preserving the unit class, the diagonal, the multiplication of the twists, the
  Kummer classes and the localization boundaries preserves Kummer boundaries.
- `map_dualizingComplexTwistShiftIso_of_preservesKummerBoundaries` (in the namespace
  `MonoidalSupportedCoefficientChange`): the canonical orientation is compatible with such a
  change of coefficients.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the definitions of
-- the derived tensor product, of the tensor maps of `R^!` and of the section invariant.
attribute [local instance high] SymmetricCategory.toBraidedCategory

attribute [local instance] HasInvertibleExponent.opens

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

/-- The defining property of the lift of a morphism along a surjective closed immersion: its
composite with the counit of `Ri_! ⊣ Ri^!` is the morphism. -/
@[reassoc]
lemma liftCounitOfRangeEqUniv_comp_counit (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U Z : Scheme.{u}} (i : Z ⟶ U) [IsClosedImmersion i] (hi : Set.range i.base = Set.univ)
    {K L : 𝐃(U, Λ)} (φ : K ⟶ L) :
    liftCounitOfRangeEqUniv Λ i hi φ ≫ (rightDerivedUpperShriekAdjunction Λ i).counit.app L = φ :=
  (existsUnique_comp_counit_of_range_eq_univ Λ i hi φ).exists.choose_spec

namespace SupportedCoefficientChange

section Supports

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [Finite Λ] [CommRing Λ'] [Finite Λ']
  [HasTateTwist Λ] [HasTateTwist Λ'] (Φ : SupportedCoefficientChange Λ Λ')

variable {U Z : Scheme.{u}} (i : Z ⟶ U) [IsClosedImmersion i]

/-- The comparison of supports `Ψ(Ri_! Ri^! L) ⟶ Ri_! Ri^! L'` is natural in `L`. -/
@[reassoc]
lemma map_map_comp_supportsMap {L₁ L₂ : 𝐃(U, Λ)} {L₁' L₂' : 𝐃(U, Λ')} (φ : L₁ ⟶ L₂)
    (φ' : L₁' ⟶ L₂') (τ₁ : (Φ.functor U).obj L₁ ≅ L₁') (τ₂ : (Φ.functor U).obj L₂ ≅ L₂')
    (h : (Φ.functor U).map φ ≫ τ₂.hom = τ₁.hom ≫ φ') :
    (Φ.functor U).map ((R(i)_![ModuleCat.{u + 1} Λ]).map ((R(i)^![Λ]).map φ)) ≫
        Φ.supportsMap i τ₂ =
      Φ.supportsMap i τ₁ ≫ (R(i)_![ModuleCat.{u + 1} Λ']).map ((R(i)^![Λ']).map φ') := by
  have hn := (Φ.lowerShriekIso i).hom.naturality ((R(i)^![Λ]).map φ)
  have hu := (Φ.upperShriekMap i).naturality φ
  simp only [Functor.comp_obj, Functor.comp_map] at hn hu
  rw [supportsMap, supportsMap, reassoc_of% hn, Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp, reassoc_of% hu, ← Functor.map_comp, h]
  simp

/-- The change of coefficients of a class with supports followed by a change of coefficients
`L' ⟶ L'₂` is the change of coefficients of the composite class. -/
lemma mapSupportedClass_comp {X : Scheme.{u}} {Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    {L₁ L₂ : 𝐃(X, Λ)} {L₁' L₂' : 𝐃(X, Λ')} (φ : L₁ ⟶ L₂) (φ' : L₁' ⟶ L₂')
    (τ₁ : (Φ.functor X).obj L₁ ≅ L₁') (τ₂ : (Φ.functor X).obj L₂ ≅ L₂')
    (h : (Φ.functor X).map φ ≫ τ₂.hom = τ₁.hom ≫ φ')
    (γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L₁)) :
    Φ.mapSupportedClass i τ₂ (γ ≫ (R(i)_![ModuleCat.{u + 1} Λ]).map ((R(i)^![Λ]).map φ)) =
      Φ.mapSupportedClass i τ₁ γ ≫ (R(i)_![ModuleCat.{u + 1} Λ']).map ((R(i)^![Λ']).map φ') := by
  simp only [mapSupportedClass, Functor.map_comp, Category.assoc]
  rw [Φ.map_map_comp_supportsMap i φ φ' τ₁ τ₂ h]

/-- The change of coefficients of a class with supports `γ`, preceded by `Ψ Λ_X ≅ Λ'_X`, is
`Ψ γ` followed by the comparison of supports. -/
@[reassoc]
lemma constantComplexIso_hom_comp_mapSupportedClass {L : 𝐃(U, Λ)} {L' : 𝐃(U, Λ')}
    (τ : (Φ.functor U).obj L ≅ L')
    (γ : constantComplex Λ U ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) :
    (Φ.constantComplexIso U).hom ≫ Φ.mapSupportedClass i τ γ =
      (Φ.functor U).map γ ≫ Φ.supportsMap i τ := by
  rw [mapSupportedClass, Iso.hom_inv_id_assoc]

/-- The change of coefficients of a class with supports, followed by the counit of
`Ri_! ⊣ Ri^!`, is the change of coefficients of the class followed by the counit. -/
@[reassoc]
lemma mapSupportedClass_comp_counit {L : 𝐃(U, Λ)} {L' : 𝐃(U, Λ')}
    (τ : (Φ.functor U).obj L ≅ L')
    (γ : constantComplex Λ U ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) :
    Φ.mapSupportedClass i τ γ ≫ (rightDerivedUpperShriekAdjunction Λ' i).counit.app L' =
      (Φ.constantComplexIso U).inv ≫
        (Φ.functor U).map (γ ≫ (rightDerivedUpperShriekAdjunction Λ i).counit.app L) ≫ τ.hom := by
  rw [mapSupportedClass, Category.assoc, Category.assoc, supportsMap_comp_counit,
    Functor.map_comp_assoc]

/-- The change of coefficients of a class supported everywhere is the class supported
everywhere lifting the change of coefficients of the underlying class
(`AlgebraicGeometry.Etale.liftCounitOfRangeEqUniv`). -/
lemma mapSupportedClass_liftCounitOfRangeEqUniv (hi : Set.range i.base = Set.univ)
    {L : 𝐃(U, Λ)} {L' : 𝐃(U, Λ')} (τ : (Φ.functor U).obj L ≅ L')
    (φ : constantComplex Λ U ⟶ L) :
    Φ.mapSupportedClass i τ (liftCounitOfRangeEqUniv Λ i hi φ) =
      liftCounitOfRangeEqUniv Λ' i hi
        ((Φ.constantComplexIso U).inv ≫ (Φ.functor U).map φ ≫ τ.hom) :=
  (existsUnique_comp_counit_of_range_eq_univ Λ' i hi _).unique
    (by rw [mapSupportedClass_comp_counit, liftCounitOfRangeEqUniv_comp_counit])
    (liftCounitOfRangeEqUniv_comp_counit Λ' i hi _)

/-- Reindexing the twist of a class with supports along an equality `m = m'` commutes with the
change of coefficients. -/
lemma mapSupportedClass_comp_eqToHom {X : Scheme.{u}} [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ' X] {i : Z ⟶ X} [IsClosedImmersion i] {m m' : ℤ} (h : m = m')
    (γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![Λ]).obj ((tateObject Λ X m)⟦2 * m⟧))) :
    Φ.mapSupportedClass i (Φ.tateShiftIso X m') (γ ≫ eqToHom (by rw [h])) =
      Φ.mapSupportedClass i (Φ.tateShiftIso X m) γ ≫ eqToHom (by rw [h]) := by
  subst h
  simp

end Supports

end SupportedCoefficientChange

section Boundary

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]

variable {U : Scheme.{u}} [HasInvertibleExponent Λ U] (f : Γ(U, ⊤))

/-- The boundary `H¹(U_f, Λ(1)) ⟶ H²_{V(f)}(U, Λ(1))` of the supported localization triangle of
`V(f) ⊂ U`, on classes: a class `α : Λ_{U_f} ⟶ Λ_{U_f}(1)[1]`, read through
`Lj^* Λ_U ≅ Λ_{U_f}` and `Lj^* Λ_U(1) ≅ Λ_{U_f}(1)`, is adjoint under `Lj^* ⊣ Rj_*` to a class
`Λ_U ⟶ (Rj_* Lj^* Λ_U(1))[1]`, which the boundary
`δ : Rj_* Lj^* Λ_U(1) ⟶ (Ri_! Ri^! Λ_U(1))[1]`
(`AlgebraicGeometry.Etale.supportedLocalizationBoundary`) carries to
`Λ_U ⟶ (Ri_! Ri^! Λ_U(1))[2]`. For the Kummer class `κ(f|_{U_f})` it is the Kummer boundary
`∂κ(f)` (`AlgebraicGeometry.Etale.kummerBoundary_eq_localizationBoundaryClass`). -/
noncomputable def localizationBoundaryClass
    (α : constantComplex Λ (U.basicOpen f) ⟶ (tateObject Λ (U.basicOpen f) 1)⟦(1 : ℤ)⟧) :
    constantComplex Λ U ⟶
      ((R(U.zeroLocusSubschemeι {f})_![ModuleCat.{u + 1} Λ]).obj
        ((R(U.zeroLocusSubschemeι {f})^![Λ]).obj (tateObject Λ U 1)))⟦(2 : ℤ)⟧ :=
  ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (U.basicOpen f).ι).homEquiv _ _
      ((leftDerivedUpperStarConstantComplexIso Λ (U.basicOpen f).ι).hom ≫ α ≫
          (leftDerivedUpperStarTateObjectIso (U.basicOpen f).ι 1).inv⟦(1 : ℤ)⟧')) ≫
    ((R(((U.basicOpen f).ι)_*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app _ ≫
      (supportedLocalizationBoundary Λ _ _
        (range_zeroLocusSubschemeι_singleton f) (tateObject Λ U 1))⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd' _ (1 : ℤ) 1 2 rfl).inv.app _

end Boundary

/-- The Kummer boundary `∂κ(f)` is the localization boundary of the Kummer class
`κ(f|_{U_f}) ∈ H¹(U_f, Λ(1))`. -/
lemma kummerBoundary_eq_localizationBoundaryClass (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [HasKummerClass Λ] {U : Scheme.{u}} [HasInvertibleExponent Λ U] (f : Γ(U, ⊤)) :
    kummerBoundary Λ f = localizationBoundaryClass Λ f (kummerClass Λ (U.basicOpenUnit f)) :=
  rfl

namespace SupportedCoefficientChange

section Kummer

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [Finite Λ] [CommRing Λ'] [Finite Λ']
  [HasKummerClass Λ] [HasKummerClass Λ'] (Φ : SupportedCoefficientChange Λ Λ')

/-- **The change of coefficients of a Kummer boundary is the Kummer boundary.** Let
`ρ X : Ψ(Λ_X(1)[1]) ≅ Λ'_X(1)[1]` identify the coefficients of the Kummer classes. If
* `hκ`: the change of coefficients carries the Kummer classes `κ(u)` over `Λ` to the Kummer
  classes over `Λ'` (the Kummer datum of `Λ` maps to that of `Λ'`), and
* `hδ`: it commutes with the boundary of the supported localization triangle of `V(f) ⊂ U` on
  classes (`AlgebraicGeometry.Etale.localizationBoundaryClass`),

then it carries `∂κ(f) ∈ H²_{V(f)}(U, Λ(1))` to `∂κ(f) ∈ H²_{V(f)}(U, Λ'(1))`. -/
theorem mapSupportedClass_kummerBoundary
    (ρ : ∀ (X : Scheme.{u}) [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X],
      (Φ.functor X).obj ((tateObject Λ X 1)⟦(1 : ℤ)⟧) ≅ (tateObject Λ' X 1)⟦(1 : ℤ)⟧)
    (hκ : ∀ (X : Scheme.{u}) [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X]
      (v : Γ(X, ⊤)ˣ), (Φ.functor X).map (kummerClass Λ v) ≫ (ρ X).hom =
        (Φ.constantComplexIso X).hom ≫ kummerClass Λ' v)
    {U : Scheme.{u}} [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ' U] (f : Γ(U, ⊤))
    (hδ : ∀ α : constantComplex Λ (U.basicOpen f) ⟶ (tateObject Λ (U.basicOpen f) 1)⟦(1 : ℤ)⟧,
      Φ.mapSupportedClass _ (Φ.tateShiftIso U 1)
          (shiftSupportedClass Λ _ 2 (localizationBoundaryClass Λ f α)) =
        shiftSupportedClass Λ' _ 2 (localizationBoundaryClass Λ' f
          ((Φ.constantComplexIso _).inv ≫ (Φ.functor _).map α ≫ (ρ _).hom))) :
    Φ.mapSupportedClass _ (Φ.tateShiftIso U 1) (shiftSupportedClass Λ _ 2 (kummerBoundary Λ f)) =
      shiftSupportedClass Λ' _ 2 (kummerBoundary Λ' f) := by
  rw [kummerBoundary_eq_localizationBoundaryClass, hδ, hκ, Iso.inv_hom_id_assoc,
    kummerBoundary_eq_localizationBoundaryClass]

end Kummer

section FrameClass

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [Finite Λ] [CommRing Λ'] [Finite Λ']
  [HasKummerClass Λ] [HasKummerClass Λ'] (Φ : SupportedCoefficientChange Λ Λ')

/-- Blueprint `proposition-compatibility-purity-change-coefficients`: change of coefficients in
purity

A change of coefficients *preserves Kummer boundaries* if it is compatible with the three
constituents of the iterated cup products of Kummer boundaries
`∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_n)` (`AlgebraicGeometry.Etale.kummerBoundaryProduct`), out of which the
frame classes are built:
* the unit class `Λ_U ≅ Λ_U(0) ≅ Λ_U(0)[0]`, through `Ψ Λ_U ≅ Λ'_U` and
  `Ψ(Λ_U(0)[0]) ≅ Λ'_U(0)[0]`;
* the Kummer boundaries `∂κ(f) ∈ H²_{V(f)}(U, Λ(1))` (see
  `AlgebraicGeometry.Etale.SupportedCoefficientChange.mapSupportedClass_kummerBoundary` for a
  reduction to the Kummer classes and the localization boundaries);
* the cup product with supports `AlgebraicGeometry.Etale.cupWithSupportsTateObject` (see
  `MonoidalSupportedCoefficientChange.mapSupportedClass_cupWithSupportsTateObject`
  for a monoidal change of coefficients). -/
structure PreservesKummerBoundaries : Prop where
  /-- The change of coefficients carries the unit class `Λ_U ≅ Λ_U(0)[0]` to the unit class. -/
  map_unitClass (U : Scheme.{u}) [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ' U] :
    (Φ.functor U).map ((HasTateTwist.twistObjectZeroIso (Λ := Λ) U).inv ≫
        (shiftFunctorZero' _ (2 * (0 : ℤ)) (by simp)).inv.app _) ≫ (Φ.tateShiftIso U 0).hom =
      (Φ.constantComplexIso U).hom ≫ (HasTateTwist.twistObjectZeroIso (Λ := Λ') U).inv ≫
        (shiftFunctorZero' _ (2 * (0 : ℤ)) (by simp)).inv.app _
  /-- The change of coefficients carries the Kummer boundaries to the Kummer boundaries. -/
  mapSupportedClass_kummerBoundary {U : Scheme.{u}} [HasInvertibleExponent Λ U]
    [HasInvertibleExponent Λ' U] (f : Γ(U, ⊤)) :
    Φ.mapSupportedClass _ (Φ.tateShiftIso U 1) (shiftSupportedClass Λ _ 2 (kummerBoundary Λ f)) =
      shiftSupportedClass Λ' _ 2 (kummerBoundary Λ' f)
  /-- The change of coefficients commutes with the cup product with supports. -/
  mapSupportedClass_cupWithSupportsTateObject {U Z₁ Z₂ Z : Scheme.{u}}
    [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ' U] (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U)
    (i : Z ⟶ U) [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base) (m m' : ℤ)
    (α : constantComplex Λ U ⟶ (R(i₁)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₁)^![Λ]).obj ((tateObject Λ U m)⟦2 * m⟧)))
    (β : constantComplex Λ U ⟶ (R(i₂)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₂)^![Λ]).obj ((tateObject Λ U m')⟦2 * m'⟧))) :
    Φ.mapSupportedClass i (Φ.tateShiftIso U (m + m')) (cupWithSupportsTateObject Λ i₁ i₂ i h α β) =
      cupWithSupportsTateObject Λ' i₁ i₂ i h (Φ.mapSupportedClass i₁ (Φ.tateShiftIso U m) α)
        (Φ.mapSupportedClass i₂ (Φ.tateShiftIso U m') β)

namespace PreservesKummerBoundaries

variable {Φ}

/-- **The change of coefficients of `∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_n)` is `∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_n)`**, for a
change of coefficients preserving Kummer boundaries, by induction on `n`. -/
theorem mapSupportedClass_kummerBoundaryProduct (hΦ : Φ.PreservesKummerBoundaries)
    {U : Scheme.{u}} [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ' U] {n : ℕ}
    (f : Fin n → Γ(U, ⊤)) :
    Φ.mapSupportedClass _ (Φ.tateShiftIso U n) (kummerBoundaryProduct Λ f) =
      kummerBoundaryProduct Λ' f := by
  induction n with
  | zero =>
    rw [kummerBoundaryProduct, kummerBoundaryProduct, mapSupportedClass_liftCounitOfRangeEqUniv]
    congr 1
    exact (Iso.inv_comp_eq _).2 (hΦ.map_unitClass U)
  | succ n ih =>
    rw [kummerBoundaryProduct, kummerBoundaryProduct, mapSupportedClass_comp_eqToHom _
      (by rw [Nat.cast_succ, add_comm (1 : ℤ)]), hΦ.mapSupportedClass_cupWithSupportsTateObject,
      hΦ.mapSupportedClass_kummerBoundary, ih]

/-- Blueprint `proposition-compatibility-purity-change-coefficients`: change of coefficients in
purity

**A change of coefficients preserving Kummer boundaries carries frame classes to frame
classes**: for every frame `(e : U ⟶ X, f₁, …, f_c)` of a closed immersion, the change of
coefficients of `∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_c)` over `Λ` is `∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_c)` over `Λ'`. This is
the hypothesis `hframe` of
`AlgebraicGeometry.Etale.SupportedCoefficientChange.mapSupportedClass_thomFundamentalClass` and
its consequences. -/
theorem mapSupportedClass_frameClass (hΦ : Φ.PreservesKummerBoundaries) {X Z : Scheme.{u}}
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X] {c : ℕ} {i : Z ⟶ X}
    (F : i.EtaleFrame c) :
    Φ.mapSupportedClass _ (Φ.tateShiftIso F.U c) (frameClass Λ F) = frameClass Λ' F :=
  hΦ.mapSupportedClass_kummerBoundaryProduct F.f

end PreservesKummerBoundaries

end FrameClass

end SupportedCoefficientChange

section SupportedTensor

/-- The tensor product `f ⊗ g` of morphisms of `D(X_ét, Λ)`, written as `f ⊗ 1` followed by
`1 ⊗ g`. -/
@[reassoc]
lemma map_app_comp_map_eq_derivedTensorHom (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    {K K₁ M M₁ : 𝐃(X, Λ)} (f : K ⟶ K₁) (g : M ⟶ M₁) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).map f).app M ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K₁).map g =
      derivedTensorHom (ModuleCat.{u + 1} Λ) f g :=
  rfl

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Let `i₁ : Z₁ ⟶ U`, `i₂ : Z₂ ⟶ U` and `i : Z ⟶ U` be closed immersions with `Z = Z₁ ∩ Z₂`
and `j` the open complement of `Z`. Then `Lj^*(Ri₁_! P ⊗ᴸ Ri₂_! Q) = 0`: it restricts to zero on
the complements of `Z₁` and of `Z₂`, which cover the source of `j`. -/
lemma isZero_leftDerivedUpperStar_openComplement_derivedTensor_rightDerivedLowerShriek_of_inter
    {U Z₁ Z₂ Z : Scheme.{u}} (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U) [IsClosedImmersion i₁]
    [IsClosedImmersion i₂] [IsClosedImmersion i]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base) (P : 𝐃(Z₁, Λ))
    (Q : 𝐃(Z₂, Λ)) :
    IsZero ((L((i.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj
      (((derivedTensor (ModuleCat.{u + 1} Λ) U).obj ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj P)).obj
        ((R(i₂)_![ModuleCat.{u + 1} Λ]).obj Q))) := by
  set j := i.openComplement.ι
  have hcd : Disjoint (Set.range (pullback.snd i₁ j)) (Set.range (pullback.snd i₂ j)) := by
    rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, Set.disjoint_left]
    intro x hx₁ hx₂
    apply x.2
    rw [h]
    exact ⟨hx₁, hx₂⟩
  refine isZero_of_isZero_leftDerivedUpperStar_of_disjoint Λ (pullback.snd i₁ j)
    (pullback.snd i₂ j) _ _ (Scheme.Hom.range_eq_compl_range_openComplement_ι _)
    (Scheme.Hom.range_eq_compl_range_openComplement_ι _) hcd ?_ ?_
  · refine IsZero.of_iso ?_ ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) _ j).app _).symm
    exact (isZero_derivedTensor_obj_obj_of_isZero_left
      (isZero_leftDerivedUpperStar_openComplement_comp_obj_rightDerivedLowerShriek
        (ModuleCat.{u + 1} Λ) i₁ j _)
        _).of_iso (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) _ _ _)
  · refine IsZero.of_iso ?_ ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) _ j).app _).symm
    exact (isZero_derivedTensor_obj_obj_of_isZero_right _
      (isZero_leftDerivedUpperStar_openComplement_comp_obj_rightDerivedLowerShriek
        (ModuleCat.{u + 1} Λ) i₂ j _)).of_iso
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) _ _ _)

end SupportedTensor

namespace MonoidalSupportedCoefficientChange

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [Finite Λ] [CommRing Λ'] [Finite Λ']

section Tensor

variable [HasTateTwist Λ] [HasTateTwist Λ'] (Φ : MonoidalSupportedCoefficientChange Λ Λ')

/-- The comparison `Ψ(P ⊗ᴸ A) ⟶ P' ⊗ᴸ A'` followed by a tensor product of morphisms. -/
@[reassoc]
lemma tensorMap_comp_derivedTensorHom {X : Scheme.{u}} {P A : 𝐃(X, Λ)}
    {P' A' P'' A'' : 𝐃(X, Λ')} (vP : (Φ.functor X).obj P ⟶ P') (vA : (Φ.functor X).obj A ⟶ A')
    (f : P' ⟶ P'') (g : A' ⟶ A'') :
    Φ.tensorMap vP vA ≫ derivedTensorHom (ModuleCat.{u + 1} Λ') f g =
      Φ.tensorMap (vP ≫ f) (vA ≫ g) := by
  simpa only [tensorMap, derivedTensorHom, Category.assoc] using
    congrArg ((Φ.tensorIso X P A).hom ≫ ·) (derivedTensorHom_comp vP vA f g)

/-- The change of coefficients of a tensor product of morphisms followed by the comparison
`Ψ(P ⊗ᴸ A) ⟶ P' ⊗ᴸ A'`. -/
@[reassoc]
lemma map_derivedTensorHom_comp_tensorMap {X : Scheme.{u}} {P A Q B : 𝐃(X, Λ)}
    {P' A' : 𝐃(X, Λ')} (f : Q ⟶ P) (g : B ⟶ A) (vP : (Φ.functor X).obj P ⟶ P')
    (vA : (Φ.functor X).obj A ⟶ A') :
    (Φ.functor X).map (derivedTensorHom (ModuleCat.{u + 1} Λ) f g) ≫ Φ.tensorMap vP vA =
      Φ.tensorMap ((Φ.functor X).map f ≫ vP) ((Φ.functor X).map g ≫ vA) := by
  rw [derivedTensorHom, Functor.map_comp, Category.assoc, tensorMap,
    reassoc_of% (Φ.tensorIso_hom_naturality_right X P g),
    reassoc_of% (Φ.tensorIso_hom_naturality_left X f B), tensorMap]
  simpa only [derivedTensorHom, Category.assoc] using
    congrArg ((Φ.tensorIso X Q B).hom ≫ ·)
      (derivedTensorHom_comp ((Φ.functor X).map f) ((Φ.functor X).map g) vP vA)

/-- The isomorphism `Ψ(P ⊗ᴸ A) ≅ P' ⊗ᴸ A'` induced by `Ψ P ≅ P'` and `Ψ A ≅ A'`. -/
noncomputable def tensorMapIso {X : Scheme.{u}} {P A : 𝐃(X, Λ)} {P' A' : 𝐃(X, Λ')}
    (vP : (Φ.functor X).obj P ≅ P') (vA : (Φ.functor X).obj A ≅ A') :
    (Φ.functor X).obj (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj P).obj A) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ') X).obj P').obj A' :=
  Φ.tensorIso X P A ≪≫ ((derivedTensor (ModuleCat.{u + 1} Λ') X).mapIso vP).app _ ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ') X).obj P').mapIso vA

@[simp]
lemma tensorMapIso_hom {X : Scheme.{u}} {P A : 𝐃(X, Λ)} {P' A' : 𝐃(X, Λ')}
    (vP : (Φ.functor X).obj P ≅ P') (vA : (Φ.functor X).obj A ≅ A') :
    (Φ.tensorMapIso vP vA).hom = Φ.tensorMap vP.hom vA.hom := by
  simp [tensorMapIso, tensorMap]

variable {U Z₁ Z₂ Z : Scheme.{u}} (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
  [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
  (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)

/-- **The product of supports is compatible with a monoidal change of coefficients**:
```
Ψ(Ri₁_! Ri₁^! M ⊗ᴸ Ri₂_! Ri₂^! N) ──Ψ(product)──▶ Ψ(Ri_! Ri^!(M ⊗ᴸ N))
              │                                         │
              ▼                                         ▼
Ri₁_! Ri₁^! M' ⊗ᴸ Ri₂_! Ri₂^! N' ───product───▶ Ri_! Ri^!(M' ⊗ᴸ N')
```
Both composites are maps out of an object supported on `Z`, so they are determined by their
composites with the counit, which are both the tensor product of the counits. -/
lemma map_supportedProduct_comp_supportsMap {M N : 𝐃(U, Λ)} {M' N' : 𝐃(U, Λ')}
    (vM : (Φ.functor U).obj M ≅ M') (vN : (Φ.functor U).obj N ≅ N') :
    (Φ.functor U).map (supportedProduct Λ i₁ i₂ i h M N) ≫
        Φ.supportsMap i (Φ.tensorMapIso vM vN) =
      Φ.tensorMap (Φ.supportsMap i₁ vM) (Φ.supportsMap i₂ vN) ≫
        supportedProduct Λ' i₁ i₂ i h M' N' := by
  have hK : IsZero ((L((i.openComplement.ι)^*[ModuleCat.{u + 1} Λ'])).obj
      ((Φ.functor U).obj (((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
        ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj ((R(i₁)^![Λ]).obj M))).obj
          ((R(i₂)_![ModuleCat.{u + 1} Λ]).obj ((R(i₂)^![Λ]).obj N))))) :=
    (isZero_leftDerivedUpperStar_openComplement_derivedTensor_rightDerivedLowerShriek_of_inter Λ'
      i₁ i₂ i
      h _ _).of_iso ((L((i.openComplement.ι)^*[ModuleCat.{u + 1} Λ'])).mapIso
        (Φ.tensorMapIso ((Φ.lowerShriekIso i₁).app _) ((Φ.lowerShriekIso i₂).app _)))
  refine (existsUnique_comp_counit_of_isZero Λ' i i.openComplement.ι
    i.range_eq_compl_range_openComplement_ι hK _).unique rfl ?_
  rw [Category.assoc, Category.assoc, supportedProduct_comp_counit,
    tensorMap_comp_derivedTensorHom, SupportedCoefficientChange.supportsMap_comp_counit,
    SupportedCoefficientChange.supportsMap_comp_counit,
    SupportedCoefficientChange.supportsMap_comp_counit, ← Functor.map_comp_assoc,
    supportedProduct_comp_counit, tensorMapIso_hom, map_derivedTensorHom_comp_tensorMap]

end Tensor

section Cup

variable [HasKummerClass Λ] [HasKummerClass Λ'] (Φ : MonoidalSupportedCoefficientChange Λ Λ')

variable {U Z₁ Z₂ Z : Scheme.{u}} (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
  [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
  (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)

/-- Blueprint `proposition-compatibility-purity-change-coefficients`: change of coefficients in
purity

**A monoidal change of coefficients commutes with the cup product with supports**
(`AlgebraicGeometry.Etale.cupWithSupportsTateObject`), provided it is compatible with
* `hΔ`: the diagonal `Λ_U ⟶ Λ_U ⊗ᴸ Λ_U` (`AlgebraicGeometry.Etale.constantComplexDiagonal`),
  through `Ψ Λ_U ≅ Λ'_U`, and
* `hμ`: the multiplication `Λ(m)[2m] ⊗ᴸ Λ(m')[2m'] ≅ Λ(m + m')[2(m + m')]`
  (`AlgebraicGeometry.Etale.shiftTateObjectAddIso`), through `Ψ(Λ(m)[2m]) ≅ Λ'(m)[2m]`. -/
theorem mapSupportedClass_cupWithSupportsTateObject [HasInvertibleExponent Λ U]
    [HasInvertibleExponent Λ' U]
    (hΔ : (Φ.functor U).map (constantComplexDiagonal Λ U) ≫
        Φ.tensorMap (Φ.constantComplexIso U).hom (Φ.constantComplexIso U).hom =
      (Φ.constantComplexIso U).hom ≫ constantComplexDiagonal Λ' U)
    (m m' : ℤ)
    (hμ : (Φ.functor U).map (shiftTateObjectAddIso Λ U m m').hom ≫
        (Φ.tateShiftIso U (m + m')).hom =
      Φ.tensorMap (Φ.tateShiftIso U m).hom (Φ.tateShiftIso U m').hom ≫
        (shiftTateObjectAddIso Λ' U m m').hom)
    (α : constantComplex Λ U ⟶ (R(i₁)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₁)^![Λ]).obj ((tateObject Λ U m)⟦2 * m⟧)))
    (β : constantComplex Λ U ⟶ (R(i₂)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₂)^![Λ]).obj ((tateObject Λ U m')⟦2 * m'⟧))) :
    Φ.mapSupportedClass i (Φ.tateShiftIso U (m + m')) (cupWithSupportsTateObject Λ i₁ i₂ i h α β) =
      cupWithSupportsTateObject Λ' i₁ i₂ i h (Φ.mapSupportedClass i₁ (Φ.tateShiftIso U m) α)
        (Φ.mapSupportedClass i₂ (Φ.tateShiftIso U m') β) := by
  rw [cupWithSupportsTateObject, cupWithSupportsTateObject,
    SupportedCoefficientChange.mapSupportedClass_comp _ _ _
      (Φ.tensorMapIso (Φ.tateShiftIso U m) (Φ.tateShiftIso U m')) _ (by rw [tensorMapIso_hom, hμ])]
  congr 1
  rw [← cancel_epi (Φ.constantComplexIso U).hom,
    SupportedCoefficientChange.constantComplexIso_hom_comp_mapSupportedClass]
  simp only [cupWithSupports]
  rw [map_app_comp_map_eq_derivedTensorHom_assoc, map_app_comp_map_eq_derivedTensorHom_assoc,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    map_supportedProduct_comp_supportsMap, map_derivedTensorHom_comp_tensorMap_assoc,
    ← SupportedCoefficientChange.constantComplexIso_hom_comp_mapSupportedClass,
    ← SupportedCoefficientChange.constantComplexIso_hom_comp_mapSupportedClass,
    ← tensorMap_comp_derivedTensorHom_assoc, reassoc_of% hΔ]

/-- Blueprint `proposition-compatibility-purity-change-coefficients`: change of coefficients in
purity

**A monoidal change of coefficients preserves Kummer boundaries**
(`AlgebraicGeometry.Etale.SupportedCoefficientChange.PreservesKummerBoundaries`), hence carries
frame classes to frame classes, provided it is compatible with
* `hunit`: the unit class `Λ_U ≅ Λ_U(0)[0]`;
* `hΔ`: the diagonal `Λ_U ⟶ Λ_U ⊗ᴸ Λ_U`;
* `hμ`: the multiplication `Λ(m)[2m] ⊗ᴸ Λ(m')[2m'] ≅ Λ(m + m')[2(m + m')]` of the twists;
* `hκ`: the Kummer classes `κ(v) ∈ H¹(X, Λ(1))`, through an identification
  `ρ X : Ψ(Λ_X(1)[1]) ≅ Λ'_X(1)[1]` (the Kummer datum of `Λ` maps to that of `Λ'`);
* `hδ`: the boundaries of the supported localization triangles of `V(f) ⊂ U`
  (`AlgebraicGeometry.Etale.localizationBoundaryClass`). -/
theorem preservesKummerBoundaries
    (hunit : ∀ (U : Scheme.{u}) [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ' U],
      (Φ.functor U).map ((HasTateTwist.twistObjectZeroIso (Λ := Λ) U).inv ≫
          (shiftFunctorZero' _ (2 * (0 : ℤ)) (by simp)).inv.app _) ≫ (Φ.tateShiftIso U 0).hom =
        (Φ.constantComplexIso U).hom ≫ (HasTateTwist.twistObjectZeroIso (Λ := Λ') U).inv ≫
          (shiftFunctorZero' _ (2 * (0 : ℤ)) (by simp)).inv.app _)
    (hΔ : ∀ (U : Scheme.{u}) [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ' U],
      (Φ.functor U).map (constantComplexDiagonal Λ U) ≫
          Φ.tensorMap (Φ.constantComplexIso U).hom (Φ.constantComplexIso U).hom =
        (Φ.constantComplexIso U).hom ≫ constantComplexDiagonal Λ' U)
    (hμ : ∀ (U : Scheme.{u}) [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ' U]
      (m m' : ℤ), (Φ.functor U).map (shiftTateObjectAddIso Λ U m m').hom ≫
          (Φ.tateShiftIso U (m + m')).hom =
        Φ.tensorMap (Φ.tateShiftIso U m).hom (Φ.tateShiftIso U m').hom ≫
          (shiftTateObjectAddIso Λ' U m m').hom)
    (ρ : ∀ (X : Scheme.{u}) [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X],
      (Φ.functor X).obj ((tateObject Λ X 1)⟦(1 : ℤ)⟧) ≅ (tateObject Λ' X 1)⟦(1 : ℤ)⟧)
    (hκ : ∀ (X : Scheme.{u}) [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X]
      (v : Γ(X, ⊤)ˣ), (Φ.functor X).map (kummerClass Λ v) ≫ (ρ X).hom =
        (Φ.constantComplexIso X).hom ≫ kummerClass Λ' v)
    (hδ : ∀ (U : Scheme.{u}) [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ' U]
      (f : Γ(U, ⊤))
      (α : constantComplex Λ (U.basicOpen f) ⟶ (tateObject Λ (U.basicOpen f) 1)⟦(1 : ℤ)⟧),
      Φ.mapSupportedClass _ (Φ.tateShiftIso U 1)
          (shiftSupportedClass Λ _ 2 (localizationBoundaryClass Λ f α)) =
        shiftSupportedClass Λ' _ 2 (localizationBoundaryClass Λ' f
          ((Φ.constantComplexIso _).inv ≫ (Φ.functor _).map α ≫ (ρ _).hom))) :
    Φ.PreservesKummerBoundaries where
  map_unitClass U _ _ := hunit U
  mapSupportedClass_kummerBoundary {U} _ _ f :=
    Φ.toSupportedCoefficientChange.mapSupportedClass_kummerBoundary ρ hκ f (hδ U f)
  mapSupportedClass_cupWithSupportsTateObject {U} _ _ _ _ _ i₁ i₂ i _ _ _ h m m' α β :=
    Φ.mapSupportedClass_cupWithSupportsTateObject i₁ i₂ i h (hΔ U) m m' (hμ U m m') α β

end Cup

section Orientation

variable [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] [HasKummerClass Λ']
  [HasKummerClass.IsNormalized Λ'] (Φ : MonoidalSupportedCoefficientChange Λ Λ')

/-- Blueprint `proposition-relative-dualizing-complex--1`,
`proposition-compatibility-purity-change-coefficients`

**The canonical orientation `ω_f ≅ Λ_X(d)[2d]` is compatible with a monoidal change of
coefficients preserving Kummer boundaries**, as soon as the smooth base change identifications
`𝒞(p₁, Δ) ≅ ω_f` (`hC`) and the composition isomorphisms `RΔ^! ω_{p₁} ≅ Λ_X` (`hε`)
correspond: `MonoidalSupportedCoefficientChange.map_dualizingComplexTwistShiftIso` with
`hframe` supplied by
`SupportedCoefficientChange.PreservesKummerBoundaries.mapSupportedClass_frameClass`. -/
theorem map_dualizingComplexTwistShiftIso_of_preservesKummerBoundaries {X Y : Scheme.{u}}
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f] [HasCompactification f] [IsSeparated f]
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X] {k : Type u} [Field k]
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiSeparatedSpace Y]
    [QuasiCompact f] [HasInvertibleExponent Λ (pullback f f)]
    [HasInvertibleExponent Λ' (pullback f f)]
    (vω : (Φ.functor X).obj (dualizingComplex Λ f) ≅ dualizingComplex Λ' f)
    (vω₁ : (Φ.functor (pullback f f)).obj (dualizingComplex Λ (pullback.fst f f)) ≅
      dualizingComplex Λ' (pullback.fst f f))
    (hΦ : Φ.PreservesKummerBoundaries)
    (hC : (Φ.functor X).map (sectionInvariantDiagonalIso Λ f d).hom ≫ vω.hom =
      ((Φ.pullbackIso (pullback.diagonal f)).hom.app _ ≫
          (L((pullback.diagonal f)^*[ModuleCat.{u + 1} Λ'])).map vω₁.hom) ≫
        (sectionInvariantDiagonalIso Λ' f d).hom)
    (hε : (Φ.functor X).map (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ
          (pullback.fst f f) (pullback.diagonal f) (pullback.diagonal_fst f)).hom ≫
        (Φ.constantComplexIso X).hom =
      ((Φ.upperShriekMap (pullback.diagonal f)).app (dualizingComplex Λ (pullback.fst f f)) ≫
          (R(pullback.diagonal f)^![Λ']).map vω₁.hom) ≫
        (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ' (pullback.fst f f)
          (pullback.diagonal f) (pullback.diagonal_fst f)).hom) :
    (Φ.functor X).map (dualizingComplexTwistShiftIso Λ f d aY).hom ≫
        (Φ.twistShiftConstantComplexIso X d).hom =
      vω.hom ≫ (dualizingComplexTwistShiftIso Λ' f d aY).hom :=
  Φ.map_dualizingComplexTwistShiftIso f d aY vω vω₁
    (fun F _ ↦ hΦ.mapSupportedClass_frameClass F) hC hε

end Orientation

end MonoidalSupportedCoefficientChange

end Etale

end AlgebraicGeometry
