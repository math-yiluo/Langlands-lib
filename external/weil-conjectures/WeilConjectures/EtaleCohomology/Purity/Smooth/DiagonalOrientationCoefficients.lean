/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientation
public import WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange

/-!
# The canonical orientation under a change of coefficients

Let `Λ`, `Λ'` be finite coefficient rings with Tate twist data and let
`Ψ : D(X_ét, Λ) ⥤ D(X_ét, Λ')` be a change of coefficients, for instance the reduction
`A_{E,n+1} → A_{E,n}`. This file shows that the fundamental class of a closed immersion with
Thom frames, and hence the purity isomorphism of a section of a smooth morphism out of which
the canonical orientation `ω_f ≅ Λ_X(d)[2d]`
(`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso`, blueprint
`proposition-relative-dualizing-complex--1`) is built, is compatible with `Ψ` (blueprint
`proposition-compatibility-purity-change-coefficients`).

The change of coefficients is bundled with the comparison data the statement needs
(`AlgebraicGeometry.Etale.SupportedCoefficientChange`): `Ψ Λ_X ≅ Λ'_X`,
`Ψ(Λ_X(m)[2m]) ≅ Λ'_X(m)[2m]`, `Ψ ∘ Le^* ≅ Le^* ∘ Ψ`, `Ψ ∘ Ri_! ≅ Ri_! ∘ Ψ` and a comparison
`Ψ ∘ Ri^! ⟶ Ri^! ∘ Ψ` compatible with the counits of `Ri_! ⊣ Ri^!`, for closed immersions `i`,
subject to the evident compatibilities. Such data carry a class with supports
`γ : Λ_X ⟶ Ri_! Ri^! L` to a class `Ψ γ : Λ'_X ⟶ Ri_! Ri^! L'`
(`AlgebraicGeometry.Etale.SupportedCoefficientChange.mapSupportedClass`), compatibly with
restriction of supports along any morphism and with the adjoint `Λ_Z ⟶ Ri^! L` of a class.

The key step is uniqueness-driven: the fundamental class `[Z ⊂ X]` is the unique class
restricting to the frame classes `∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_c)` on every frame
(`AlgebraicGeometry.Etale.HasThomFrames.existsUnique_fundamentalClass`), so as soon as `Ψ`
carries the frame classes over `Λ` to the frame classes over `Λ'` (which is where the
compatibility of the Kummer classes enters), it carries `[Z ⊂ X]` over `Λ` to `[Z ⊂ X]` over
`Λ'`. Consequently the purity isomorphism `Rs^!(Λ_V(c)[2c]) ≅ Λ_B` of a section is compatible
with `Ψ`, and so is the canonical orientation `ω_f ≅ Λ_X(d)[2d]`, provided the remaining
building blocks of its construction are: the smooth base change `𝒞(p₁, Δ) ≅ ω_f`, the
composition isomorphism `RΔ^! ω_{p₁} ≅ Λ_X`, and the tensor maps of `RΔ^!` entering the section
invariant (`AlgebraicGeometry.Etale.SupportedCoefficientChange.PreservesSectionInvariantIso`).
These are hypotheses, as are the compatibilities of the constituents of the purity map in
`AlgebraicGeometry.Etale.map_smoothPurityIso_hom_comp`.

## Main definitions

- `AlgebraicGeometry.Etale.SupportedCoefficientChange`: a change of coefficients with its
  comparisons with `Le^*`, `Ri_!` and `Ri^!`.
- `AlgebraicGeometry.Etale.SupportedCoefficientChange.mapSupportedClass`: the change of
  coefficients of a class with supports.
- `AlgebraicGeometry.Etale.SupportedCoefficientChange.PreservesSectionInvariantIso`: the change
  of coefficients is compatible with the section invariant construction.

## Main statements

In the namespace `AlgebraicGeometry.Etale.SupportedCoefficientChange`:

- `restrictSupportedClass_mapSupportedClass`: the change of coefficients commutes with
  restriction of supports.
- `supportedClassMap_mapSupportedClass`: it commutes with taking adjoints `Λ_Z ⟶ Ri^! L`.
- `mapSupportedClass_thomFundamentalClass`: the change of coefficients of the fundamental class
  is the fundamental class.
- `map_thomFundamentalClassMap`, `isIso_upperShriekMap_app_of_hasThomFrames`: the purity map
  `cl_i` is compatible with the change of coefficients, and `Ψ Ri^! ⟶ Ri^! Ψ` is an isomorphism
  at `Λ_X(c)[2c]`.
- `map_rightDerivedUpperShriekTateObjectIsoOfSection`: the purity isomorphism
  `Rs^!(Λ_V(c)[2c]) ≅ Λ_B` of a section is compatible with the change of coefficients.
- `map_sectionInvariantTwistShiftIsoOfSection`, `map_dualizingComplexTwistShiftIso`: the section
  invariant isomorphism and the canonical orientation are compatible with the change of
  coefficients.
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

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

section Structure

variable (Λ Λ' : Type (u + 1)) [CommRing Λ] [Finite Λ] [CommRing Λ'] [Finite Λ']
  [HasTateTwist Λ] [HasTateTwist Λ']

/-- Blueprint `proposition-compatibility-purity-change-coefficients`: change of coefficients in
purity

A change of coefficients `Ψ : D(X_ét, Λ) ⥤ D(X_ét, Λ')` (for instance the reduction
`A_{E,n+1} → A_{E,n}`, i.e. the derived extension of scalars), together with the comparisons
through which it acts on classes with supports:
* `Ψ Λ_X ≅ Λ'_X` and `Ψ(Λ_X(m)[2m]) ≅ Λ'_X(m)[2m]`;
* `Ψ ∘ Le^* ≅ Le^* ∘ Ψ`, compatibly with `Le^* Λ_X ≅ Λ_U` and `Le^*(Λ_X(m)[2m]) ≅ Λ_U(m)[2m]`;
* for a closed immersion `i`, `Ψ ∘ Ri_! ≅ Ri_! ∘ Ψ`, carrying the restriction map
  `Λ_X ⟶ Ri_! Λ_Z` to the restriction map, and a comparison `Ψ ∘ Ri^! ⟶ Ri^! ∘ Ψ` compatible
  with the counits of `Ri_! ⊣ Ri^!`. -/
structure SupportedCoefficientChange where
  /-- The change of coefficients on `D(X_ét)`. -/
  functor (X : Scheme.{u}) : 𝐃(X, Λ) ⥤ 𝐃(X, Λ')
  /-- The change of coefficients of the constant complex. -/
  constantComplexIso (X : Scheme.{u}) :
    (functor X).obj (constantComplex Λ X) ≅ constantComplex Λ' X
  /-- The change of coefficients of the shifted twisting objects. -/
  tateShiftIso (X : Scheme.{u}) [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X]
    (m : ℤ) : (functor X).obj ((tateObject Λ X m)⟦2 * m⟧) ≅ (tateObject Λ' X m)⟦2 * m⟧
  /-- The change of coefficients commutes with derived pullback. -/
  pullbackIso {U X : Scheme.{u}} (e : U ⟶ X) :
    L((e)^*[ModuleCat.{u + 1} Λ]) ⋙ functor U ≅ functor X ⋙ L((e)^*[ModuleCat.{u + 1} Λ'])
  /-- The change of coefficients commutes with `Ri_!` for a closed immersion `i`. -/
  lowerShriekIso {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    R(i)_![ModuleCat.{u + 1} Λ] ⋙ functor X ≅ functor Z ⋙ R(i)_![ModuleCat.{u + 1} Λ']
  /-- The comparison of the change of coefficients with `Ri^!` for a closed immersion `i`. -/
  upperShriekMap {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    R(i)^![Λ] ⋙ functor Z ⟶ functor X ⋙ R(i)^![Λ']
  /-- The comparison with `Ri^!` is compatible with the counits of `Ri_! ⊣ Ri^!`. -/
  map_counit {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (L : 𝐃(X, Λ)) :
    (R(i)_![ModuleCat.{u + 1} Λ']).map ((upperShriekMap i).app L) ≫
        (rightDerivedUpperShriekAdjunction Λ' i).counit.app ((functor X).obj L) =
      (lowerShriekIso i).inv.app ((R(i)^![Λ]).obj L) ≫
        (functor X).map ((rightDerivedUpperShriekAdjunction Λ i).counit.app L)
  /-- The change of coefficients carries the restriction map `Λ_X ⟶ Ri_! Λ_Z` to the
  restriction map. -/
  map_supportedRestrictionMap {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (functor X).map (supportedRestrictionMap Λ i) ≫ (lowerShriekIso i).hom.app _ ≫
        (R(i)_![ModuleCat.{u + 1} Λ']).map (constantComplexIso Z).hom =
      (constantComplexIso X).hom ≫ supportedRestrictionMap Λ' i
  /-- Compatibility of the commutation with pullback with `Le^* Λ_X ≅ Λ_U`. -/
  map_leftDerivedUpperStarConstantComplexIso {U X : Scheme.{u}} (e : U ⟶ X) :
    (functor U).map (leftDerivedUpperStarConstantComplexIso Λ e).hom ≫
        (constantComplexIso U).hom =
      (pullbackIso e).hom.app _ ≫
        (L((e)^*[ModuleCat.{u + 1} Λ'])).map (constantComplexIso X).hom ≫
          (leftDerivedUpperStarConstantComplexIso Λ' e).hom
  /-- Compatibility of the commutation with pullback with `Le^*(Λ_X(m)[2m]) ≅ Λ_U(m)[2m]`. -/
  map_leftDerivedUpperStarTateShiftIso {U X : Scheme.{u}} [HasInvertibleExponent Λ U]
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' U] [HasInvertibleExponent Λ' X]
    (e : U ⟶ X) (m : ℤ) :
    (functor U).map (leftDerivedUpperStarTateShiftIso Λ e m).hom ≫ (tateShiftIso U m).hom =
      (pullbackIso e).hom.app _ ≫
        (L((e)^*[ModuleCat.{u + 1} Λ'])).map (tateShiftIso X m).hom ≫
          (leftDerivedUpperStarTateShiftIso Λ' e m).hom

end Structure

namespace SupportedCoefficientChange

section Supports

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [Finite Λ] [CommRing Λ'] [Finite Λ']
  [HasTateTwist Λ] [HasTateTwist Λ'] (Φ : SupportedCoefficientChange Λ Λ')

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The comparison `Ψ(Ri_! Ri^! L) ⟶ Ri_! Ri^! L'` for `τ : Ψ L ≅ L'`: the commutation of `Ψ`
with `Ri_!`, followed by `Ri_!` of the comparison `Ψ Ri^! L ⟶ Ri^! Ψ L` and of `Ri^! τ`. -/
noncomputable def supportsMap {L : 𝐃(X, Λ)} {L' : 𝐃(X, Λ')} (τ : (Φ.functor X).obj L ≅ L') :
    (Φ.functor X).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) ⟶
      (R(i)_![ModuleCat.{u + 1} Λ']).obj ((R(i)^![Λ']).obj L') :=
  (Φ.lowerShriekIso i).hom.app _ ≫
    (R(i)_![ModuleCat.{u + 1} Λ']).map ((Φ.upperShriekMap i).app L ≫ (R(i)^![Λ']).map τ.hom)

/-- The comparison `Ψ(Ri_! Ri^! L) ⟶ Ri_! Ri^! L'` is compatible with the counits. -/
@[reassoc]
lemma supportsMap_comp_counit {L : 𝐃(X, Λ)} {L' : 𝐃(X, Λ')} (τ : (Φ.functor X).obj L ≅ L') :
    Φ.supportsMap i τ ≫ (rightDerivedUpperShriekAdjunction Λ' i).counit.app L' =
      (Φ.functor X).map ((rightDerivedUpperShriekAdjunction Λ i).counit.app L) ≫ τ.hom := by
  rw [supportsMap, Functor.map_comp, Category.assoc, Category.assoc,
    (rightDerivedUpperShriekAdjunction Λ' i).counit_naturality τ.hom,
    reassoc_of% (Φ.map_counit i L), Iso.hom_inv_id_app_assoc]

/-- The change of coefficients of a class with supports `γ : Λ_X ⟶ Ri_! Ri^! L`, along an
identification `τ : Ψ L ≅ L'`: the class `Λ'_X ≅ Ψ Λ_X ⟶ Ψ(Ri_! Ri^! L) ⟶ Ri_! Ri^! L'`. -/
noncomputable def mapSupportedClass {L : 𝐃(X, Λ)} {L' : 𝐃(X, Λ')}
    (τ : (Φ.functor X).obj L ≅ L')
    (γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) :
    constantComplex Λ' X ⟶ (R(i)_![ModuleCat.{u + 1} Λ']).obj ((R(i)^![Λ']).obj L') :=
  (Φ.constantComplexIso X).inv ≫ (Φ.functor X).map γ ≫ Φ.supportsMap i τ

/-- The change of coefficients commutes with the adjoint `Hom(Λ_X, Ri_! N) ≅ Hom(Λ_Z, N)`
(`AlgebraicGeometry.Etale.supportedTranspose`): every `γ : Λ_X ⟶ Ri_! N` is the restriction
map followed by `Ri_!` of its adjoint, and `Ψ` preserves the restriction map. -/
@[reassoc]
lemma supportedTranspose_map {N : 𝐃(Z, Λ)}
    (γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj N) :
    supportedTranspose Λ' i ((Φ.constantComplexIso X).inv ≫ (Φ.functor X).map γ ≫
        (Φ.lowerShriekIso i).hom.app N) =
      (Φ.constantComplexIso Z).inv ≫ (Φ.functor Z).map (supportedTranspose Λ i γ) := by
  have hu : (Φ.constantComplexIso X).inv ≫ (Φ.functor X).map (supportedRestrictionMap Λ i) ≫
      (Φ.lowerShriekIso i).hom.app _ =
        supportedRestrictionMap Λ' i ≫
          (R(i)_![ModuleCat.{u + 1} Λ']).map (Φ.constantComplexIso Z).inv := by
    rw [Iso.inv_comp_eq, ← reassoc_of% (Φ.map_supportedRestrictionMap i), ← Functor.map_comp,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]
  have hn := (Φ.lowerShriekIso i).hom.naturality (supportedTranspose Λ i γ)
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  conv_lhs => rw [← supportedRestrictionMap_comp_map_supportedTranspose Λ i γ,
    Functor.map_comp, Category.assoc, hn, ← Category.assoc, ← Category.assoc, Category.assoc _ _
      ((Φ.lowerShriekIso i).hom.app _), hu, Category.assoc, ← Functor.map_comp]
  rw [supportedTranspose_comp, supportedTranspose_supportedRestrictionMap, Category.id_comp]

/-- The adjoint `Λ'_Z ⟶ Ri^! L'` of the change of coefficients of a class with supports is the
change of coefficients of its adjoint, followed by the comparison `Ψ Ri^! L ⟶ Ri^! Ψ L` and
`Ri^! τ`. -/
theorem supportedClassMap_mapSupportedClass {L : 𝐃(X, Λ)} {L' : 𝐃(X, Λ')}
    (τ : (Φ.functor X).obj L ≅ L')
    (γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) :
    supportedClassMap Λ' i (Φ.mapSupportedClass i τ γ) =
      (Φ.constantComplexIso Z).inv ≫ (Φ.functor Z).map (supportedClassMap Λ i γ) ≫
        (Φ.upperShriekMap i).app L ≫ (R(i)^![Λ']).map τ.hom := by
  rw [supportedClassMap_eq_supportedTranspose, supportedClassMap_eq_supportedTranspose,
    mapSupportedClass, supportsMap]
  simp only [← Category.assoc]
  rw [supportedTranspose_comp]
  simp only [Category.assoc]
  rw [supportedTranspose_map_assoc]

end Supports

section Restriction

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [Finite Λ] [CommRing Λ'] [Finite Λ']
  [HasTateTwist Λ] [HasTateTwist Λ'] (Φ : SupportedCoefficientChange Λ Λ')

variable {U X Z Z' : Scheme.{u}} (e : U ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ U) [IsClosedImmersion i]
  [IsClosedImmersion i'] (g : Z' ⟶ Z) (hg : IsPullback g i' i e) [HasInvertibleExponent Λ U]
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' U] [HasInvertibleExponent Λ' X]

/-- The comparison of supports `Ψ(Ri_! Ri^! L) ⟶ Ri_! Ri^! L'` commutes with restriction of
supports along `e` (`AlgebraicGeometry.Etale.supportedRestriction`). Both sides are maps out of
an object supported on the base change `Z'` of `Z`, so they are determined by their composites
with the counit, which agree. -/
lemma map_supportsMap_comp_supportedRestriction (m : ℤ) :
    (L((e)^*[ModuleCat.{u + 1} Λ'])).map (Φ.supportsMap i (Φ.tateShiftIso X m)) ≫
        supportedRestriction Λ' e i i' g hg _ _ (leftDerivedUpperStarTateShiftIso Λ' e m) =
      (Φ.pullbackIso e).inv.app _ ≫ (Φ.functor U).map
          (supportedRestriction Λ e i i' g hg _ _ (leftDerivedUpperStarTateShiftIso Λ e m)) ≫
        Φ.supportsMap i' (Φ.tateShiftIso U m) := by
  have hK : IsZero ((L((i'.openComplement.ι)^*[ModuleCat.{u + 1} Λ'])).obj
      ((L((e)^*[ModuleCat.{u + 1} Λ'])).obj ((Φ.functor X).obj
        ((R(i)_![ModuleCat.{u + 1} Λ]).obj
          ((R(i)^![Λ]).obj ((tateObject Λ X m)⟦2 * m⟧)))))) :=
    (isZero_leftDerivedUpperStar_openComplement_leftDerivedUpperStar_rightDerivedLowerShriek
      (ModuleCat.{u + 1} Λ') e i i' g hg _).of_iso
      ((L((i'.openComplement.ι)^*[ModuleCat.{u + 1} Λ'])).mapIso
        ((L((e)^*[ModuleCat.{u + 1} Λ'])).mapIso ((Φ.lowerShriekIso i).app _)))
  refine (existsUnique_comp_counit_of_isZero Λ' i' i'.openComplement.ι
    i'.range_eq_compl_range_openComplement_ι hK _).unique rfl ?_
  have hτ := Φ.map_leftDerivedUpperStarTateShiftIso e m
  have hn := (Φ.pullbackIso e).hom.naturality
    ((rightDerivedUpperShriekAdjunction Λ i).counit.app ((tateObject Λ X m)⟦2 * m⟧))
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [supportedRestriction_comp_counit, ← Functor.map_comp_assoc,
    Φ.supportsMap_comp_counit i (Φ.tateShiftIso X m),
    Φ.supportsMap_comp_counit i' (Φ.tateShiftIso U m), ← Functor.map_comp_assoc,
    supportedRestriction_comp_counit, Functor.map_comp_assoc, hτ, reassoc_of% hn,
    Iso.inv_hom_id_app_assoc, Functor.map_comp_assoc]

/-- **The change of coefficients commutes with restriction of supports.** Restricting the change
of coefficients of a class `γ ∈ H^{2m}_Z(X, Λ(m))` along `e : U ⟶ X` is the change of
coefficients of the restriction of `γ` (`AlgebraicGeometry.Etale.restrictSupportedClass`). -/
theorem restrictSupportedClass_mapSupportedClass (m : ℤ)
    (γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![Λ]).obj ((tateObject Λ X m)⟦2 * m⟧))) :
    restrictSupportedClass Λ' e i i' g hg (leftDerivedUpperStarConstantComplexIso Λ' e).inv
        (leftDerivedUpperStarTateShiftIso Λ' e m) (Φ.mapSupportedClass i (Φ.tateShiftIso X m) γ) =
      Φ.mapSupportedClass i' (Φ.tateShiftIso U m)
        (restrictSupportedClass Λ e i i' g hg (leftDerivedUpperStarConstantComplexIso Λ e).inv
          (leftDerivedUpperStarTateShiftIso Λ e m) γ) := by
  have hc : (Φ.constantComplexIso U).inv ≫
      (Φ.functor U).map (leftDerivedUpperStarConstantComplexIso Λ e).inv ≫
        (Φ.pullbackIso e).hom.app _ =
      (leftDerivedUpperStarConstantComplexIso Λ' e).inv ≫
        (L((e)^*[ModuleCat.{u + 1} Λ'])).map (Φ.constantComplexIso X).inv := by
    rw [← cancel_epi ((Φ.functor U).map (leftDerivedUpperStarConstantComplexIso Λ e).hom ≫
      (Φ.constantComplexIso U).hom)]
    conv_rhs => rw [Φ.map_leftDerivedUpperStarConstantComplexIso e]
    simp
  have hn := (Φ.pullbackIso e).hom.naturality γ
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  simp only [restrictSupportedClass, mapSupportedClass, Functor.map_comp, Category.assoc]
  rw [Φ.map_supportsMap_comp_supportedRestriction e i i' g hg m, ← reassoc_of% hc,
    ← reassoc_of% hn, Iso.hom_inv_id_app_assoc]

/-- The change of coefficients commutes with the restriction of classes to a frame
(`AlgebraicGeometry.Etale.frameRestriction`). -/
theorem frameRestriction_mapSupportedClass {c : ℕ} (F : i.EtaleFrame c)
    (γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))) :
    frameRestriction Λ' F (Φ.mapSupportedClass i (Φ.tateShiftIso X c) γ) =
      Φ.mapSupportedClass _ (Φ.tateShiftIso F.U c) (frameRestriction Λ F γ) :=
  Φ.restrictSupportedClass_mapSupportedClass F.e i _ F.toZ F.isPullback c γ

end Restriction

section FundamentalClass

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [Finite Λ] [CommRing Λ'] [Finite Λ']
  [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] [HasKummerClass Λ']
  [HasKummerClass.IsNormalized Λ'] (Φ : SupportedCoefficientChange Λ Λ')

variable {X Z : Scheme.{u}} [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X] {c : ℕ}
  {i : Z ⟶ X} [IsClosedImmersion i]

/-- Blueprint `proposition-compatibility-purity-change-coefficients`: change of coefficients in
purity

**The change of coefficients of the fundamental class is the fundamental class.** Let
`i : Z ⟶ X` be a closed immersion with Thom frames over `Λ` and `Λ'` and regular Zariski frames,
`X` locally of finite type over a field. If the change of coefficients carries the frame class
`∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_c)` over `Λ` of every Zariski frame to the frame class over `Λ'` (the
compatibility of the Kummer classes), then it carries the fundamental class `[Z ⊂ X]` over `Λ`
to the fundamental class over `Λ'`: the latter is the unique class restricting to the frame
classes (`AlgebraicGeometry.Etale.HasThomFrames.eq_of_frameRestriction_eq`), and the change of
coefficients commutes with restriction to frames
(`AlgebraicGeometry.Etale.SupportedCoefficientChange.frameRestriction_mapSupportedClass`). -/
theorem mapSupportedClass_thomFundamentalClass (hT : HasThomFrames Λ c i)
    (hT' : HasThomFrames Λ' c i) (hR : HasRegularZariskiFrames c i) {k : Type u} [Field k]
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
    (hframe : ∀ F : i.EtaleFrame c, IsOpenImmersion F.e →
      Φ.mapSupportedClass _ (Φ.tateShiftIso F.U c) (frameClass Λ F) = frameClass Λ' F) :
    Φ.mapSupportedClass i (Φ.tateShiftIso X c) (thomFundamentalClass Λ hT hR aX) =
      thomFundamentalClass Λ' hT' hR aX :=
  hT'.eq_of_frameRestriction_eq hR fun F hF ↦ by
    rw [frameRestriction_mapSupportedClass, frameRestriction_thomFundamentalClass, hframe F hF,
      frameRestriction_thomFundamentalClass]

/-- Blueprint `proposition-compatibility-purity-change-coefficients`: change of coefficients in
purity

**The purity map `cl_i : Λ_Z ⟶ Ri^!(Λ_X(c)[2c])` is compatible with the change of
coefficients**, for a closed immersion with Thom frames whose frame classes are carried to the
frame classes:

```
Ψ Λ_Z ──────Ψ cl_i──────▶ Ψ Ri^!(Λ_X(c)[2c]) ──▶ Ri^! Ψ(Λ_X(c)[2c])
  │ ≅                                                  │ ≅
  ▼                                                    ▼
Λ'_Z ─────────────────cl'_i─────────────────▶ Ri^!(Λ'_X(c)[2c])
``` -/
theorem map_thomFundamentalClassMap (hT : HasThomFrames Λ c i) (hT' : HasThomFrames Λ' c i)
    (hR : HasRegularZariskiFrames c i) {k : Type u} [Field k] (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX]
    (hframe : ∀ F : i.EtaleFrame c, IsOpenImmersion F.e →
      Φ.mapSupportedClass _ (Φ.tateShiftIso F.U c) (frameClass Λ F) = frameClass Λ' F) :
    (Φ.functor Z).map (thomFundamentalClassMap Λ hT hR aX) ≫
        (Φ.upperShriekMap i).app ((tateObject Λ X c)⟦2 * (c : ℤ)⟧) ≫
          (R(i)^![Λ']).map (Φ.tateShiftIso X c).hom =
      (Φ.constantComplexIso Z).hom ≫ thomFundamentalClassMap Λ' hT' hR aX := by
  rw [thomFundamentalClassMap, thomFundamentalClassMap,
    ← Φ.mapSupportedClass_thomFundamentalClass hT hT' hR aX hframe,
    supportedClassMap_mapSupportedClass, Iso.hom_inv_id_assoc]

/-- For a closed immersion with Thom frames whose frame classes are carried to the frame
classes, the comparison `Ψ Ri^! ⟶ Ri^! Ψ` is an isomorphism at `Λ_X(c)[2c]`: up to the
isomorphisms `cl_i` and `cl'_i`, it is `Ψ Λ_Z ≅ Λ'_Z`
(`AlgebraicGeometry.Etale.SupportedCoefficientChange.map_thomFundamentalClassMap`). -/
theorem isIso_upperShriekMap_app_of_hasThomFrames (hT : HasThomFrames Λ c i)
    (hT' : HasThomFrames Λ' c i) (hR : HasRegularZariskiFrames c i) {k : Type u} [Field k]
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
    (hframe : ∀ F : i.EtaleFrame c, IsOpenImmersion F.e →
      Φ.mapSupportedClass _ (Φ.tateShiftIso F.U c) (frameClass Λ F) = frameClass Λ' F) :
    IsIso ((Φ.upperShriekMap i).app ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)) := by
  have := isIso_thomFundamentalClassMap Λ hT hR aX
  have := isIso_thomFundamentalClassMap Λ' hT' hR aX
  have h : (Φ.upperShriekMap i).app ((tateObject Λ X c)⟦2 * (c : ℤ)⟧) ≫
      (R(i)^![Λ']).map (Φ.tateShiftIso X c).hom =
        inv ((Φ.functor Z).map (thomFundamentalClassMap Λ hT hR aX)) ≫
          (Φ.constantComplexIso Z).hom ≫ thomFundamentalClassMap Λ' hT' hR aX := by
    rw [← Φ.map_thomFundamentalClassMap hT hT' hR aX hframe, IsIso.inv_hom_id_assoc]
  have : IsIso ((Φ.upperShriekMap i).app ((tateObject Λ X c)⟦2 * (c : ℤ)⟧) ≫
      (R(i)^![Λ']).map (Φ.tateShiftIso X c).hom) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((R(i)^![Λ']).map (Φ.tateShiftIso X c).hom)

/-- Blueprint `proposition-compatibility-purity-change-coefficients`: change of coefficients in
purity

**Purity for a section of a smooth morphism is compatible with the change of coefficients.**
For `g : V ⟶ B` smooth of relative dimension `c` with a closed section `s`, `B` separated and
locally of finite type over a field, if the change of coefficients carries the frame classes of
`s` over `Λ` to those over `Λ'`, then the purity isomorphisms `Rs^!(Λ_V(c)[2c]) ≅ Λ_B`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekTateObjectIsoOfSection`) over `Λ` and `Λ'`
correspond under `Ψ Rs^! ⟶ Rs^! Ψ`, `Ψ(Λ_V(c)[2c]) ≅ Λ'_V(c)[2c]` and `Ψ Λ_B ≅ Λ'_B`. -/
theorem map_rightDerivedUpperShriekTateObjectIsoOfSection {V B : Scheme.{u}} (c : ℕ)
    (g : V ⟶ B) [SmoothOfRelativeDimension c g] (s : B ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 B) {k : Type u} [Field k] (aB : B ⟶ Spec (.of k)) [IsSeparated aB]
    [LocallyOfFiniteType aB] [HasInvertibleExponent Λ V] [HasInvertibleExponent Λ' V]
    (hframe : ∀ F : s.EtaleFrame c, IsOpenImmersion F.e →
      Φ.mapSupportedClass _ (Φ.tateShiftIso F.U c) (frameClass Λ F) = frameClass Λ' F) :
    (Φ.functor B).map (rightDerivedUpperShriekTateObjectIsoOfSection Λ c g s hs aB).hom ≫
        (Φ.constantComplexIso B).hom =
      ((Φ.upperShriekMap s).app ((tateObject Λ V c)⟦2 * (c : ℤ)⟧) ≫
          (R(s)^![Λ']).map (Φ.tateShiftIso V c).hom) ≫
        (rightDerivedUpperShriekTateObjectIsoOfSection Λ' c g s hs aB).hom := by
  have := SmoothOfRelativeDimension.smooth c g
  have h := Φ.map_thomFundamentalClassMap (hasThomFrames_of_section Λ c g s hs aB)
    (hasThomFrames_of_section Λ' c g s hs aB) (hasRegularZariskiFrames_of_section c g s hs)
    (g ≫ aB) hframe
  have := isIso_thomFundamentalClassMap Λ (hasThomFrames_of_section Λ c g s hs aB)
    (hasRegularZariskiFrames_of_section c g s hs) (g ≫ aB)
  have := isIso_thomFundamentalClassMap Λ' (hasThomFrames_of_section Λ' c g s hs aB)
    (hasRegularZariskiFrames_of_section c g s hs) (g ≫ aB)
  simp only [rightDerivedUpperShriekTateObjectIsoOfSection, Iso.symm_hom, asIso_inv]
  rw [← cancel_epi ((Φ.functor B).map (thomFundamentalClassMap Λ
      (hasThomFrames_of_section Λ c g s hs aB) (hasRegularZariskiFrames_of_section c g s hs)
      (g ≫ aB))), ← Functor.map_comp_assoc, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.assoc, reassoc_of% h, IsIso.hom_inv_id, Category.comp_id]

end FundamentalClass

section SectionInvariant

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [Finite Λ] [CommRing Λ'] [Finite Λ']
  [HasTateTwist Λ] [HasTateTwist Λ'] (Φ : SupportedCoefficientChange Λ Λ')

/-- The change of coefficients of `Λ_X(m)[2m] = twistShift (Λ_X)`: through
`AlgebraicGeometry.Etale.twistShiftConstantComplexIso` it is the change of coefficients
`Ψ(Λ_X(m)[2m]) ≅ Λ'_X(m)[2m]` of the shifted twisting objects. -/
noncomputable def twistShiftConstantComplexIso (X : Scheme.{u}) [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ' X] (m : ℤ) :
    (Φ.functor X).obj ((twistShift Λ X m).obj (constantComplex Λ X)) ≅
      (twistShift Λ' X m).obj (constantComplex Λ' X) :=
  (Φ.functor X).mapIso (Etale.twistShiftConstantComplexIso Λ X m) ≪≫ Φ.tateShiftIso X m ≪≫
    (Etale.twistShiftConstantComplexIso Λ' X m).symm

/-- The change of coefficients *preserves the section invariant construction* at a closed
immersion `s : B ⟶ V`: for identifications `vω : Ψ ω ≅ ω'` and `vT : Ψ T ≅ T'` of invertible
objects, the isomorphisms `Ls^* ω ≅ Ls^* T`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso`, built from the
tensor maps `Rs^! M ⊗ Ls^* N ⟶ Rs^!(M ⊗ N)`, the symmetry and the unitors of `⊗ᴸ`) built from
corresponding isomorphisms `Rs^! T ≅ Λ_B`, `Rs^! ω ≅ Λ_B` over `Λ` and `Λ'` correspond. This
holds for a change of coefficients compatible with the monoidal structures and the tensor maps
of `Rs^!`. -/
def PreservesSectionInvariantIso {V B : Scheme.{u}} (s : B ⟶ V) [IsClosedImmersion s] : Prop :=
  ∀ {ω T : 𝐃(V, Λ)} {ω' T' : 𝐃(V, Λ')} (vω : (Φ.functor V).obj ω ≅ ω')
    (vT : (Φ.functor V).obj T ≅ T') (hω : DerivedCategory.isInvertible Λ V ω)
    (hT : DerivedCategory.isInvertible Λ V T) (hω' : DerivedCategory.isInvertible Λ' V ω')
    (hT' : DerivedCategory.isInvertible Λ' V T') (θ : (R(s)^![Λ]).obj T ≅ constantComplex Λ B)
    (ε : (R(s)^![Λ]).obj ω ≅ constantComplex Λ B)
    (θ' : (R(s)^![Λ']).obj T' ≅ constantComplex Λ' B)
    (ε' : (R(s)^![Λ']).obj ω' ≅ constantComplex Λ' B),
    (Φ.functor B).map θ.hom ≫ (Φ.constantComplexIso B).hom =
        ((Φ.upperShriekMap s).app T ≫ (R(s)^![Λ']).map vT.hom) ≫ θ'.hom →
      (Φ.functor B).map ε.hom ≫ (Φ.constantComplexIso B).hom =
          ((Φ.upperShriekMap s).app ω ≫ (R(s)^![Λ']).map vω.hom) ≫ ε'.hom →
      (Φ.functor B).map (leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso Λ s hω hT θ ε).hom ≫
          (Φ.pullbackIso s).hom.app T ≫ (L((s)^*[ModuleCat.{u + 1} Λ'])).map vT.hom =
        (Φ.pullbackIso s).hom.app ω ≫ (L((s)^*[ModuleCat.{u + 1} Λ'])).map vω.hom ≫
          (leftDerivedUpperStarIsoOfRightDerivedUpperShriekIso Λ' s hω' hT' θ' ε').hom

end SectionInvariant

section Orientation

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [Finite Λ] [CommRing Λ'] [Finite Λ']
  [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] [HasKummerClass Λ']
  [HasKummerClass.IsNormalized Λ'] (Φ : SupportedCoefficientChange Λ Λ')

/-- Blueprint `proposition-compatibility-purity-change-coefficients`: change of coefficients in
purity

**The section invariant isomorphism `𝒞(g, s) ≅ Λ_B(c)[2c]` is compatible with the change of
coefficients.** Let `g : V ⟶ B` be smooth of relative dimension `c` with a closed section `s`,
`B` separated and locally of finite type over a field, and `vω : Ψ ω_g ≅ ω'_g` an
identification of the dualizing complexes. Assume
* `hframe`: the change of coefficients carries the frame classes of `s` over `Λ` to those
  over `Λ'` (this gives the compatibility of the purity isomorphism of `s`,
  `SupportedCoefficientChange.map_rightDerivedUpperShriekTateObjectIsoOfSection`);
* `hε`: the isomorphisms `Rs^! ω_g ≅ Λ_B` (composition of `R^!`,
  `AlgebraicGeometry.Etale.rightDerivedUpperShriekDualizingComplexIsoOfCompEqId`) correspond;
* `hL`: the change of coefficients preserves the section invariant construction at `s`
  (`AlgebraicGeometry.Etale.SupportedCoefficientChange.PreservesSectionInvariantIso`).

Then the section invariant isomorphisms
(`AlgebraicGeometry.Etale.sectionInvariantTwistShiftIsoOfSection`) over `Λ` and `Λ'`
correspond under `Ψ Ls^* ω_g ≅ Ls^* Ψ ω_g ≅ Ls^* ω'_g` and
`Ψ(Λ_B(c)[2c]) ≅ Λ'_B(c)[2c]`. -/
theorem map_sectionInvariantTwistShiftIsoOfSection {V B : Scheme.{u}} (c : ℕ) (g : V ⟶ B)
    [SmoothOfRelativeDimension c g] [HasCompactification g] (s : B ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 B) {k : Type u} [Field k] (aB : B ⟶ Spec (.of k)) [IsSeparated aB]
    [LocallyOfFiniteType aB] [HasInvertibleExponent Λ V] [HasInvertibleExponent Λ' V]
    [HasInvertibleExponent Λ B] [HasInvertibleExponent Λ' B]
    (vω : (Φ.functor V).obj (dualizingComplex Λ g) ≅ dualizingComplex Λ' g)
    (hframe : ∀ F : s.EtaleFrame c, IsOpenImmersion F.e →
      Φ.mapSupportedClass _ (Φ.tateShiftIso F.U c) (frameClass Λ F) = frameClass Λ' F)
    (hε : (Φ.functor B).map (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ g s hs).hom ≫
        (Φ.constantComplexIso B).hom =
      ((Φ.upperShriekMap s).app (dualizingComplex Λ g) ≫ (R(s)^![Λ']).map vω.hom) ≫
        (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ' g s hs).hom)
    (hL : Φ.PreservesSectionInvariantIso s) :
    (Φ.functor B).map (sectionInvariantTwistShiftIsoOfSection Λ c g s hs aB).hom ≫
        (Φ.twistShiftConstantComplexIso B c).hom =
      ((Φ.pullbackIso s).hom.app _ ≫ (L((s)^*[ModuleCat.{u + 1} Λ'])).map vω.hom) ≫
        (sectionInvariantTwistShiftIsoOfSection Λ' c g s hs aB).hom := by
  have hθ := Φ.map_rightDerivedUpperShriekTateObjectIsoOfSection c g s hs aB hframe
  have hτ := Φ.map_leftDerivedUpperStarTateShiftIso s (c : ℤ)
  simp only [sectionInvariantTwistShiftIsoOfSection, twistShiftConstantComplexIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (Φ.functor B) (Etale.twistShiftConstantComplexIso Λ B c).inv,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% hτ,
    reassoc_of% (hL vω (Φ.tateShiftIso V c) _ _ _ _ _ _ _ _ hθ hε)]

/-- Blueprint `proposition-relative-dualizing-complex--1`,
`proposition-compatibility-purity-change-coefficients`

**The canonical orientation `ω_f ≅ Λ_X(d)[2d]` is compatible with the change of
coefficients.** Let `f : X ⟶ Y` be smooth separated of relative dimension `d`, `Y` separated and
locally of finite type over a field, with diagonal `Δ` and first projection
`p₁ : X ×_Y X ⟶ X`, and let `vω : Ψ ω_f ≅ ω'_f`, `vω₁ : Ψ ω_{p₁} ≅ ω'_{p₁}` identify the
dualizing complexes. Assume
* `hframe`: the change of coefficients carries the frame classes of `Δ` over `Λ` to those over
  `Λ'` (the compatibility of the Kummer classes);
* `hC`: the smooth base change identifications `𝒞(p₁, Δ) ≅ ω_f`
  (`AlgebraicGeometry.Etale.sectionInvariantDiagonalIso`) correspond;
* `hε`: the isomorphisms `RΔ^! ω_{p₁} ≅ Λ_X` (composition of `R^!`) correspond;
* `hL`: the change of coefficients preserves the section invariant construction at `Δ`.

Then the canonical orientations `θ_f` (`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso`)
over `Λ` and `Λ'` correspond: `vω ≫ θ'_f = Ψ θ_f ≫ (Ψ(Λ_X(d)[2d]) ≅ Λ'_X(d)[2d])`. This is the
hypothesis `hθ` of `AlgebraicGeometry.Etale.map_smoothPurityIso_hom_comp` for the canonical
orientation. -/
theorem map_dualizingComplexTwistShiftIso {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    [SmoothOfRelativeDimension d f] [HasCompactification f] [IsSeparated f]
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X] {k : Type u} [Field k]
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiSeparatedSpace Y]
    [QuasiCompact f] [HasInvertibleExponent Λ (pullback f f)]
    [HasInvertibleExponent Λ' (pullback f f)]
    (vω : (Φ.functor X).obj (dualizingComplex Λ f) ≅ dualizingComplex Λ' f)
    (vω₁ : (Φ.functor (pullback f f)).obj (dualizingComplex Λ (pullback.fst f f)) ≅
      dualizingComplex Λ' (pullback.fst f f))
    (hframe : ∀ F : (pullback.diagonal f).EtaleFrame d, IsOpenImmersion F.e →
      Φ.mapSupportedClass _ (Φ.tateShiftIso F.U d) (frameClass Λ F) = frameClass Λ' F)
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
          (pullback.diagonal f) (pullback.diagonal_fst f)).hom)
    (hL : Φ.PreservesSectionInvariantIso (pullback.diagonal f)) :
    (Φ.functor X).map (dualizingComplexTwistShiftIso Λ f d aY).hom ≫
        (Φ.twistShiftConstantComplexIso X d).hom =
      vω.hom ≫ (dualizingComplexTwistShiftIso Λ' f d aY).hom := by
  have := SmoothOfRelativeDimension.smooth d f
  have hS := Φ.map_sectionInvariantTwistShiftIsoOfSection d (pullback.fst f f)
    (pullback.diagonal f) (pullback.diagonal_fst f) (f ≫ aY) vω₁ hframe hε hL
  have hC' : (Φ.functor X).map (sectionInvariantDiagonalIso Λ f d).inv ≫
      ((Φ.pullbackIso (pullback.diagonal f)).hom.app _ ≫
        (L((pullback.diagonal f)^*[ModuleCat.{u + 1} Λ'])).map vω₁.hom) =
      vω.hom ≫ (sectionInvariantDiagonalIso Λ' f d).inv := by
    rw [← cancel_epi ((Φ.functor X).map (sectionInvariantDiagonalIso Λ f d).hom),
      ← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp, reassoc_of% hC, Iso.hom_inv_id, Category.comp_id]
  simp only [dualizingComplexTwistShiftIso, Iso.trans_hom, Iso.symm_hom, Functor.map_comp,
    Category.assoc]
  rw [hS, ← Category.assoc, hC', Category.assoc]

end Orientation

end SupportedCoefficientChange

end Etale

end AlgebraicGeometry
