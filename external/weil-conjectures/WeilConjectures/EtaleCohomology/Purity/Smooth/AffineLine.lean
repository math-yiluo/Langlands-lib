/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection
public import WeilConjectures.ConstructibleSheaf.Restriction
public import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineGluing
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineRelative
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineInputs

/-!
# The affine line, `𝔾ₘ`, and the model purity

The rank-one computation that the whole of smooth purity rests on. The base `Y` is separated
of finite type over a field `k`, the coefficient ring `Λ` is finite with exponent invertible
on `Y`, and `p : 𝔸¹_Y → Y` is the projection, `s : Y → 𝔸¹_Y` the zero section and
`j : 𝔾_{m,Y} → 𝔸¹_Y` the open complement:

* the affine line is acyclic, `Rp_* Λ ≅ Λ_Y`, and `Rπ_* Λ(1)` has `Λ_Y(1)` in degree zero,
  `Λ_Y` in degree one and nothing else (`sk-prop-a1-kummer`);
* consequently `Rs^! Λ(1)[2] ≅ Λ_Y`, the *fundamental class* of the zero section
  (`sk-prop-a1`);
* a complex on `𝔸¹_Y` that is a pullback is determined by its restriction to `t = 1`, so its
  fibres at `t = 0` and `t = 1` agree (`lemma-section-normal-bundle--1`).

Iterating the one-dimensional case gives the model purity `Rz^! Λ(c)[2c] ≅ Λ_B` for the zero
section of `𝔸^c_B` (`proposition-purity-vector-bundles`), in
`WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace`.

The invertibility hypothesis is not decorative: for `Λ = ℤ/p` over a base of characteristic
`p` the Artin–Schreier sequence gives `H¹(𝔸¹_k, ℤ/p) = k[t]/(F − 1)k[t] ≠ 0`, so the affine
line is not acyclic and every statement below fails.

## Implementation notes

`𝔾_m` is not a Mathlib scheme, so the open complement of the zero section is carried as data:
a scheme `G` with an open immersion `j` whose range is the complement of the range of the
zero section. This is the same idiom as `AlgebraicGeometry.Etale.openClosedShortComplex`.

The statements that compare the twist with geometry, `R¹π_*Λ(1) ≅ Λ_Y`,
`R^mπ_*Λ(1) = 0` for `m ≥ 2` and `Rs^!Λ(1)[2] ≅ Λ_Y`, assume the twist datum normalized
(`AlgebraicGeometry.Etale.HasTateTwist.IsNormalized`); they are false for the untwisted datum
`Λ_X(m) = Λ_X` or the shifted datum `Λ_X(m) = Λ_X[-2m]` (for the latter
`R²π_*(Λ_G[-2]) = R⁰π_*Λ_G = Λ_Y ≠ 0`). The last is then the normalisation itself,
transported along the identification of the zero section with `V(t)`.

Two clauses of the blueprint are stated only in part, and are TODOs.

* `sk-prop-a1-kummer` is recorded here as what the cohomology sheaves *are* rather than as a
  statement about the generator `κ(t)` of `R¹π_*Λ(1)`; for the twist `Λ(1) = μₙ ⊗ Λ` the
  generator, the unit `p^*` in degree zero and the compatibility with base change on `Y` are in
  `WeilConjectures.EtaleCohomology.Purity.Smooth.GmRelativeKummer`
  (`AlgebraicGeometry.Etale.isIso_homology_zero_kummerClassAdjoint` and its neighbours).
  Here `sk-prop-a1` records that `Rs^!Λ(1)[2] ≅ Λ_Y`; that the boundary `∂κ(t)` of the Kummer class
  (`AlgebraicGeometry.Etale.kummerBoundary`) is this isomorphism is the orientation
  `AlgebraicGeometry.Etale.affineLineOrientation` of
  `WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation`.
* The gluing half of `lemma-section-normal-bundle--1` (ii) — that normalized local comparisons over
an étale
  cover of `Y` glue (`lemma-section-normal-bundle--1`) — is stated for a single surjective étale
  `v : Y' ⟶ Y`, the disjoint union of the members of a covering family.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_affineLine`
- `AlgebraicGeometry.Etale.nonempty_iso_homology_zero_multiplicativeGroup`,
  `AlgebraicGeometry.Etale.nonempty_iso_homology_one_multiplicativeGroup`,
  `AlgebraicGeometry.Etale.isZero_homology_multiplicativeGroup`
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineLineZero`
- `AlgebraicGeometry.Etale.injective_upperStar_map_of_isFiniteLocallyConstantSheaf`,
  `AlgebraicGeometry.Etale.injective_upperStar_oneSection_map_of_isFiniteLocallyConstantSheaf`
- `AlgebraicGeometry.Etale.eq_of_leftDerivedUpperStar_oneSection_eq`
- `AlgebraicGeometry.Etale.existsUnique_iso_leftDerivedUpperStar_of_etale`,
  `AlgebraicGeometry.Etale.exists_iso_leftDerivedUpperStar_oneSection_iff_of_etale`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]

section

variable {k : Type u} [Field k] {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [IsSeparated aY]
  [LocallyOfFiniteType aY] [HasInvertibleExponent Λ Y]

omit [HasTateTwist Λ] [HasInvertibleExponent Λ Y] in
include aY in
/-- Blueprint `sk-prop-a1-kummer`: The affine line and `𝔾ₘ` with `Λ(1)`-coefficients

*Acyclicity of the affine line*: for the projection `p : 𝔸¹_Y → Y` one has
`Rp_* Λ ≅ Λ_Y`, equivalently `R^m p_* Λ = 0` for `m > 0` and `R⁰p_*Λ = Λ_Y`. Being an
instance of smooth base change, it is compatible with base change on `Y`; on a geometric
fibre it is the vanishing `H^q(𝔸¹_k, μ_{ℓ^N}) = 0` for `q > 0`, which follows from the
Kummer sequence, the divisibility of `k^×` and `Pic(𝔸¹_k) = 0`. -/
theorem nonempty_iso_rightDerivedLowerStar_affineLine [IsAlgClosed k] [QuasiCompact aY]
    [HasInvertibleExponent Λ (Spec (.of k))] :
    Nonempty ((R((𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).obj
        (constantComplex Λ 𝔸(ULift.{u} (Fin 1); Y)) ≅ constantComplex Λ Y) := by
  obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerStar_affineLine_of_cohomology Λ aY
    (isZero_cohomology_affineLine Λ (k := k)) (cohomologyZeroConstantComplexIso Λ _)
    (constructibleFiniteTor_constantComplex Λ Y)
  exact ⟨(R((𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).mapIso
    (leftDerivedUpperStarConstantComplexIso Λ _).symm ≪≫ e⟩

omit [HasTateTwist Λ] [HasInvertibleExponent Λ Y] in
include aY in
/-- Blueprint `lem-pur-a1-direct-image`: The affine line has no higher direct images

For `B` separated of finite type over the algebraically closed field `k` and the projection
`π : 𝔸¹_B ⟶ B`, the unit `Λ_B ⟶ Rπ_* Lπ^* Λ_B = Rπ_* Λ_{𝔸¹_B}` of `Lπ^* ⊣ Rπ_*` is an
isomorphism: the affine line has no higher direct images for the constant coefficients, and its
`H⁰` is the unit. The proof computes `Rπ_* Λ ≅ RΓ(𝔸¹_k, Λ)_B ≅ Λ_B` by the Künneth formula
(in place of the stalk computation over strict henselizations by smooth base change of the
blueprint), and then the unit, split by the zero section, is an isomorphism by counting
geometric stalks. -/
theorem isIso_unit_constantComplex_affineLine [IsAlgClosed k] [QuasiCompact aY]
    [HasInvertibleExponent Λ (Spec (.of k))] :
    IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).unit.app (constantComplex Λ Y)) :=
  isIso_unit_affineLine_of_cohomology Λ aY (isZero_cohomology_affineLine Λ (k := k))
    (cohomologyZeroConstantComplexIso Λ _)
    (constructibleFiniteTor_constantComplex Λ Y) (constantComplexIsoSingleFunctor Λ Y)
    (nonempty_sheafFiber_unit_iso Λ)

include aY in
/-- The twisted affine line is acyclic: `H^m(Rp_* Λ(1)) = 0` for `m ≠ 0`, `p : 𝔸¹_Y ⟶ Y`. -/
theorem isZero_homology_rightDerivedLowerStar_tateTwist_affineLine [IsAlgClosed k]
    [QuasiCompact aY] [HasInvertibleExponent Λ (Spec (.of k))] (m : ℤ) (hm : m ≠ 0) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ m).obj
      ((R((𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).obj
        ((tateTwist Λ 𝔸(ULift.{u} (Fin 1); Y) 1).obj (constantComplex Λ _)))) := by
  obtain ⟨LT, -, hLT, ⟨eTY⟩⟩ := HasTateTwist.exists_isLocallyConstantSheaf_twistObject
    (Λ := Λ) Y 1
  obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerStar_affineLine_of_cohomology Λ aY
    (isZero_cohomology_affineLine Λ (k := k)) (cohomologyZeroConstantComplexIso Λ _)
    (boundedConstructibleFiniteTor_tateObject Λ Y 1)
  exact ((homology_props_of_iso_singleFunctor Λ eTY hLT).1 m hm).of_iso
    ((_root_.DerivedCategory.homologyFunctor _ m).mapIso
      ((R((𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).mapIso
        (derivedTensorLeftUnitor _ _ _ ≪≫
          (leftDerivedUpperStarTateObjectIso (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) 1).symm) ≪≫ e))

variable {G : Scheme.{u}} (j : G ⟶ 𝔸(ULift.{u} (Fin 1); Y)) [IsOpenImmersion j]

include aY in
/-- Blueprint `sk-prop-a1-kummer`: The affine line and `𝔾ₘ` with `Λ(1)`-coefficients

*Degree zero.* Let `j : G ↪ 𝔸¹_Y` be the open complement of the zero section — so
`G = 𝔾_{m,Y}` — and let `π = p ∘ j`. Then `R⁰π_* Λ(1) ≅ Λ_Y(1)`; on a geometric fibre this is
the Kummer computation `H⁰(𝔾_{m,k}, μ_n) = μ_n(k)`. -/
theorem nonempty_iso_homology_zero_multiplicativeGroup [IsAlgClosed k] [QuasiCompact aY]
    [HasInvertibleExponent Λ (Spec (.of k))]
    (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ) :
    Nonempty ((_root_.DerivedCategory.homologyFunctor _ 0).obj
        ((R((j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).obj
          ((tateTwist Λ G 1).obj (constantComplex Λ G))) ≅
      (_root_.DerivedCategory.homologyFunctor _ 0).obj (tateObject Λ Y 1)) := by
  have : HasInvertibleExponent Λ G := .of_hom (j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)
  let j₀ := (multiplicativeGroupModel k).ι
  have hj₀ := range_multiplicativeGroupModel_ι k
  have : HasInvertibleExponent Λ (multiplicativeGroupModel k) := .of_hom j₀
  have := connectedSpace_of_range_eq_compl_zeroSection j₀ hj₀
  obtain ⟨eG₁⟩ := nonempty_iso_cohomology_one_multiplicativeGroup Λ j₀ hj₀
  obtain ⟨LT, -, hLT, ⟨eTY⟩⟩ := HasTateTwist.exists_isLocallyConstantSheaf_twistObject
    (Λ := Λ) Y 1
  obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerStar_multiplicativeGroup_of_cohomology Λ aY j₀ hj₀
    (isZero_cohomology_multiplicativeGroup Λ j₀ hj₀) (cohomologyZeroConstantComplexIso Λ _) eG₁
    j hj
    (boundedConstructibleFiniteTor_tateObject Λ Y 1)
  exact ⟨(_root_.DerivedCategory.homologyFunctor _ 0).mapIso
    ((R((j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).mapIso
      (derivedTensorLeftUnitor _ _ _ ≪≫
        (leftDerivedUpperStarTateObjectIso (j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y) 1).symm) ≪≫ e) ≪≫
    homologyZeroBiprodShiftIso Λ _ (homology_props_of_iso_singleFunctor Λ eTY hLT).1⟩

include aY in
/-- Blueprint `sk-prop-a1`: Rank-one orientation: the fundamental class of the zero section

For the zero section `s : Y ↪ 𝔸¹_Y` the complex `Rs^! Λ(1)[2]` is concentrated in degree zero
with lisse rank-one `H⁰`; the *fundamental class* `pur_s : Λ_Y ⟶ Rs^! Λ(1)[2]` normalized to
`1` at every geometric point is therefore an isomorphism, and it is the boundary of the
Kummer class `κ(t)`.

For a normalized twist datum this is the normalisation itself
(`AlgebraicGeometry.Etale.HasKummerClass.IsNormalized`): the zero section is the closed
subscheme `V(t)` cut out by the coordinate
(`AlgebraicGeometry.AffineSpace.zeroSectionIsoZeroLocusSubscheme`), and the adjoint of the
Kummer boundary `∂κ(t)` is an isomorphism `Λ_{V(t)} ≅ Rs^! Λ(1)[2]`. The blueprint proves the
normalisation for the concrete twist by applying `Rp_*` to the localization triangle of the
closed–open pair `(s, j)` and reading off the long exact sequence with `sk-prop-a1-kummer`.

The orientation itself, `1 ↦ ∂κ(t)`, is `AlgebraicGeometry.Etale.affineLineOrientation`; that
it is an isomorphism is `AlgebraicGeometry.Etale.isIso_affineLineOrientation`, the
identification of `Hom(Λ_Y, Rs^! Λ(1)[2])` with `H²_{s(Y)}(𝔸¹_Y, Λ(1))` is
`AlgebraicGeometry.Etale.supportedClassMap_bijective`, and its uniqueness
(`prop-pur-affine-line-orientation-uniqueness`) is
`AlgebraicGeometry.Etale.eq_affineLineOrientation_iff`. -/
theorem nonempty_iso_rightDerivedUpperShriek_affineLineZero [HasTateTwist.IsNormalized Λ] :
    Nonempty ((rightDerivedUpperShriek Λ
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)).obj
        ((twistShift Λ 𝔸(ULift.{u} (Fin 1); Y) 1).obj
          (constantComplex Λ 𝔸(ULift.{u} (Fin 1); Y))) ≅
      constantComplex Λ Y) := by
  obtain ⟨K, hK, hN⟩ := HasTateTwist.IsNormalized.exists_hasKummerClass (Λ := Λ)
  subst hK
  let := K
  -- the zero section is the closed subscheme `V(t)` cut out by the coordinate
  let e := AffineSpace.zeroSectionIsoZeroLocusSubscheme (ULift.{u} (Fin 1)) Y
    (s := {AffineSpace.coord Y (ULift.up 0)}) Set.range_unique
  let ι := 𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι {AffineSpace.coord Y (ULift.up 0)}
  have he : e.hom ≫ ι = AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y :=
    AffineSpace.zeroSectionIsoZeroLocusSubscheme_hom_zeroLocusSubschemeι _ _ _
  have : HasCompactification (e.hom ≫ ι) := .of_eq he.symm
  -- the normalisation: the Kummer boundary of `t` is a fundamental class `Λ_{V(t)} ≅ Rι^! Λ(1)[2]`
  have hφ := hN.isIso_supportedClassMap_kummerBoundary_coord Y aY
  obtain ⟨heq⟩ := nonempty_iso_rightDerivedUpperShriek_of_eq Λ he.symm
  obtain ⟨comp⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ e.hom ι
  exact ⟨heq.app _ ≪≫ comp.app _ ≪≫ (rightDerivedUpperShriekIsoOfIso _ e).app _ ≪≫
    (L((e.hom)^*[ModuleCat.{u + 1} Λ])).mapIso ((R(ι)^![Λ]).mapIso
      ((shiftFunctor _ (2 * 1 : ℤ)).mapIso (derivedTensorLeftUnitor _ _ _) ≪≫
        eqToIso (by rw [mul_one])) ≪≫ (@asIso _ _ _ _ _ hφ).symm) ≪≫
    leftDerivedUpperStarConstantComplexIso Λ e.hom⟩

include aY in
/-- The degree-one part of `sk-prop-a1-kummer` for a normalized twist, from the localization
triangle: in the direct image along `p : 𝔸¹_Y ⟶ Y` of the triangle
`Rs_* Rs^! Λ(1) ⟶ Λ(1) ⟶ Rj_* Λ_G(1) ⟶` of the zero section `s` and its complement
`j : G ⟶ 𝔸¹_Y`, if `H¹(Rp_* Λ(1))` and `H²(Rp_* Λ(1))` vanish, the boundary identifies
`R¹π_* Λ(1)` with `H²(Rs^! Λ(1)) = H⁰(Rs^! Λ(1)[2]) ≅ H⁰(Λ_Y)`. -/
theorem nonempty_iso_homology_multiplicativeGroup_of_isZero [HasTateTwist.IsNormalized Λ]
    (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ)
    (n : ℤ) (h₁ : IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R((𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).obj
        ((tateTwist Λ 𝔸(ULift.{u} (Fin 1); Y) 1).obj (constantComplex Λ _)))))
    (h₂ : IsZero ((_root_.DerivedCategory.homologyFunctor _ (n + 1)).obj
      ((R((𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).obj
        ((tateTwist Λ 𝔸(ULift.{u} (Fin 1); Y) 1).obj (constantComplex Λ _))))) :
    Nonempty ((_root_.DerivedCategory.homologyFunctor _ n).obj
        ((R((j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).obj
          ((tateTwist Λ G 1).obj (constantComplex Λ G))) ≅
      (_root_.DerivedCategory.homologyFunctor _ (n - 1)).obj (constantComplex Λ Y)) := by
  have : HasInvertibleExponent Λ G := .of_hom (j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)
  let s := AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y
  let p := 𝔸(ULift.{u} (Fin 1); Y) ↘ Y
  let L := (tateTwist Λ 𝔸(ULift.{u} (Fin 1); Y) 1).obj (constantComplex Λ 𝔸(ULift.{u} (Fin 1); Y))
  have hsj : Set.range s.base = (Set.range j.base)ᶜ := by rw [hj, compl_compl]
  obtain ⟨e⟩ := nonempty_iso_homology_of_localizationTriangleLowerStar Λ p s j hsj L n h₁ h₂
  obtain ⟨π₀⟩ := nonempty_iso_rightDerivedUpperShriek_affineLineZero Λ aY
  -- `Lj^* Λ(1) ≅ Λ_G(1)`
  let eJ : (L((j)^*[ModuleCat.{u + 1} Λ])).obj L ≅ (tateTwist Λ G 1).obj (constantComplex Λ G) :=
    leftDerivedUpperStarTensorIso _ j _ _ ≪≫
      ((derivedTensor _ G).mapIso (leftDerivedUpperStarConstantComplexIso Λ j)).app _ ≪≫
        ((derivedTensor _ G).obj _).mapIso (leftDerivedUpperStarTateObjectIso j 1)
  -- `R(s ≫ p)_* = R(𝟙)_*` is the identity
  let eS : (R((s ≫ p)_*[ModuleCat.{u + 1} Λ])).obj ((R(s)^![Λ]).obj L) ≅
      (R(s)^![Λ]).obj L :=
    (rightDerivedLowerStarCongr _ (AffineSpace.zeroSection_comp_over _ Y)).app _ ≪≫
      (rightDerivedLowerStarIdIso Λ Y).app _
  exact ⟨(_root_.DerivedCategory.homologyFunctor _ n).mapIso
      ((R((j ≫ p)_*[ModuleCat.{u + 1} Λ])).mapIso eJ.symm) ≪≫ e ≪≫
    (_root_.DerivedCategory.homologyFunctor _ (n + 1)).mapIso eS ≪≫
    (((_root_.DerivedCategory.homologyFunctor _ 0).shiftIso (2 * 1 : ℤ) (n - 1) (n + 1)
      (by ring)).app _).symm ≪≫
    (_root_.DerivedCategory.homologyFunctor _ (n - 1)).mapIso
      (((R(s)^![Λ]).commShiftIso (2 * 1 : ℤ)).app L).symm ≪≫
    (_root_.DerivedCategory.homologyFunctor _ (n - 1)).mapIso π₀⟩

include aY in
/-- Blueprint `sk-prop-a1-kummer`: The affine line and `𝔾ₘ` with `Λ(1)`-coefficients

*Degree one.* In the situation above `R¹π_* Λ(1) ≅ Λ_Y`, free of rank one; on a geometric
fibre this is `H¹(𝔾_{m,k}, μ_n) = ℤ/n`, generated by the class of the coordinate `t`. For a
normalized twist this is read off from the localization triangle of the zero section
(`AlgebraicGeometry.Etale.nonempty_iso_homology_multiplicativeGroup_of_isZero`), the twisted
affine line being acyclic. -/
theorem nonempty_iso_homology_one_multiplicativeGroup [IsAlgClosed k] [QuasiCompact aY]
    [HasInvertibleExponent Λ (Spec (.of k))] [HasTateTwist.IsNormalized Λ]
    (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ) :
    Nonempty ((_root_.DerivedCategory.homologyFunctor _ 1).obj
        ((R((j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).obj
          ((tateTwist Λ G 1).obj (constantComplex Λ G))) ≅
      (_root_.DerivedCategory.homologyFunctor _ 0).obj (constantComplex Λ Y)) :=
  nonempty_iso_homology_multiplicativeGroup_of_isZero Λ aY j hj 1
    (isZero_homology_rightDerivedLowerStar_tateTwist_affineLine Λ aY 1 one_ne_zero)
    (isZero_homology_rightDerivedLowerStar_tateTwist_affineLine Λ aY (1 + 1) (by norm_num))

include aY in
/-- Blueprint `sk-prop-a1-kummer`: The affine line and `𝔾ₘ` with `Λ(1)`-coefficients

*Vanishing above degree one.* In the situation above `R^m π_* Λ(1) = 0` for `m ≥ 2`, by the
cohomological dimension of an affine curve. For a normalized twist this is read off from the
localization triangle of the zero section: `R^m π_* Λ(1) ≅ H^{m+1}(Rs^! Λ(1)) = H^{m-1}(Λ_Y)`. -/
theorem isZero_homology_multiplicativeGroup [IsAlgClosed k] [QuasiCompact aY]
    [HasInvertibleExponent Λ (Spec (.of k))] [HasTateTwist.IsNormalized Λ]
    (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ)
    (m : ℤ) (hm : 2 ≤ m) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ m).obj
      ((R((j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).obj
        ((tateTwist Λ G 1).obj (constantComplex Λ G)))) := by
  obtain ⟨e⟩ := nonempty_iso_homology_multiplicativeGroup_of_isZero Λ aY j hj m
    (isZero_homology_rightDerivedLowerStar_tateTwist_affineLine Λ aY m (by omega))
    (isZero_homology_rightDerivedLowerStar_tateTwist_affineLine Λ aY (m + 1) (by omega))
  exact (isZero_homology_constantComplex Λ Y (m - 1) (by omega)).of_iso e

set_option linter.unusedSectionVars false in
/-- Blueprint `lemma-section-normal-bundle--1`: Uniqueness for lisse sheaf maps (first assertion,
for the base `B = Y`); also clause (i) of `lemma-section-normal-bundle--1` (Weak `𝔸¹`-invariance).

*Uniqueness for lisse sheaf maps on `𝔸¹_Y`.* Two morphisms between finite locally constant
sheaves on `𝔸¹_Y` that agree after restriction to the open complement `G = 𝔾_{m,Y}` of the
zero section agree everywhere: the internal Hom is again finite locally constant, a section of
a locally constant sheaf on a connected scheme is determined by one geometric stalk, and every
connected component of `𝔸¹_Y` meets `𝔾_{m,Y}`. -/
theorem injective_upperStar_map_of_isFiniteLocallyConstantSheaf
    (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ)
    (L M : Sheaf 𝔸(ULift.{u} (Fin 1); Y).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf L] [Scheme.IsFiniteLocallyConstantSheaf M] :
    Function.Injective fun φ : L ⟶ M ↦ ((j)^*[ModuleCat.{u + 1} Λ]).map φ :=
  upperStar_map_injective_of_isLocallyConstantSheaf j (by
    rw [hj]
    exact AffineSpace.dense_compl_range_zeroSection _ _)

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- Blueprint `lemma-section-normal-bundle--1`: Uniqueness for lisse sheaf maps (second assertion,
for the base `B = Y`); also clause (i) of `lemma-section-normal-bundle--1` (Weak `𝔸¹`-invariance).

*Uniqueness for lisse sheaf maps on `𝔾_{m,Y}`.* Two morphisms between finite locally constant
sheaves on `𝔾_{m,Y}` that agree after restriction along the unit section `i₁ : Y ⟶ 𝔾_{m,Y}`
agree everywhere. This is the second assertion of clause (i), and it is what
`lemma-section-normal-bundle` Step 2 and `proposition-purity-vector-bundles` Step 3 use. -/
theorem injective_upperStar_oneSection_map_of_isFiniteLocallyConstantSheaf
    (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ)
    (i₁ : Y ⟶ G) (hi₁ : i₁ ≫ j = AffineSpace.oneSection (ULift.{u} (Fin 1)) Y)
    (L M : Sheaf G.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf L] [Scheme.IsFiniteLocallyConstantSheaf M] :
    Function.Injective fun φ : L ⟶ M ↦ ((i₁)^*[ModuleCat.{u + 1} Λ]).map φ := by
  -- `i₁` is a section of the separated `G ⟶ Y`, hence a closed immersion
  have hp : i₁ ≫ j ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) = 𝟙 Y := by
    rw [reassoc_of% hi₁, AffineSpace.oneSection_comp_over]
  have : IsClosedImmersion (i₁ ≫ j ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)) := by
    rw [hp]
    infer_instance
  have : IsClosedImmersion i₁ :=
    IsClosedImmersion.of_comp i₁ (j ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y))
  -- every fibre of `G ⟶ Y` is irreducible, being open in a fibre of `𝔸¹_Y ⟶ Y`
  refine upperStar_map_injective_of_isPreconnected i₁ fun g ↦ ?_
  let y := (𝔸(ULift.{u} (Fin 1); Y) ↘ Y).base (j.base g)
  refine ⟨j.base ⁻¹' ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y).base ⁻¹' {y}),
    ((((𝔸(ULift.{u} (Fin 1); Y) ↘ Y).isIrreducible_preimage
      (AffineSpace.isOpenMap_over (n := ULift.{u} (Fin 1)) Y)
      isIrreducible_singleton).isPreirreducible.preimage j.isOpenEmbedding).isPreconnected),
    rfl, i₁.base y, ?_, y, rfl⟩
  have := congrArg (fun f : Y ⟶ Y ↦ f.base y) hp
  simpa using this

set_option linter.unusedSectionVars false in
/-- Blueprint `lemma-section-normal-bundle--1`: Weak `𝔸¹`-invariance

*Invariance along the line.* A comparison between an invertible complex `F` on `𝔸¹_Y` and a
pullback from `Y` is determined by its restriction to the unit section `t = 1`: two
isomorphisms `α, β : F ≅ Lp^* C` with `Li₁^* α = Li₁^* β` are equal. Consequently the
identifications `Li₀^* F ≅ C ≅ Li₁^* F` obtained from such a comparison are canonical, and the
invariant is *constant* along the `𝔸¹`-direction: its values at `t = 0` and at `t = 1` agree.

Invertibility of `F` is what puts the comparison inside the lisse rank-one world in which the
uniqueness statements above apply; it is the hypothesis `lemma-section-normal-bundle--1` (ii)
imposes, in the weaker form available here (the blueprint asks that `F` be étale-locally a shift and
twist of a lisse rank-one sheaf). -/
theorem eq_of_leftDerivedUpperStar_oneSection_eq
    (F : _root_.DerivedCategory
      (Sheaf 𝔸(ULift.{u} (Fin 1); Y).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (C : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hF : DerivedCategory.isInvertible Λ 𝔸(ULift.{u} (Fin 1); Y) F)
    (α β : F ≅ (L(((𝔸(ULift.{u} (Fin 1); Y) ↘ Y))^*[ModuleCat.{u + 1} Λ])).obj C)
    (h : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) Y)^*[ModuleCat.{u + 1} Λ])).map α.hom =
      (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) Y)^*[ModuleCat.{u + 1} Λ])).map β.hom) :
    α = β := by
  let π := 𝔸(ULift.{u} (Fin 1); Y) ↘ Y
  let i₁ := AffineSpace.oneSection (ULift.{u} (Fin 1)) Y
  -- the unit section is a closed immersion, being a section of the separated `𝔸¹_Y ⟶ Y`
  have hp : i₁ ≫ π = 𝟙 Y := AffineSpace.oneSection_comp_over _ _
  have : IsClosedImmersion (i₁ ≫ π) := by
    rw [hp]
    infer_instance
  have : IsClosedImmersion i₁ := IsClosedImmersion.of_comp i₁ π
  -- the fibres of `𝔸¹_Y ⟶ Y` are irreducible and meet the unit section
  have hi : ∀ x : 𝔸(ULift.{u} (Fin 1); Y), ∃ S : Set 𝔸(ULift.{u} (Fin 1); Y),
      _root_.IsPreconnected S ∧ x ∈ S ∧ (S ∩ Set.range i₁.base).Nonempty := fun x ↦
    ⟨π.base ⁻¹' {π.base x}, (π.isIrreducible_preimage
      (AffineSpace.isOpenMap_over (n := ULift.{u} (Fin 1)) Y)
      isIrreducible_singleton).isPreirreducible.isPreconnected, rfl, i₁.base (π.base x),
      by simpa using congrArg (fun f : Y ⟶ Y ↦ f.base (π.base x)) hp, π.base x, rfl⟩
  have hγ : (L((i₁)^*[ModuleCat.{u + 1} Λ])).map (α.hom ≫ β.inv) = 𝟙 _ := by
    rw [CategoryTheory.Functor.map_comp, h, ← CategoryTheory.Functor.map_comp, β.hom_inv_id,
      CategoryTheory.Functor.map_id]
  have := eq_id_of_leftDerivedUpperStar_map_eq_id_of_isInvertible i₁ hi hF _ hγ
  exact Iso.ext (by rw [← Category.comp_id α.hom, ← β.inv_hom_id, ← Category.assoc, this,
    Category.id_comp])

set_option linter.unusedSectionVars false in
include aY in
/-- Blueprint `lemma-section-normal-bundle--1`: Invariance along the affine line

*Gluing.* Let `F ∈ D(𝔸¹_Y)`, `C ∈ D(Y)` and `θ : Li₁^* F ≅ C`. Let `v : Y' ⟶ Y` be surjective
and étale with `Y'` separated of finite type over `k`, for instance the disjoint union of an
étale covering family `{Y_α ⟶ Y}`, and write `v₁ : 𝔸¹_{Y'} ⟶ 𝔸¹_Y` for the base change of `v`
and `a' : 𝔸¹_{Y'} ⟶ Y'` for the projection. Suppose

* (local shape) `Lv₁^* F ≅ L(m)[n]` for a finite locally constant sheaf `L` on `𝔸¹_{Y'}`, free
  of rank one at every geometric point;
* (normalized local comparison) `κ' : Lv₁^* F ≅ La'^* Lv^* C` restricts along the unit section
  `i₁'` of `𝔸¹_{Y'}` to `Lv^* θ`, under `Li₁'^* La'^* ≅ 𝟭` and `Li₁'^* Lv₁^* ≅ Lv^* Li₁^*`.

Then there is a unique isomorphism `κ : F ≅ La^* C` whose restriction to `𝔸¹_{Y'}` is `κ'`,
under `Lv₁^* La^* ≅ La'^* Lv^*`.

The blueprint also asks `F` and `C` to lie in `D^b_{ctf}`; this is not imposed here, the local
shape making `F`, and through `κ'` and `θ` also `C`, étale-locally a shift and twist of a lisse
sheaf. -/
theorem existsUnique_iso_leftDerivedUpperStar_of_etale
    (F : _root_.DerivedCategory
      (Sheaf 𝔸(ULift.{u} (Fin 1); Y).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (C : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (θ : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) Y)^*[ModuleCat.{u + 1} Λ])).obj F ≅ C)
    {Y' : Scheme.{u}} (v : Y' ⟶ Y) [Etale v] [Surjective v] [IsSeparated (v ≫ aY)]
    (hF : ∃ L : Sheaf 𝔸(ULift.{u} (Fin 1); Y').smallEtaleTopology (ModuleCat.{u + 1} Λ),
      IsFiniteLocallyConstantSheaf L ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ 𝔸(ULift.{u} (Fin 1); Y')),
        Nonempty ((pointSmallEtale x).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) ∧
      ∃ m n : ℤ, Nonempty
        ((L((AffineSpace.map (ULift.{u} (Fin 1)) v)^*[ModuleCat.{u + 1} Λ])).obj F ≅
          ((tateTwist Λ _ m).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj L))⟦n⟧))
    (κ' : (L((AffineSpace.map (ULift.{u} (Fin 1)) v)^*[ModuleCat.{u + 1} Λ])).obj F ≅
      (L((𝔸(ULift.{u} (Fin 1); Y') ↘ Y')^*[ModuleCat.{u + 1} Λ])).obj
        ((L((v)^*[ModuleCat.{u + 1} Λ])).obj C))
    (hκ' : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) Y')^*[ModuleCat.{u + 1} Λ])).map
          κ'.hom ≫ (leftDerivedUpperStarCompSectionIso _ _ _
            (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) Y')).hom.app _ =
        ((leftDerivedUpperStarComp _ (AffineSpace.oneSection (ULift.{u} (Fin 1)) Y')
            (AffineSpace.map (ULift.{u} (Fin 1)) v)).inv.app F ≫
          (leftDerivedUpperStarComp _ v (AffineSpace.oneSection (ULift.{u} (Fin 1)) Y) _
            (AffineSpace.oneSection_comp_map v)).hom.app F) ≫
        (L((v)^*[ModuleCat.{u + 1} Λ])).map θ.hom) :
    ∃! κ : F ≅ (L((𝔸(ULift.{u} (Fin 1); Y) ↘ Y)^*[ModuleCat.{u + 1} Λ])).obj C,
      (L((AffineSpace.map (ULift.{u} (Fin 1)) v)^*[ModuleCat.{u + 1} Λ])).map κ.hom ≫
          (leftDerivedUpperStarComp _ (AffineSpace.map (ULift.{u} (Fin 1)) v)
            (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).inv.app C ≫
          (leftDerivedUpperStarComp _ (𝔸(ULift.{u} (Fin 1); Y') ↘ Y') v _
            (AffineSpace.map_over (n := ULift.{u} (Fin 1)) v)).hom.app C =
        κ'.hom := by
  obtain ⟨L, hL, hLs, m, n, ⟨e⟩⟩ := hF
  have : HasInvertibleExponent Λ Y' := .of_hom v
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); Y') :=
    .of_hom (𝔸(ULift.{u} (Fin 1); Y') ↘ Y')
  have : _root_.AlgebraicGeometry.Etale (AffineSpace.map (ULift.{u} (Fin 1)) v) :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale)
      (AffineSpace.isPullback_map v).flip inferInstance
  have : Surjective (AffineSpace.map (ULift.{u} (Fin 1)) v) :=
    MorphismProperty.of_isPullback (P := @Surjective) (AffineSpace.isPullback_map v).flip
      inferInstance
  have := hL
  -- the local shape: `Lv₁^* F` is invertible and a sheaf placed in degree `-n`
  obtain ⟨S, ⟨eS⟩⟩ := exists_iso_tateTwist_singleFunctor_obj L hLs m
  have hFw : DerivedCategory.isInvertible Λ _
      ((L((AffineSpace.map (ULift.{u} (Fin 1)) v)^*[ModuleCat.{u + 1} Λ])).obj F) :=
    ((isInvertible_tateTwist_singleFunctor_obj L hLs m).shift n).of_iso e.symm
  -- the local comparison as a morphism `Lv₁^* F ≅ Lv₁^* La^* C`
  let ψ : (L((AffineSpace.map (ULift.{u} (Fin 1)) v)^*[ModuleCat.{u + 1} Λ])).obj F ≅
      (L((AffineSpace.map (ULift.{u} (Fin 1)) v)^*[ModuleCat.{u + 1} Λ])).obj
        ((L((𝔸(ULift.{u} (Fin 1); Y) ↘ Y)^*[ModuleCat.{u + 1} Λ])).obj C) :=
    κ' ≪≫ ((leftDerivedUpperStarComp _ (𝔸(ULift.{u} (Fin 1); Y') ↘ Y') v _
        (AffineSpace.map_over (n := ULift.{u} (Fin 1)) v)).app C).symm ≪≫
      (leftDerivedUpperStarComp _ (AffineSpace.map (ULift.{u} (Fin 1)) v)
        (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).app C
  -- invertibility and concentration in one degree descend along `v₁`
  have hFinv := isInvertible_of_isInvertible_leftDerivedUpperStar_of_etale _ hFw
  have hGinv := isInvertible_of_isInvertible_leftDerivedUpperStar_of_etale _ (hFw.of_iso ψ)
  obtain ⟨SF, ⟨eK⟩⟩ := exists_iso_shift_singleFunctor_obj_of_leftDerivedUpperStar_iso
    (AffineSpace.map (ULift.{u} (Fin 1)) v) n (e ≪≫ (shiftFunctor _ n).mapIso eS)
  obtain ⟨SG, ⟨eM⟩⟩ := exists_iso_shift_singleFunctor_obj_of_leftDerivedUpperStar_iso
    (AffineSpace.map (ULift.{u} (Fin 1)) v) n (ψ.symm ≪≫ e ≪≫ (shiftFunctor _ n).mapIso eS)
  -- the overlap `𝔸¹_{Y' ×_Y Y'}`, on which the two pullbacks of `κ'` agree
  have hY := IsPullback.of_hasPullback v v
  have hZ := isPullback_affineSpace_map hY
  have := isClosedImmersion_oneSection (pullback v v)
  obtain ⟨κ, hκ⟩ := exists_iso_leftDerivedUpperStar_map_hom_eq_of_isPullback hFinv hGinv (-n)
    eK eM (AffineSpace.map (ULift.{u} (Fin 1)) v) hZ ψ
    (conj_leftDerivedUpperStar_eq_of_section (exists_isPreconnected_inter_range_oneSection _)
      (AffineSpace.map_over (n := ULift.{u} (Fin 1)) v)
      (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) Y)
      (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) Y')
      (AffineSpace.oneSection_comp_map v) (AffineSpace.oneSection_comp_map _)
      (AffineSpace.oneSection_comp_map _) hY.w hZ.w hFinv θ κ' hκ')
  refine ⟨κ, ?_, fun κ₂ hκ₂ ↦ ?_⟩
  · beta_reduce
    rw [hκ]
    simp [ψ]
  · -- uniqueness: comparisons out of the invertible `F` are detected after `Lv₁^*`
    beta_reduce at hκ₂
    have h₂ : (L((AffineSpace.map (ULift.{u} (Fin 1)) v)^*[ModuleCat.{u + 1} Λ])).map κ₂.hom =
        (L((AffineSpace.map (ULift.{u} (Fin 1)) v)^*[ModuleCat.{u + 1} Λ])).map κ.hom := by
      rw [hκ]
      simp only [ψ, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
      rw [← hκ₂]
      simp
    have h := eq_id_of_leftDerivedUpperStar_map_eq_id_of_isInvertible_of_surjective
      (AffineSpace.map (ULift.{u} (Fin 1)) v) hFinv (κ₂.hom ≫ κ.inv) (by
        rw [Functor.map_comp, h₂, ← Functor.map_comp, Iso.hom_inv_id,
          CategoryTheory.Functor.map_id])
    ext
    simpa using h =≫ κ.hom

-- unifying the objects of the composition and section isomorphisms is expensive
set_option linter.unusedSectionVars false in
include aY in
/-- Blueprint `lemma-section-normal-bundle--1`: Invariance along the affine line

*Uniqueness and normalization*, clauses (1) and (2). In the situation of
`AlgebraicGeometry.Etale.existsUnique_iso_leftDerivedUpperStar_of_etale`, the glued comparison
`κ : F ≅ La^* C`, whose restriction to `𝔸¹_{Y'}` is `κ'`, restricts along the unit section
`i₁` to `θ`, under `Li₁^* La^* ≅ 𝟭`; and it is the unique isomorphism `F ≅ La^* C` with this
property, so that it depends neither on the cover nor on the local comparison `κ'`. Applying
`Li₀^*` to `κ` then gives the canonical identification `Li₀^* F ≅ C` of clause (3). -/
theorem exists_iso_leftDerivedUpperStar_oneSection_iff_of_etale
    (F : _root_.DerivedCategory
      (Sheaf 𝔸(ULift.{u} (Fin 1); Y).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (C : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (θ : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) Y)^*[ModuleCat.{u + 1} Λ])).obj F ≅ C)
    {Y' : Scheme.{u}} (v : Y' ⟶ Y) [Etale v] [Surjective v] [IsSeparated (v ≫ aY)]
    (hF : ∃ L : Sheaf 𝔸(ULift.{u} (Fin 1); Y').smallEtaleTopology (ModuleCat.{u + 1} Λ),
      IsFiniteLocallyConstantSheaf L ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ 𝔸(ULift.{u} (Fin 1); Y')),
        Nonempty ((pointSmallEtale x).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) ∧
      ∃ m n : ℤ, Nonempty
        ((L((AffineSpace.map (ULift.{u} (Fin 1)) v)^*[ModuleCat.{u + 1} Λ])).obj F ≅
          ((tateTwist Λ _ m).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj L))⟦n⟧))
    (κ' : (L((AffineSpace.map (ULift.{u} (Fin 1)) v)^*[ModuleCat.{u + 1} Λ])).obj F ≅
      (L((𝔸(ULift.{u} (Fin 1); Y') ↘ Y')^*[ModuleCat.{u + 1} Λ])).obj
        ((L((v)^*[ModuleCat.{u + 1} Λ])).obj C))
    (hκ' : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) Y')^*[ModuleCat.{u + 1} Λ])).map
          κ'.hom ≫ (leftDerivedUpperStarCompSectionIso _ _ _
            (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) Y')).hom.app _ =
        ((leftDerivedUpperStarComp _ (AffineSpace.oneSection (ULift.{u} (Fin 1)) Y')
            (AffineSpace.map (ULift.{u} (Fin 1)) v)).inv.app F ≫
          (leftDerivedUpperStarComp _ v (AffineSpace.oneSection (ULift.{u} (Fin 1)) Y) _
            (AffineSpace.oneSection_comp_map v)).hom.app F) ≫
        (L((v)^*[ModuleCat.{u + 1} Λ])).map θ.hom) :
    ∃ κ : F ≅ (L((𝔸(ULift.{u} (Fin 1); Y) ↘ Y)^*[ModuleCat.{u + 1} Λ])).obj C,
      (L((AffineSpace.map (ULift.{u} (Fin 1)) v)^*[ModuleCat.{u + 1} Λ])).map κ.hom ≫
          (leftDerivedUpperStarComp _ (AffineSpace.map (ULift.{u} (Fin 1)) v)
            (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).inv.app C ≫
          (leftDerivedUpperStarComp _ (𝔸(ULift.{u} (Fin 1); Y') ↘ Y') v _
            (AffineSpace.map_over (n := ULift.{u} (Fin 1)) v)).hom.app C = κ'.hom ∧
      ∀ κ₂ : F ≅ (L((𝔸(ULift.{u} (Fin 1); Y) ↘ Y)^*[ModuleCat.{u + 1} Λ])).obj C,
        (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) Y)^*[ModuleCat.{u + 1} Λ])).map
            κ₂.hom ≫ (leftDerivedUpperStarCompSectionIso _ _ _
              (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) Y)).hom.app C = θ.hom ↔
          κ₂ = κ := by
  obtain ⟨κ, hκ, -⟩ := existsUnique_iso_leftDerivedUpperStar_of_etale Λ aY F C θ v hF κ' hκ'
  beta_reduce at hκ
  obtain ⟨L, hL, hLs, m, n, ⟨e⟩⟩ := hF
  have : HasInvertibleExponent Λ Y' := .of_hom v
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); Y') :=
    .of_hom (𝔸(ULift.{u} (Fin 1); Y') ↘ Y')
  have : _root_.AlgebraicGeometry.Etale (AffineSpace.map (ULift.{u} (Fin 1)) v) :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale)
      (AffineSpace.isPullback_map v).flip inferInstance
  have : Surjective (AffineSpace.map (ULift.{u} (Fin 1)) v) :=
    MorphismProperty.of_isPullback (P := @Surjective) (AffineSpace.isPullback_map v).flip
      inferInstance
  have := hL
  have hFinv := isInvertible_of_leftDerivedUpperStar_iso_tateTwist
    (AffineSpace.map (ULift.{u} (Fin 1)) v) L hLs m n e
  -- the restriction of `κ` to `𝔸¹_{Y'}` is `κ'`, whose restriction at `t = 1` is `Lv^* θ`
  have hψ : (L((AffineSpace.map (ULift.{u} (Fin 1)) v)^*[ModuleCat.{u + 1} Λ])).map κ.hom =
      κ'.hom ≫ (leftDerivedUpperStarComp _ (𝔸(ULift.{u} (Fin 1); Y') ↘ Y') v _
          (AffineSpace.map_over (n := ULift.{u} (Fin 1)) v)).inv.app C ≫
        (leftDerivedUpperStarComp _ (AffineSpace.map (ULift.{u} (Fin 1)) v)
          (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).hom.app C := by
    rw [← hκ]
    simp
  have hD := conj_leftDerivedUpperStar_section_eq
    (AffineSpace.map_over (n := ULift.{u} (Fin 1)) v)
    (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) Y)
    (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) Y')
    (AffineSpace.oneSection_comp_map v) θ κ' hκ'
  rw [← hψ] at hD
  have n₁ := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ)
    (AffineSpace.oneSection (ULift.{u} (Fin 1)) Y')
    (AffineSpace.map (ULift.{u} (Fin 1)) v)).hom.naturality κ.hom
  have n₂ := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) v
    (AffineSpace.oneSection (ULift.{u} (Fin 1)) Y) _
    (AffineSpace.oneSection_comp_map v)).hom.naturality κ.hom
  simp only [Functor.comp_map] at n₁ n₂
  rw [← reassoc_of% n₁, Iso.hom_inv_id_app, Category.comp_id] at hD
  have h₁ : (L((v)^*[ModuleCat.{u + 1} Λ])).map
      ((L((AffineSpace.oneSection (ULift.{u} (Fin 1)) Y)^*[ModuleCat.{u + 1} Λ])).map κ.hom) =
      (L((v)^*[ModuleCat.{u + 1} Λ])).map (θ.hom ≫ (leftDerivedUpperStarCompSectionIso _ _ _
        (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) Y)).inv.app C) := by
    rw [← cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) v
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) Y) _
      (AffineSpace.oneSection_comp_map v)).hom.app F), ← n₂, hD]
    simp
  -- hence `κ` is normalized at `t = 1`, comparisons out of `Li₁^* F` being detected after `Lv^*`
  have hnorm : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) Y)^*[ModuleCat.{u + 1} Λ])).map
      κ.hom ≫ (leftDerivedUpperStarCompSectionIso _ _ _
        (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) Y)).hom.app C = θ.hom := by
    refine eq_of_leftDerivedUpperStar_map_eq_of_isInvertible_of_surjective v
      (hFinv.leftDerivedUpperStar (AffineSpace.oneSection (ULift.{u} (Fin 1)) Y)) _ _ ?_
    rw [Functor.map_comp, h₁, ← Functor.map_comp, Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
  refine ⟨κ, hκ, fun κ₂ ↦ ⟨fun h₂ ↦ eq_of_leftDerivedUpperStar_oneSection_eq Λ F C hFinv κ₂ κ
    ((cancel_mono _).1 (h₂.trans hnorm.symm)), ?_⟩⟩
  rintro rfl
  exact hnorm
end

end Etale

end AlgebraicGeometry
