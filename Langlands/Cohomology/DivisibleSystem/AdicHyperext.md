# The `ℓ`-adic hyperext spectral sequence of an `ℓ`-divisible system of complexes

Author: Worker 61. Built on the Library modules
`Langlands.Cohomology.DivisibleSystem.TowerComplex` (`towerComplex`,
`towerComplexHomologyIso`, `homComplexLimitHomologyAddEquiv`) and
`Langlands.Cohomology.HyperextSecondPage` (`secondPageExtIso`,
`isZero_secondPage_of_neg`, `precompAddEquiv`, `postcompAddEquiv`). Through
these imports it uses `hyperextSpectralSequence`, `hyperextSpectralObject` and
`abutmentIso` (`Langlands.Cohomology.HyperextSpectralSequence`),
`DivisibleSystem`, `DivisibleSystem.tower`, `DivisibleSystem.map` and
`SmoothRepComplexDivisibleSystem` (`Langlands.Cohomology.DivisibleSystem`),
`homComplexLimit` (`Langlands.Cohomology.DivisibleSystem.HomSystem`) and
`SmoothRep`. From Mathlib it uses `HomologicalComplex.single`,
`HomologicalComplex.isZero_single_obj_X`,
`HomologicalComplex.singleCompEvalIsoSelf`,
`HomologicalComplex.mkHomToSingle`, `HomologicalComplex.mkHomFromSingle`,
`HomologicalComplex.from_single_hom_ext`, `HasDerivedCategory`, the derived
category `DerivedCategory` with `DerivedCategory.Q`, `DerivedCategory.Qh`,
`DerivedCategory.quotientCompQhIso`, `DerivedCategory.singleFunctor`,
`DerivedCategory.homologyFunctor`, `DerivedCategory.homologyFunctorFactors`
and the standard t-structure `DerivedCategory.TStructure.t`, the shift
compatibility `Functor.commShiftIso` of `Q`, `Functor.mapAddHom`, and
`Abelian.Ext`, `Abelian.extFunctor` and `HasExt`.

## Conventions

`C` is an abelian category (objects in `Type u`, morphisms in `Type v`) and
`ℓ` a natural number. `ℕᵒᵖ ⥤ C` is the abelian category of inverse systems in
`C`. `T` is an `ℓ`-divisible system of cochain complexes in `C`
(`DivisibleSystem (CochainComplex C ℤ) ℓ`) with levels `T m`, and
`towerComplex T` is the published cochain complex in `ℕᵒᵖ ⥤ C` whose degree
`p` term is the inverse system `m ↦ (T m)^p`; its degree `q` cohomology is the
inverse system `m ↦ H^q(T m)` (`towerComplexHomologyIso`).

From section `Derived` on, `HasDerivedCategory.{w'} (ℕᵒᵖ ⥤ C)` is assumed:
`DerivedCategory (ℕᵒᵖ ⥤ C)` is Mathlib's derived category of inverse systems,
with morphisms in `Type w'`, `Q` is the localization functor from cochain
complexes, `(singleFunctor (ℕᵒᵖ ⥤ C) n).obj M` is `M` placed in degree `n`,
and `TStructure.t` is the standard t-structure. The Ext groups are Mathlib's
`Abelian.Ext` in `ℕᵒᵖ ⥤ C`, which require `HasExt.{w'} (ℕᵒᵖ ⥤ C)`; they are
computed in the category of inverse systems, not levelwise and not as limits
of levelwise Ext groups. These instances are hypotheses: no instance for
`ℕᵒᵖ ⥤ C` is constructed here.

## Systems placed in degree `0` (namespace `Langlands.Cohomology.DivisibleSystem`)

Here `W` is an `ℓ`-divisible system in `C`.

- `singleZero W` (`abbrev`): the `ℓ`-divisible system of complexes `m ↦ W m`
  placed in degree `0`, the image of `W` under Mathlib's
  `HomologicalComplex.single C (ComplexShape.up ℤ) 0` by the published
  `DivisibleSystem.map` (this functor is additive and preserves finite limits
  and colimits).
- `isZero_towerComplex_singleZero_X W p hp`: for `p ≠ 0` the degree `p` term
  of `towerComplex (singleZero W)` is zero, being an inverse system of zero
  objects (`HomologicalComplex.isZero_single_obj_X`).
- `towerComplexSingleZeroXIso W`: the degree `0` term of
  `towerComplex (singleZero W)` is isomorphic to `W.tower`, by Mathlib's
  `singleCompEvalIsoSelf` whiskered by `W.tower` and the right unitor.
- `towerComplexSingleZeroIso W`: an isomorphism from
  `towerComplex (singleZero W)` to `W.tower` placed in degree `0` in
  `CochainComplex (ℕᵒᵖ ⥤ C) ℤ`. Both directions are built by
  `mkHomToSingle` and `mkHomFromSingle` from `towerComplexSingleZeroXIso`; the
  conditions on the differentials hold because the neighbouring terms of
  `towerComplex (singleZero W)` are zero. The inverse laws are checked in
  degree `0` by `simp` (other degrees are zero), and on the single complex by
  `from_single_hom_ext`.

## The spectral sequence (namespace `Langlands.Cohomology.DivisibleSystem`)

Here `W : ℕᵒᵖ ⥤ C` is any inverse system.

- `towerDerivedHomologyIso T q`: the degree `q` cohomology of
  `Q.obj (towerComplex T)` is isomorphic to the inverse system
  `m ↦ H^q(T m)` (`T.tower ⋙ HomologicalComplex.homologyFunctor C _ q`). It is
  Mathlib's `homologyFunctorFactors` at `towerComplex T` followed by the
  inverse of `towerComplexHomologyIso T q`.
- `towerDerivedSingleZeroIso W` (for an `ℓ`-divisible system `W`): the image
  under `Q` of `towerComplexSingleZeroIso W`, an isomorphism from
  `Q.obj (towerComplex (singleZero W))` to `W.tower` placed in degree `0` in
  the derived category.
- `adicHyperextSpectralSequence T W`: the published
  `hyperextSpectralSequence` for the t-structure `TStructure.t`, applied to
  `Q.obj (towerComplex T)` and to `W` placed in degree `0`. It is an
  `E₂`-cohomological spectral sequence in `AddCommGrpCat.{w'}`, with objects
  indexed by `ℤ × ℤ` and differentials of bidegree `(r, 1 - r)` on page `r`.
- `adicHyperextSecondPageIso T W p q` (assuming `HasExt.{w'} (ℕᵒᵖ ⥤ C)`): for
  `p : ℕ` and `q : ℤ`, the object in position `(p, q)` on page 2 is isomorphic
  to `Ext^p(m ↦ H^{-q}(T m), W)`, the Ext group in `ℕᵒᵖ ⥤ C`. It is the
  published `secondPageExtIso` for `Q.obj (towerComplex T)` followed by the
  isomorphism of Ext groups induced, through Mathlib's `extFunctor p`, by
  `towerDerivedHomologyIso T (-q)`.
- `isZero_adicHyperextSecondPage_of_neg T W p q hp`: for `p < 0` the object
  in position `(p, q)` on page 2 is zero (the published
  `isZero_secondPage_of_neg`).
- `adicHyperextAbutmentIso T W n`: the term in degree `n` of the underlying
  spectral object `hyperextSpectralObject` for the arrow `⊥ ⟶ ⊤` of `EInt` is
  isomorphic to the group of morphisms from `Q.obj (towerComplex T)` to
  `W⟦n⟧` (`W` placed in degree `0`) in the derived category: the intended
  abutment in total degree `n`. It is the published `abutmentIso`, the
  identity.

Convergence of the spectral sequence to this abutment is not proved, here or
in the published hyperext modules.

## The comparison map (namespace `Langlands.Cohomology.DivisibleSystem`)

Here `R` is a ring, `C` is moreover `R`-linear, and
`homComplexLimit R T W` is the published inverse limit, in cochain complexes
of `R`-modules, of the Hom complexes `Hom^•(T m, W m)`.

- `homComplexLimitToDerived R T W n` (for an `ℓ`-divisible system `W` of
  complexes): an additive map from the degree `n` cohomology of
  `homComplexLimit R T W` to the group of morphisms
  `Q.obj (towerComplex T) ⟶ (Q.obj (towerComplex W))⟦n⟧` in the derived
  category. It is the published additive equivalence
  `homComplexLimitHomologyAddEquiv R T W n` with morphisms
  `towerComplex T ⟶ (towerComplex W)⟦n⟧` in the homotopy category, followed by
  the localization functor `Qh` from the homotopy category to the derived
  category (`Functor.mapAddHom`), and then by composition with Mathlib's
  isomorphisms `quotientCompQhIso` (identifying `Qh` after the quotient with
  `Q`) at `towerComplex T` and at `(towerComplex W)⟦n⟧`, and the shift
  isomorphism `(Q.commShiftIso n).app (towerComplex W)`.
- `adicHyperextComparison R T W n` (for an `ℓ`-divisible system `W` in `C`):
  an additive map from the degree `n` cohomology of
  `homComplexLimit R T (singleZero W)`, the inverse limit of the Hom complexes
  `Hom^•(T m, W m)` with `W m` placed in degree `0`, to the abutment
  `Q.obj (towerComplex T) ⟶ ((singleFunctor (ℕᵒᵖ ⥤ C) 0).obj W.tower)⟦n⟧` of
  `adicHyperextSpectralSequence T W.tower` (`adicHyperextAbutmentIso`). It is
  `homComplexLimitToDerived` for `singleZero W` followed by composition with
  the `n`-th shift of `towerDerivedSingleZeroIso W`.

The comparison map is not claimed to be injective or surjective. Bijectivity
would need hypotheses not formalized here (for example that `towerComplex T`
is K-projective in `ℕᵒᵖ ⥤ C`, so that morphisms in the homotopy category out
of it agree with morphisms in the derived category).

## Smooth representations (namespace `Langlands.Cohomology`)

For a commutative ring `R` and a group `G` with a topology, assuming
`HasDerivedCategory.{w'} (ℕᵒᵖ ⥤ SmoothRep R G)`,
`smoothAdicHyperextSpectralSequence T W` (`abbrev`) is
`adicHyperextSpectralSequence T W` for
`T : SmoothRepComplexDivisibleSystem R G ℓ` and an inverse system `W` of
smooth representations. All results above apply to it with
`C = SmoothRep R G`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), end of the proof of Proposition 4.10,
printed p.312 (one-based PDF page 14; Worker 61 read the rendered scanned
page). After checking the Mittag-Leffler condition for the complexes (4.10.2)
as `m` varies, Harris writes: "In fact, we have proved the stronger (integral)
statement

(4.10.4) `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̆_N, 𝒪(n-1)), 𝒜_ℓ(GJ, 𝓛, H)) ⇒
H^{i+j}(S̄_{K(N)}, 𝓛̃)`."

This module formalizes a spectral sequence of the same shape for
`ℓ`-divisible systems, in our own formulation. With `i = p` and `j = q`, its
second page `Ext^p(m ↦ H^{-q}(T m), W)` has the form of Harris's `E_2^{i,j}`
when `T` is a system of complexes with `H^{-j}(T m)` playing the role of
`H_c^{2(n-1)-j}` at level `m` and `W` the role of `𝒜_ℓ(GJ, 𝓛, H)`. Harris does
not say in which category his integral Ext groups are taken; reading them as
Ext groups in the category of inverse systems (in the spirit of continuous
cohomology of inverse systems) is our interpretation. In Harris's proof the
integral statement comes from the complexes (4.10.2) at the finite levels
`m`, which satisfy a Mittag-Leffler condition as `m` varies, together with
"the arguments of [H1]". The object here corresponding to the inverse limit
of such complexes of homomorphisms is `homComplexLimit`; we only provide the
comparison map `adicHyperextComparison` from its cohomology to the
derived-category abutment, and prove neither its bijectivity nor convergence.

The constructions, statements and proofs are ours; the module is derived. The
spectral sequence, its second page and its abutment are the published hyperext
modules applied to the derived category of inverse systems; the
identification of the cohomology of the limit Hom complex with morphisms in
the homotopy category is the published `homComplexLimitHomologyAddEquiv`.

## Scope

The module does not construct Harris's complexes (4.10.2), the cohomology
`H_c^{2(n-1)-j}(M̆_N, 𝒪(n-1))` or the space `𝒜_ℓ(GJ, 𝓛, H)`, and does not
identify them with `ℓ`-divisible systems. It proves no convergence, no
degeneration and no bijectivity of the comparison map, and it does not
compare the Ext groups in `ℕᵒᵖ ⥤ C` with inverse limits of levelwise Ext
groups. The existence of the derived category and of Ext groups for
`ℕᵒᵖ ⥤ C` is assumed, not proved. The smooth abbreviation is a
specialization; no smooth-specific result is proved.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
