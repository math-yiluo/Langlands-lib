# Ext computed with a projective resolution of the first argument

Author: Worker 61. Built on the Library modules
`Langlands.Cohomology.HyperextHomComplex` (`homObjComplex`, `sign`,
`cochainAddEquiv`, `cochainAddEquiv_toSingleMk`, `homComplexSingleIso`),
`Langlands.Cohomology.SmoothHyperextSecondPage` (`secondPageAddEquiv`),
`Langlands.Cohomology.ExtRightDerived` (`hasExt_smoothRep`,
`smoothExtAddEquiv`) and `Langlands.Cohomology.SmoothExt` (`SmoothExt.ext`,
by Worker 13), and on Mathlib's computation of `Ext` with projective
resolutions (`Mathlib.CategoryTheory.Abelian.Projective.Ext`) and
`Ext.subsingleton_of_projective`.

For a projective resolution `P` of an object `X`, the module identifies
`Ext^n(X, Y)` with the cohomology in degree `n` of the explicit complex
`Hom(P^{-•}, Y)` of `Langlands.Cohomology.HyperextHomComplex`, and computes
this identification on Mathlib's constructor `ProjectiveResolution.extMk`
(the sign `sign n` appears). It states the same for smooth Ext. It also
records consequences of projectivity of the first argument: the higher Ext
groups vanish, page 2 of the hyperext spectral sequence of smooth
representations vanishes off the column `p = 0` when the relevant
cohomology object is projective, and the Ext hypothesis of
`HyperextDegenerationStatement` holds when every cohomology object is
projective. `HyperextDegenerationStatement` itself is not proved.

## Setting and notation

Sections `General` and `Degeneration` take an abelian category `C` (objects
in `Type u`, morphisms in `Type v`). Section `General` assumes
`HasExt.{w} C`, so that Mathlib's `Ext.{w} X Y n` is defined;
`Degeneration` assumes `HasDerivedCategory.{w} C` and `HasExt.{w'} C`, as in
`HyperextDegenerationStatement`.

`P : ProjectiveResolution X` is Mathlib's notion: a chain complex
`P.complex` indexed by `ℕ` with projective terms and a quasi-isomorphism
`P.π` to `X` placed in degree `0`. `P.cochainComplex` is the cochain complex
indexed by `ℤ` obtained by extending `P.complex` by zero, with
`P.complex.X k` in degree `-k` and zero in positive degrees, and
`P.cochainComplexXIso (-n) n rfl` is Mathlib's isomorphism
`P.cochainComplex.X (-n) ≅ P.complex.X n`. As in
`Langlands.Cohomology.HyperextHomComplex`, `homObjComplex L Y` is the
cochain complex of abelian groups with `L.X (-n) ⟶ Y` in degree `n`, whose
differential from degree `n` to `n + 1` is precomposition with
`L.d (-(n + 1)) (-n)`, without signs, and `sign n` is the unit
`(-1)^{n(n+1)/2}` of `ℤ`. `homComplexSingleIso L Y` is the isomorphism from
Mathlib's Hom complex `HomComplex L Y₀`, with `Y₀ = (singleFunctor C 0).obj Y`
the complex with `Y` in degree `0`, to `homObjComplex L Y`; in degree `n` it
is `cochainAddEquiv L Y n`, which takes the component of a cochain from
degree `-n` to degree `0` and multiplies it by `sign n`.

Section `Smooth` takes a commutative ring `R` and a topological group `G`,
both in universe `u`, and the abelian category `SmoothRep.{u, u, u} R G` of
smooth representations of `G` on `R`-modules in `Type u`.
`SmoothExt.ext R G V n` is the `n`-th right derived functor of equivariant
`Hom(V, -)` with values in `R`-modules (Worker 13). The last theorem also
assumes `HasDerivedCategory.{w} (SmoothRep.{u, u, u} R G)`.

## Declarations

| Declaration | Statement |
| --- | --- |
| `extAddEquivHomology P Y n` | For `n : ℕ`, an additive equivalence `Ext.{w} X Y n ≃+ (homObjComplex P.cochainComplex Y).homology n`. |
| `coe_cyclesIso_hom_cyclesMap Y K n c` (lemma) | For a cochain complex `K` indexed by `ℤ` and a cycle `c` of `homObjComplex K Y` in degree `n`, the cocycle of `HomComplex K Y₀` that corresponds to `c` (the image of `c` under the map on cycles of `(homComplexSingleIso K Y).inv`, read as a cocycle through Mathlib's `HomComplex.leftHomologyData`) has underlying cochain `(cochainAddEquiv K Y n).symm ((homObjComplex K Y).iCycles n c)`. |
| `homologyAddEquiv_homologyπ K L n c` (lemma) | For cochain complexes `K`, `L` indexed by `ℤ` and a cycle `c` of Mathlib's `HomComplex K L` in degree `n`, Mathlib's `HomComplex.homologyAddEquiv K L n` sends the class of `c` to `CohomologyClass.mk` of the corresponding cocycle (again read through `HomComplex.leftHomologyData`). |
| `extAddEquivHomology_extMk P Y f m hm hf c hc` (lemma) | Let `f : P.complex.X n ⟶ Y` with `hf : P.complex.d m n ≫ f = 0`, where `hm : n + 1 = m`, and let `c` be a cycle of `homObjComplex P.cochainComplex Y` in degree `n` whose underlying morphism is `(P.cochainComplexXIso (-n) n rfl).hom ≫ f` (hypothesis `hc`). Then `extAddEquivHomology P Y n (P.extMk f m hm hf) = sign n • (homObjComplex P.cochainComplex Y).homologyπ n c`. |
| `subsingleton_ext_homology_of_projective K hK W` (theorem) | For `K : DerivedCategory C` such that `H^k(K)` is projective for every `k : ℤ` (hypothesis `hK`) and every `W : C`: for all `k : ℤ` and `i : ℕ` with `0 < i`, `Ext.{w'} (H^k(K)) W i` has at most one element. Here `H^k` is `DerivedCategory.homologyFunctor C k`. This is exactly the `Ext` hypothesis of `HyperextDegenerationStatement` for `K` and `W`. |
| `smoothExtAddEquivHomology R G P W n` | For a projective resolution `P` of a smooth representation `V` and a smooth representation `W`, an additive equivalence `(SmoothExt.ext R G V n).obj W ≃+ (homObjComplex P.cochainComplex W).homology n`. In degree `n` the complex `homObjComplex P.cochainComplex W` is the group of equivariant maps `P.cochainComplex.X (-n) ⟶ W`. |
| `isZero_ext_succ_of_projective R G V W n` (theorem) | If the smooth representation `V` is projective in `SmoothRep.{u, u, u} R G`, then `(SmoothExt.ext R G V (n + 1)).obj W` is a zero object of `R`-modules, for every `W` and `n : ℕ`. |
| `isZero_secondPage_of_projective R G K W p q hp` (theorem) | For `K` in the derived category of smooth representations, `W` a smooth representation and integers `p`, `q` with `0 < p`: if `H^{-q}(K)` is projective, the object in position `(p, q)` on page 2 of `hyperextSpectralSequence TStructure.t K ((DerivedCategory.singleFunctor _ 0).obj W)` is a zero object of `AddCommGrpCat`. |

The name `extAddEquivHomology` also occurs in
`Langlands.Cohomology.ExtRightDerived`, for an injective resolution of the
second argument; the two declarations live in different namespaces and are
not compared here.

`coe_cyclesIso_hom_cyclesMap` is the same lemma as the one of that name in
`Langlands.Cohomology.HyperextEdgeMap`, stated here without a derived
category assumption; this module does not import
`Langlands.Cohomology.HyperextEdgeMap`.

## Proofs

- `extAddEquivHomology` is the composite of three equivalences:
  1. Mathlib's `P.extAddEquivCohomologyClass`, from `Ext X Y n` to the
     cohomology classes of degree `n` from `P.cochainComplex` to `Y₀`;
  2. the inverse of Mathlib's
     `HomComplex.homologyAddEquiv P.cochainComplex Y₀ n`, from these classes
     to the cohomology in degree `n` of `HomComplex P.cochainComplex Y₀`;
  3. the isomorphism on cohomology in degree `n` induced by
     `homComplexSingleIso P.cochainComplex Y`, viewed as an additive
     equivalence.
- `coe_cyclesIso_hom_cyclesMap` combines Mathlib's
  `LeftHomologyData.cyclesIso_hom_comp_i` and
  `HomologicalComplex.cyclesMap_i`; `homologyAddEquiv_homologyπ` is
  Mathlib's `LeftHomologyData.homologyπ_comp_homologyIso_hom` applied to
  `c`.
- `extAddEquivHomology_extMk`: let `c'` be the cycle of
  `HomComplex P.cochainComplex Y₀` obtained from `sign n • c` by the map on
  cycles of `(homComplexSingleIso P.cochainComplex Y).inv`. First, step 2
  sends `P.extAddEquivCohomologyClass (P.extMk f m hm hf)` to the class of
  `c'`. To see this, apply the injective map `HomComplex.homologyAddEquiv`:
  by `homologyAddEquiv_homologyπ` and Mathlib's
  `extEquivCohomologyClass_extMk`, both sides are classes of cocycles, and
  it suffices to compare their underlying cochains. Mathlib's cocycle is
  `Cochain.toSingleMk ((P.cochainComplexXIso (-n) n rfl).hom ≫ f) _`. By
  `coe_cyclesIso_hom_cyclesMap`, additivity and `hc`, the cochain of `c'` is
  `sign n • (cochainAddEquiv _ Y n).symm ((P.cochainComplexXIso (-n) n rfl).hom ≫ f)`.
  After applying `cochainAddEquiv _ Y n`, `cochainAddEquiv_toSingleMk`
  turns Mathlib's cochain into `sign n • ((P.cochainComplexXIso (-n) n rfl).hom ≫ f)`.
  Second, step 3 sends the class of `c'` to the class of the image of `c'`
  under the map on cycles of `homComplexSingleIso P.cochainComplex Y`
  (`HomologicalComplex.homologyπ_naturality`). This image is `sign n • c`,
  because the maps on cycles induced by the inverse and the isomorphism
  compose to the identity. Finally the scalar `sign n` is moved out of
  `homologyπ` by additivity.
- `subsingleton_ext_homology_of_projective`: write `i = n + 1` and apply
  Mathlib's `Ext.subsingleton_of_projective` to the projective object
  `H^k(K)`.
- `smoothExtAddEquivHomology`: with `HasExt.{u}` supplied by
  `ExtRightDerived.hasExt_smoothRep R G` (used locally through `letI`), the
  composite of `ExtRightDerived.smoothExtAddEquiv R G V W n`, from smooth
  Ext to Mathlib's `Ext.{u} V W n`, and `extAddEquivHomology P W n`.
- `isZero_ext_succ_of_projective`: Mathlib's `Ext.subsingleton_of_projective`
  shows that `Ext V W (n + 1)` has at most one element; through
  `smoothExtAddEquiv` so does `(SmoothExt.ext R G V (n + 1)).obj W`, which
  is therefore a zero object (`ModuleCat.isZero_of_subsingleton`).
- `isZero_secondPage_of_projective`: write `p = n + 1` with `n : ℕ`. By the
  previous theorem `(SmoothExt.ext R G (H^{-q}(K)) (n + 1)).obj W` has at
  most one element, and through `SmoothHyperext.secondPageAddEquiv R G K W (n + 1) q`
  so does the page-2 object, which is therefore a zero object of
  `AddCommGrpCat`.

Together with `HyperextSpectralSequence.isZero_secondPage_of_neg` of
`Langlands.Cohomology.HyperextSecondPage` (zero for `p < 0`), `isZero_secondPage_of_projective` says that page 2 vanishes off
the column `p = 0` in every row `q` for which `H^{-q}(K)` is projective.
`SmoothHyperext.isZero_secondPage_of_injective` gives the same
conclusion for every row when `W` is injective.

## Provenance and interpretation

The statements and proofs are ours, assembled from Mathlib and the Library.
Computing `Ext` with a projective resolution of the first argument, and the
vanishing of higher `Ext` out of a projective object, are standard
homological algebra. The following passages of Harris, *Galois properties of
cohomological automorphic forms on GL(n)*, J. Math. Kyoto Univ. 39-2 (1999),
299-318 (source
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`), motivate the
module; Worker 61 read them in the rendered page scans.

- Printed p.310 (one-based PDF page 12), on the proof of Lemma 6 of Harris
  1997: "There the main step is to show that `H_c^•(M̌_N, O_m)` can be
  calculated by a complex of smooth projective `GJ`-modules over `Q_ℓ`." and
  "Projectivity of the modules `Z^{i,j}` is shown by realizing them as
  compactly induced from smooth representations `N^{i,j}` of compact (mod
  center) open subgroups `U^{i,j}` of `GJ`."
- §5, printed p.312 (one-based PDF page 14): "since `π_v` is supercuspidal,
  the higher Ext's vanish and the spectral sequence (4.10.1) degenerates to
  an isomorphism" (5.2).

Interpretation (explanation only). `smoothExtAddEquivHomology` is the
description of the classical `Ext` of Harris's `E_2` terms through a
complex of projective smooth representations, in the abstract setting of a
projective resolution of a single smooth representation.
`subsingleton_ext_homology_of_projective` and
`isZero_secondPage_of_projective` record one sufficient condition for the
vanishing of higher `Ext` groups that the degeneration (5.2) uses:
projectivity of the first argument in the category of smooth
representations. This is not Harris's argument. In (5.2) the vanishing comes
from supercuspidality of `π_v`, and the projectivity on p.310 concerns the
terms of a complex computing `H_c^•`, not its cohomology objects. Harris's
projectivity is moreover modulo the center, for compactly induced modules
over compact-mod-center open subgroups. Nothing here shows that any of
Harris's modules is projective in `SmoothRep.{u, u, u} R G`; no ring `O_m`,
group `GJ`, space `M̌_N` or complex `Z^{i,j}` is defined in this module.

## Scope

- `HyperextDegenerationStatement` is not proved. Only its `Ext` hypothesis
  is verified, and only for objects all of whose cohomology objects are
  projective.
- Projectivity is projectivity in the abelian category in question (for
  smooth representations, in `SmoothRep.{u, u, u} R G`). Projectivity
  modulo the center, compact induction and the banal hypotheses on `ℓ` are
  not treated.
- All equivalences are additive. The smooth Ext groups are `R`-modules, but
  `smoothExtAddEquivHomology` is not shown to be `R`-linear.
- No naturality in `X`, `Y`, `P`, `V` or `W` is stated, and no independence
  of the choice of projective resolution beyond the fact that each choice
  gives an equivalence with the same group `Ext X Y n`.
- The sign `sign n` in `extAddEquivHomology_extMk` depends on the
  conventions of `homComplexSingleIso` and `cochainAddEquiv` in
  `Langlands.Cohomology.HyperextHomComplex`.
- Smooth representations are those in `SmoothRep.{u, u, u} R G`, with ring,
  group and carriers in one universe `u`.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
pp.310 and 312 read in the rendered page scans.

Dependencies: `Langlands.Cohomology.HyperextHomComplex` and
`Langlands.Cohomology.SmoothHyperextSecondPage` (which imports
`Langlands.Cohomology.ExtRightDerived`, `Langlands.Cohomology.SmoothExt` and
`Langlands.Cohomology.HyperextSpectralSequence`), with Mathlib's
`Mathlib.CategoryTheory.Abelian.Projective.Ext` and
`Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives`, pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
