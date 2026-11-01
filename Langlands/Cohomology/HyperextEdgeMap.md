# The edge map of the hyperext spectral sequence on a K-projective complex

Author: Worker 61. Built on the Library modules
`Langlands.Cohomology.HyperextHomComplex` (`homObjComplex`, `sign`,
`cochainAddEquiv`, `homComplexSingleIso`, `cohomologyClassAddEquiv`,
`homObjHomologyAddEquiv`) and
`Langlands.Cohomology.HyperextDegeneration.Statement` (`edgeMap`), and on
Mathlib's homology of complexes, Hom complexes and derived categories.

Let `P` be a cochain complex in an abelian category `C`, `W` an object of
`C`, and `W₀` the complex with `W` in degree `0` and zero elsewhere. The edge
map `HyperextDegeneration.edgeMap (Q.obj P) W n` sends a morphism
`Q.obj P ⟶ W₀⟦n⟧` of the derived category to the morphism
`H^{-n}(Q.obj P) ⟶ W` it induces on cohomology in degree `-n`. When `P` is
K-projective, `homObjHomologyAddEquiv` identifies the source of the edge map
with the cohomology in degree `n` of the explicit complex `Hom(P^{-•}, W)`.
This module computes the edge map in these terms: the class of a cocycle
`f : P.X (-n) ⟶ W` goes to `sign n` times the morphism that `f` induces on
`P.homology (-n)`. Consequently the edge map is bijective exactly when this
"restriction" map is.

This module does **not** prove `HyperextDegenerationStatement`. It treats
only objects of the derived category of the form `Q.obj P` with `P`
K-projective, it makes no assumption on `Ext` groups, and it does not show
that the restriction map is bijective in any case.

## Restriction to cohomology of `P`

Section `Restriction` takes an abelian category `C` (objects in `Type u`,
morphisms in `Type v`), a cochain complex `P : CochainComplex C ℤ`, an object
`W : C` and an integer `n`. Recall from
`Langlands.Cohomology.HyperextHomComplex` that `homObjComplex P W` has the
group `P.X (-n) ⟶ W` in degree `n`, and that its differential from degree `n`
to degree `n + 1` sends `f` to `P.d (-(n + 1)) (-n) ≫ f`. For a cycle `c` of
`homObjComplex P W` in degree `n`, `(homObjComplex P W).iCycles n c` is the
underlying morphism `P.X (-n) ⟶ W`. `P.iCycles (-n)` is the inclusion of the
cycles of `P` in degree `-n` into `P.X (-n)`, and `P.homologyπ (-n)` the
projection from these cycles onto `P.homology (-n)`.

| Declaration | Statement |
| --- | --- |
| `homologyDesc P W n f hf` | For `f : P.X (-n) ⟶ W` and `hf : P.d (-(n + 1)) (-n) ≫ f = 0`, the morphism `P.homology (-n) ⟶ W` induced by `P.iCycles (-n) ≫ f`. It is defined with Mathlib's `HomologicalComplex.homologyIsCokernel`, which presents `P.homology (-n)` as the cokernel of the map from `P.X (-(n + 1))` to the cycles in degree `-n`. |
| `homologyπ_homologyDesc` | `P.homologyπ (-n) ≫ homologyDesc P W n f hf = P.iCycles (-n) ≫ f` (a `simp` and `reassoc` lemma). |
| `d_comp_iCycles_apply P W n c` | For a cycle `c` of `homObjComplex P W` in degree `n`: `P.d (-(n + 1)) (-n) ≫ (homObjComplex P W).iCycles n c = 0`. |
| `cyclesRestriction P W n` | The morphism of abelian groups `(homObjComplex P W).cycles n ⟶ AddCommGrpCat.of (P.homology (-n) ⟶ W)` sending `c` to `homologyDesc P W n ((homObjComplex P W).iCycles n c) _`. |
| `restriction P W n` | The morphism of abelian groups `(homObjComplex P W).homology n ⟶ AddCommGrpCat.of (P.homology (-n) ⟶ W)` induced by `cyclesRestriction P W n`, using Mathlib's presentation of `(homObjComplex P W).homology n` as a cokernel (`homologyIsCokernel` for the degrees `n - 1` and `n`). |
| `homologyπ_restriction P W n c` | `P.homologyπ (-n) ≫ restriction P W n ((homObjComplex P W).homologyπ n c) = P.iCycles (-n) ≫ (homObjComplex P W).iCycles n c`. |
| `toSingleEquiv_cochainAddEquiv_symm P W n f` | For `f : P.X (-n) ⟶ W`: `Cochain.toSingleEquiv _ ((cochainAddEquiv P W n).symm f) = sign n • f`. |
| `cyclesMap_eq_liftCycles φ i j hj` | For a morphism `φ : K ⟶ L` of cochain complexes indexed by `ℤ` and `j` the degree after `i`: `HomologicalComplex.cyclesMap φ i = L.liftCycles (K.iCycles i ≫ φ.f i) j hj _`. |

So `restriction P W n` sends the class of a cocycle `f : P.X (-n) ⟶ W` to
the morphism that `f` induces on `P.homology (-n)`. It is well defined
because a coboundary `P.d (-n) (-(n - 1)) ≫ g` vanishes on the cycles of `P`.

Proofs. `cyclesRestriction` is additive and `restriction` is well defined
because each side becomes equal after composing with the epimorphism
`P.homologyπ (-n)`; for a coboundary, Mathlib's
`HomologicalComplex.toCycles_i` writes its underlying morphism as
`P.d (-n) (-(n - 1)) ≫ g`, and `HomologicalComplex.iCycles_d` gives
`P.iCycles (-n) ≫ P.d (-n) _ = 0`. `homologyπ_restriction` combines the
factorization property of the cokernel with `homologyπ_homologyDesc`.
`toSingleEquiv_cochainAddEquiv_symm` uses `sign n * sign n = 1`: since
`cochainAddEquiv P W n` is `Cochain.toSingleEquiv` followed by
multiplication by `sign n`, `Cochain.toSingleEquiv g = sign n • cochainAddEquiv P W n g`
for every cochain `g`. `cyclesMap_eq_liftCycles` follows by composing both
sides with the monomorphism `L.iCycles i`.

## The edge map

Section `Derived` adds `HasDerivedCategory.{w} C`. `Q` is the localization
functor from cochain complexes to `DerivedCategory C`, `W₀` is
`(CochainComplex.singleFunctor C 0).obj W`, and
`DerivedCategory.homologyFunctorFactors C k` is Mathlib's identification of
`H^k(Q.obj P)` with `P.homology k`; its inverse at `P` is a morphism
`P.homology (-n) ⟶ H^{-n}(Q.obj P)`. `edgeMap` is
`HyperextDegeneration.edgeMap` from
`Langlands.Cohomology.HyperextDegeneration.Statement`.

| Declaration | Statement |
| --- | --- |
| `cohomologyClassAddEquiv_apply P L n x` | For `P` K-projective and a cohomology class `x` of degree `n` of Mathlib's Hom complex from `P` to `L`, `cohomologyClassAddEquiv P L n x` is the composite of the inverse of `(quotientCompQhIso C).app P`, `Qh.map (CohomologyClass.toHom x)`, `(quotientCompQhIso C).hom.app (L⟦n⟧)` and `(Q.commShiftIso n).hom.app L` (by definition). |
| `cohomologyClassAddEquiv_mk P L n z` | For `P` K-projective and a cocycle `z : Cocycle P L n`: `cohomologyClassAddEquiv P L n (CohomologyClass.mk z) = ShiftedHom.map (Cocycle.equivHomShift.symm z) Q`. Here `Cocycle.equivHomShift.symm z : P ⟶ L⟦n⟧` is the morphism of complexes corresponding to `z`, and `ShiftedHom.map f Q` is `Q.map f ≫ (Q.commShiftIso n).hom.app L`. |
| `homologyFunctorFactors_inv_app_singleFunctorCompHomologyFunctorIso W` | `(homologyFunctorFactors C 0).inv.app W₀ ≫ (singleFunctorCompHomologyFunctorIso C 0).hom.app W = (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 W).hom`: the identification `H^0(W₀) ≅ W` used by `edgeMap`, transported to the cohomology of the complex `W₀`, is Mathlib's isomorphism for single complexes. |
| `homologyπ_comp_edgeMap_map P W n φ` | For every morphism of complexes `φ : P ⟶ W₀⟦n⟧` (no K-projectivity assumed): `P.homologyπ (-n) ≫ (homologyFunctorFactors C (-n)).inv.app P ≫ edgeMap (Q.obj P) W n (ShiftedHom.map φ Q) = P.iCycles (-n) ≫ φ.f (-n) ≫ (W₀.shiftFunctorObjXIso n (-n) 0 _).hom ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 W).hom`, where the last two isomorphisms identify `(W₀⟦n⟧).X (-n)` with `W₀.X 0` and `W₀.X 0` with `W`. |
| `homologyπ_comp_edgeMap_mk P W n z` | For `P` K-projective and a cocycle `z : Cocycle P W₀ n`: `P.homologyπ (-n) ≫ (homologyFunctorFactors C (-n)).inv.app P ≫ edgeMap (Q.obj P) W n (cohomologyClassAddEquiv P W₀ n (CohomologyClass.mk z)) = P.iCycles (-n) ≫ Cochain.toSingleEquiv _ z`, where `Cochain.toSingleEquiv _ z : P.X (-n) ⟶ W` is the component of `z` from degree `-n` to degree `0`. No sign appears. |
| `homObjHomologyAddEquiv_homologyπ P W n c` | For `P` K-projective and a cycle `c` of `homObjComplex P W` in degree `n`: `homObjHomologyAddEquiv P W n ((homObjComplex P W).homologyπ n c)` is `cohomologyClassAddEquiv P W₀ n` applied to the class of the cocycle of `HomComplex P W₀` that corresponds to `c` under `homComplexSingleIso` (the image of `c` under the map on cycles of `(homComplexSingleIso P W).inv`, read as a cocycle through Mathlib's `HomComplex.leftHomologyData`). |
| `coe_cyclesIso_hom_cyclesMap P W n c` | The underlying cochain of the cocycle in the previous row is `(cochainAddEquiv P W n).symm ((homObjComplex P W).iCycles n c)`. This lemma needs only `[Abelian C]`. |
| `homologyπ_comp_edgeMap P W n c` | For `P` K-projective and a cycle `c` of `homObjComplex P W` in degree `n`: `P.homologyπ (-n) ≫ (homologyFunctorFactors C (-n)).inv.app P ≫ edgeMap (Q.obj P) W n (homObjHomologyAddEquiv P W n ((homObjComplex P W).homologyπ n c)) = sign n • (P.iCycles (-n) ≫ (homObjComplex P W).iCycles n c)`. |
| `comp_edgeMap_homObjHomologyAddEquiv P W n x` | For `P` K-projective and every `x` in the cohomology of `homObjComplex P W` in degree `n`: `(homologyFunctorFactors C (-n)).inv.app P ≫ edgeMap (Q.obj P) W n (homObjHomologyAddEquiv P W n x) = sign n • restriction P W n x`. |
| `bijective_edgeMap_iff P W n` | For `P` K-projective: `edgeMap (Q.obj P) W n` is bijective if and only if `restriction P W n` is bijective. |

In words, `comp_edgeMap_homObjHomologyAddEquiv` says that the square formed
by `homObjHomologyAddEquiv P W n`, the edge map, the identification
`P.homology (-n) ≅ H^{-n}(Q.obj P)` and `restriction P W n` commutes up to
the sign `sign n = (-1)^{n(n+1)/2}`.

Where the sign comes from. The edge map itself introduces no sign
(`homologyπ_comp_edgeMap_mk`): on the class of a cocycle of Mathlib's Hom
complex it is the restriction of the component of degree `-n` to `0`. The
sign comes from `homComplexSingleIso` of
`Langlands.Cohomology.HyperextHomComplex`, which identifies Mathlib's Hom
complex `HomComplex P W₀` (whose differential has signs) with the unsigned
complex `homObjComplex P W` by multiplying the component of degree `n` by
`sign n`. The sign is proved as it comes out of these conventions; the
definitions of `HyperextHomComplex` are not changed.

Proofs.

- `homologyFunctorFactors_inv_app_singleFunctorCompHomologyFunctorIso`
  unfolds Mathlib's `singleFunctorCompHomologyFunctorIso` and cancels the
  isomorphisms `homologyFunctorFactors`.
- `homologyπ_comp_edgeMap_map`: Mathlib's `shiftMap_homologyFunctor_map_Q`
  rewrites the `shiftMap` in `edgeMap` as
  `(homologyFunctorFactors C (-n)).hom.app P`, followed by the `shiftMap`
  of `φ` for the homology functor of complexes, followed by
  `(homologyFunctorFactors C 0).inv.app _`. The first factor cancels against
  `(homologyFunctorFactors C (-n)).inv.app P`, and the last one combines with
  `singleFunctorCompHomologyFunctorIso` by the previous lemma. On complexes,
  the `shiftMap` of `φ` is `HomologicalComplex.homologyMap φ (-n)` followed
  by the isomorphism `shiftIso`. By `homologyπ_naturality` and
  `cyclesMap_eq_liftCycles`, `P.homologyπ (-n) ≫ homologyMap φ (-n)` is
  `liftCycles (P.iCycles (-n) ≫ φ.f (-n))` followed by `homologyπ`.
  Mathlib's `liftCycles_shift_homologyπ` moves this across the shift
  isomorphism. The lemmas `homologyπ_singleObjHomologySelfIso_hom`,
  `singleObjCyclesSelfIso_hom` and `liftCycles_i` finish the computation.
- `homologyπ_comp_edgeMap_mk`: rewrite with `cohomologyClassAddEquiv_mk`
  and apply the previous lemma to `φ = Cocycle.equivHomShift.symm z`. By
  Mathlib's `Cochain.rightShift_v`, the component of `φ` in degree `-n` is
  the component of `z` from `-n` to `0` followed by the inverse of
  `W₀.shiftFunctorObjXIso n (-n) 0 _`, so the shift isomorphisms cancel.
  What remains is the definition of `Cochain.toSingleEquiv`.
- `homObjHomologyAddEquiv_homologyπ`: by definition,
  `homObjHomologyAddEquiv` is the inverse of the map on cohomology induced
  by `homComplexSingleIso P W`, which is the map induced by its inverse,
  followed by Mathlib's `HomComplex.homologyAddEquiv` and
  `cohomologyClassAddEquiv`. `homologyπ_naturality` moves the class of `c`
  across the first map, and `LeftHomologyData.homologyπ_comp_homologyIso_hom`
  computes `HomComplex.homologyAddEquiv` on classes of cycles.
- `coe_cyclesIso_hom_cyclesMap` combines Mathlib's
  `LeftHomologyData.cyclesIso_hom_comp_i` and
  `HomologicalComplex.cyclesMap_i`.
- `homologyπ_comp_edgeMap` chains `homObjHomologyAddEquiv_homologyπ`,
  `homologyπ_comp_edgeMap_mk`, `coe_cyclesIso_hom_cyclesMap` and
  `toSingleEquiv_cochainAddEquiv_symm`, and moves the scalar out of the
  composition.
- `comp_edgeMap_homObjHomologyAddEquiv`: every element `x` is the class of a
  cycle (`homologyπ` is an epimorphism of abelian groups, hence surjective by
  Mathlib's `AddCommGrpCat.epi_iff_surjective`). Both sides agree after
  composing with the epimorphism `P.homologyπ (-n)`, by
  `homologyπ_comp_edgeMap` and `homologyπ_restriction`.
- `bijective_edgeMap_iff`: the map `g` sending `φ` to
  `sign n • ((homologyFunctorFactors C (-n)).inv.app P ≫ φ)` is a bijection,
  with inverse `ψ ↦ sign n • ((homologyFunctorFactors C (-n)).hom.app P ≫ ψ)`,
  because `sign n * sign n = 1`. By `comp_edgeMap_homObjHomologyAddEquiv`,
  `restriction P W n` is the composite of `homObjHomologyAddEquiv P W n`,
  the edge map and `g`. Composing with bijections on either side preserves
  and reflects bijectivity.

## Provenance and interpretation

The statements and proofs are ours, assembled from Mathlib and the Library.
The edge map is the one of `HyperextDegenerationStatement` (Worker 3),
whose Markdown relates it to the degeneration steps in Harris 1997 ((10) to
(11), p.96) and Harris 1999 ((4.10.1) to (5.2), p.312). For this module
Worker 61 re-read the following passage of Harris 1999 in the PDF:

- Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
  J. Math. Kyoto Univ. 39-2 (1999), 299-318 (source
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`), §5,
  printed p.312 (one-based PDF page 14): "since `π_v` is supercuspidal, the
  higher Ext's vanish and the spectral sequence (4.10.1) degenerates to an
  isomorphism" (5.2).

As recorded in the Markdown of `Langlands.Cohomology.HyperextHomComplex`,
Harris computes the abutment of his spectral sequences with a complex of
smooth projective modules (Harris 1999 printed p.310, referring to the proof
of Lemma 6 of Harris 1997). The present module is a derived, internal step
for such a complex `P`: it identifies the edge homomorphism, which the
degeneration (5.2) asserts to be an isomorphism under the vanishing of the
higher `Ext` groups, with the explicit map "restrict a cocycle
`P^{-n} ⟶ W` to the cohomology of `P`", up to the sign `sign n`. By
`bijective_edgeMap_iff`, proving degeneration for `Q.obj P` amounts to
proving that this explicit map is bijective. Neither the vanishing of `Ext`
groups nor the bijectivity is proved here.

Specialization (explanation only). In Harris's situation `C` would be a
category of smooth representations, `W` the coefficient module, and `P` a
complex of projective smooth representations computing compactly supported
cohomology up to shift and Tate twist. None of this is formalized here; see
the Scope section of `Langlands.Cohomology.HyperextHomComplex`.

## Scope

- `HyperextDegenerationStatement` is not proved. Only objects `Q.obj P`
  with `P` K-projective are treated (`homologyπ_comp_edgeMap_map` holds for
  any `P`, but only for morphisms of the form `ShiftedHom.map φ Q`).
- No `Ext` hypothesis appears, and bijectivity of `restriction P W n` is
  not proved in any case.
- The sign `sign n` depends on the conventions of `homComplexSingleIso` and
  `cochainAddEquiv` in `Langlands.Cohomology.HyperextHomComplex`.
- All maps are additive or set-theoretic; no linearity over a coefficient
  ring and no naturality in `P` or `W` is stated.
- `HasDerivedCategory.{w} C` is a hypothesis; the results hold for each such
  instance.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
p.312 read in the PDF (text layer and rendered page).

Dependencies: `Langlands.Cohomology.HyperextHomComplex` and
`Langlands.Cohomology.HyperextDegeneration.Statement`, with Mathlib pinned
to Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
