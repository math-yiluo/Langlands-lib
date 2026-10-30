# Full domain transport along bounded equivalences of the base

Worker 56 constructs transport of supplied full affinoid-domain
representations along a bounded equivalence of their actual base algebras.
The main construction is
`Langlands.Analytic.PresentedAffinoidAlgebra.Domain.transportBaseEquivalence`.

## Inputs and variance

The coefficient field `K : Type u` is a complete ultrametric normed field.
The bases `A` and `B` are `PresentedAffinoidAlgebra K`: actual quotients of
finite positive-polyradius Tate algebras by displayed closed ideals, with
their quotient norms and algebra structures. The input
`e : BoundedAlgEquiv K A B` contains mutually inverse algebra maps bounded
in both directions. It need not preserve the norms exactly.

Write `h = e.spectrumHomeomorph`. Its direction is
`BanachSpectrum B ≃ₜ BanachSpectrum A`: the forward map pulls a seminorm
back along `e`, and its inverse pulls back along `e.symm`.

A `Domain K A` stores a representing algebra `C`, a bounded base map
`i : A → C`, a closed locus `U` in `BanachSpectrum A`, equality of the
structural spectrum image with `U`, and the full unique-factorization
property against every presented positive-radius affinoid in the common
universe. The module uses that published predicate and category directly.
It imposes no reducedness, nonzero-quotient, nontrivial-valuation,
positive-arity, or nonempty-locus condition.

## Transport of the full representation property

`hasImageIn_precomp_equiv_iff` proves that a bounded map `φ : B → R`
has spectrum image in `h ⁻¹' U` exactly when `φ.comp e.toBoundedAlgHom`
has image in `U`. Evaluation on every `a : A` proves the identity of the
two comapped seminorms. The preimage membership condition then gives the
equivalence.

`Represents.precomp_equiv` keeps `C` and replaces the structural map by
`i.comp e.symm.toBoundedAlgHom : B → C` and the locus by `h ⁻¹' U`.
Its three proof clauses are as follows.

1. Closedness follows by continuous preimage along `h`.
2. For every seminorm on `C`, applying `h` after the new structural comap
   gives the old structural comap: evaluation reduces this to
   `e.symm (e a) = a`. The old exact-image equality proves forward
   containment. For reverse containment, use the old image equality to
   lift `h x`, and use injectivity of `h` to recover `x`.
3. For any presented affinoid `R` and bounded map `φ : B → R` with the
   required image containment, apply the old universal property to
   `φ.comp e.toBoundedAlgHom`. This produces a unique bounded map
   `ψ : C → R`. Evaluating its commuting equation at `e.symm b`
   proves the new equation over `B`. Conversely, evaluate a competing
   new equation at `e a` to invoke the old uniqueness clause.

The test algebra `R` is unrestricted among the presented positive-radius
affinoids. No inverse, extension, or norm-bound certificate beyond the
input bounded equivalence and the supplied full representation is added.

## Actual restrictions and the categorical equivalence

`Domain.transportBase e U` packages this transported representation.
The `transportBase_algebra`, `transportBase_baseMap`, and
`transportBase_locus` lemmas expose its data.

For an actual domain arrow `f : U ⟶ V`, `transportBaseMap e f`
retains exactly `f.restriction : V.algebra → U.algebra`. Its new equation
over `B` follows from the old equation by associativity of bounded-map
composition. `transportBaseMap_restriction` records this equality, and
`transportBaseFunctor` verifies identity and composition by extensionality
of actual restriction maps.

`transportBase_symm_baseMap` shows that transporting by `e` and then by
`e.symm` restores the base map, by evaluating the two maps on elements
and using the inverse identity. `transportBase_symm_locus` similarly
restores the represented subset, by evaluating the twice-comapped
seminorm on each base element.

`transportBaseRoundTripIso` makes this round trip into an isomorphism in
the domain category. Both restrictions are bounded identity algebra
maps on the retained representing algebra. The restored base-map
equation proves that they are arrows over the original base; their
composites are the actual identities.

`transportBaseEquivalence` uses the functors for `e` and `e.symm`.
Its unit is the inverse round-trip isomorphism, and its counit is the
round-trip isomorphism for `e.symm`. Naturality and the required triangle
equation hold by extensionality of restriction maps: the remaining maps
are identities on the retained algebras. This constructs an equivalence
of the actual categories, including their bounded arrows.

## Compatibility with topology and realizations

`transportBase_spectrumMap` proves that applying `h` to the new
structural spectrum map gives the old map on the unchanged quotient
spectrum. It uses the seminorm identity from the representation proof.

`transportBaseLocusHomeomorph` restricts `h` to a homeomorphism from the
transported locus to the original locus, using Mathlib's restriction of
a homeomorphism to corresponding subsets. The theorem
`transportBase_spectrumToLocus` proves compatibility with the actual
maps from the quotient spectrum to the loci, by subtype extensionality
and the structural spectrum equation.

`transportBaseLocusHomeomorph_naturality` says that these homeomorphisms
commute with every domain arrow's continuous locus inclusion. The
underlying points on both sides are definitionally the same.

The two functor equalities
`transportBaseFunctor_toAffinoidSpace` and
`transportBaseFunctor_toTopologicalSpace` hold by reflexivity:
transport retains each quotient algebra and restriction exactly, so
both its algebra realization in the opposite category and its
quotient-spectrum realization are unchanged.

The locus homeomorphism here compares subsets of two base spectra.
Injectivity of a generic representing-spectrum map to its locus remains
a separate obligation. The module constructs no new rational
representation, intersection, atlas, structure sheaf, or site.

## Provenance

This is derived internal transport of the published full representation
predicate and bounded category. The registered original is V. G.
Berkovich, *Non-archimedean analytic spaces* (Trieste lectures, 2009),
source ID `berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.1.11, printed/PDF p.8, supplies the category dual to bounded
affinoid algebra maps. Definition 2.2.1, p.9, supplies the full
closed-locus representation property. Definition 2.2.7, p.10, supplies
the affinoid-domain embedding convention.

The source does not separately name this base-transport equivalence.
The construction follows by substituting mutually inverse bounded base
maps into Definition 2.2.1, as proved above. Existing bounded-equivalence
and spectrum machinery supplies the topological maps. The related
strict-test calculus changes a representing algebra for a fixed base;
this module changes the base and proves the full property for every
positive-radius test.
