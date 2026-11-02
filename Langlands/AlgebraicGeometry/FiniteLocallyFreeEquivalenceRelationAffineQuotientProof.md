# Affine quotient proof for finite locally free equivalence relations

The theorem
`Langlands.AlgebraicGeometry.finiteLocallyFreeEquivalenceRelationAffineQuotient.{u}`
proves the published proposition
`Langlands.AlgebraicGeometry.FiniteLocallyFreeEquivalenceRelationAffineQuotientStatement.{u}`
for an arbitrary universe `u`, with exactly its stated hypotheses. It constructs
an affine scheme `M` and a finite, flat, locally finitely presented, surjective
morphism `q : U ⟶ M` for which `IsPullback t s q q`.

## Sources and attribution

The mathematical source is The Stacks Project Authors, *Groupoid Schemes*,
Proposition 39.23.9 ([Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)),
together with the surjectivity in Lemma 39.23.6
([Tag 03BL](https://stacks.math.columbia.edu/tag/03BL)). These are available in
the registered source `stacks-groupoid-schemes-chapter-pdf-2026-07-14`, PDF
pp. 50–51 and p. 47 respectively, and in the registered HTML snapshot
`stacks-finite-flat-groupoid-quotient-2026-11-01`, files `03BM.txt` and
`03BL.txt`. The quotient ring is the equalizer of the two global-section maps.
The formal conclusion is the affine quotient morphism and its kernel-pair
square specified by the published statement.

Worker 424 adapted the scheme proof from Anthropic, PBC, *Fermat's Last
Theorem in Lean 4*, registered source
`anthropic-flt-complete-lean-source-6e837e75`, commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`. The source root is
`/home/taskhub/pilot/literature/Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2/`.
The relevant source files, relative to that root, are:

- `P2M/Sol/S_AlgebraicGeometry_Scheme_exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation.lean`,
  SHA-256
  `91d680dd922b8e25fc01b46d851c7789ee7308d2afaec4a69d5a12dc0a9fafea`.
  Its `Q1AFF` namespace supplies the three preliminary lemmas and `main`
  adapted below.
- `Theorems/Thm_AlgebraicGeometry_Scheme_exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation.lean`,
  SHA-256
  `8914db4d0423caa00fc2a18b4574681e0b8117656096ebfacac565abf9bb67f0`.
  This exports the source theorem
  `AlgebraicGeometry.Scheme.exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation`.

Copyright 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0;
the Library retains `licenses/Anthropic-FLT/LICENSE`, `NOTICE`, and
`ATTRIBUTION.md`. The source attribution table has no additional entry for
these two scheme files.

The port replaces the source namespaces and export wrapper with ordinary Lean
declarations, imports the published target and the companion ring proof, uses
`s.finite_appTop` for the current finiteness API, and updates local hypotheses
to the current Lean elaboration conventions. Worker 424 wrote the final
adapter from the published pointwise hypotheses. Worker 101 ported the
companion ring theorem; its detailed provenance and proof are in
[FiniteLocallyFreeInvariantRingQuotientProof.md](FiniteLocallyFreeInvariantRingQuotientProof.md).
The implementation follows the registered Lean proof's ring reduction and
affine duality.

## Preliminary declarations

All four helper theorems below are in namespace
`Langlands.AlgebraicGeometry.FiniteLocallyFreeQuotient`, with schemes and
coordinate rings in the arbitrary universe `u`.

### `finite_projective_appTop`

For affine schemes `X` and `R`, a finite, flat, locally finitely presented
morphism `s : R ⟶ X` makes `Γ(R, ⊤)` a finite projective module over
`Γ(X, ⊤)` through `s.appTop.hom`. The theorem returns the conjunction of those
two module properties, using the algebra structure induced by that ring map.

This adapts `Q1AFF.finite_projective_appTop` from the scheme source. The proof
extracts finiteness, flatness and finite presentation of the ring map, derives
finite presentation of its underlying module, and applies Mathlib's result
that a flat finitely presented module is projective.

### `range_sup_range_eq_top`

For affine `X` and `R`, suppose `s : R ⟶ X` is finite and `s, t : R ⟶ X`
are jointly monic on morphisms from every scheme in universe `u`. Then the
images of `s.appTop.hom` and `t.appTop.hom` generate `Γ(R, ⊤)` as a subring:
their supremum is the top subring.

This adapts `Q1AFF.range_sup_range_eq_top`. Write `B₀` for that supremum.
Both maps factor through its inclusion into `Γ(R, ⊤)`. Joint monicity,
the affine identifications with spectra, and faithfulness of `Spec` show
that this inclusion is an epimorphism of commutative rings. It is finite
because its composite with the factorization of `s.appTop.hom` is finite.
Mathlib's surjectivity theorem for finite ring epimorphisms makes the
inclusion surjective, proving `B₀ = ⊤`.

### `equivalence_ringPoints`

For affine `X` and `R`, assume that `s, t : R ⟶ X` give an equivalence
relation on `T ⟶ X` for every scheme `T`. For every commutative ring `T`
in universe `u`, the relation on ring maps `Γ(X, ⊤) →+* T` defined by a
common lift `Γ(R, ⊤) →+* T` is then an equivalence relation.

This adapts `Q1AFF.equivalence_ringPoints`. The proof identifies a ring map
with the corresponding morphism from `Spec T`, followed by the inverse of
the canonical affine isomorphism. Naturality identifies the two relations.
Fullness of `Spec` supplies lifts and faithfulness reflects their endpoint
equalities. Reflexivity, symmetry and transitivity transfer across that
identification.

## `existsAffineQuotient`

This adapts the source `Q1AFF.main`. Its hypotheses are: `X` is affine;
both `s, t : R ⟶ X` are finite, flat and locally finitely presented;
they are jointly monic; and their relation on morphisms from every scheme
is an equivalence relation. Its conclusion supplies an affine `Y`,
`p : X ⟶ Y`, and `w : s ≫ p = t ≫ p`, with finiteness, flatness, local
finite presentation and surjectivity of `p`, the pullback
`IsPullback s t p p`, and a colimit cofork `Cofork.ofπ p w`.

First, finiteness of `s` makes `R` affine. Set `A = Γ(X, ⊤)`,
`B = Γ(R, ⊤)`, and `C = sr.eqLocus tr`, where `sr` and `tr` are the
global-section ring maps. The preceding three lemmas supply the finite
projective module structures, generation condition and equivalence relation
required by `invariantRingQuotient`. The inclusion `C → A` is injective
and its image is exactly the elements equalized by `sr` and `tr`.

The ring theorem gives that `A` is finite projective and faithfully flat
over `C`, and that the square with both maps `C → A` and maps `A ⇉ B`
is a pushout. Define `Y = Spec C` and compose `X.isoSpec.hom` with the
spectrum map of `C → A` to obtain `p`. Naturality gives `w`.
The finite projective and faithfully flat properties yield the four
claimed morphism properties using Mathlib's spectrum-map characterizations;
finite presentation follows from finite projectivity of the module.
The spectrum of the pushout is a pullback, and the canonical affine
isomorphisms transport it to `IsPullback s t p p`. Finally, this kernel pair
and Mathlib's effective-epimorphism instance for `p` give the colimit cofork.
This last conclusion is retained from the source helper.

## `finiteLocallyFreeEquivalenceRelationAffineQuotient`

The entry theorem is in namespace `Langlands.AlgebraicGeometry`. Its type is
exactly the imported proposition
`FiniteLocallyFreeEquivalenceRelationAffineQuotientStatement.{u}`.

The adapter introduces that proposition's schemes, arrows and hypotheses.
From `Mono (prod.lift t s)`, cancellation and product extensionality yield
joint monicity of `t` and `s`. The published reflexivity, symmetry and
transitivity conditions give an `Equivalence` on each `T ⟶ U`: symmetry
uses the reversed relation arrow, and transitivity uses a composed relation
arrow after matching the intermediate endpoints.

It then applies `existsAffineQuotient` with its arguments `s, t` instantiated
as the target's `t, s`. This preserves the exact orientation
`IsPullback t s q q`. The affine scheme, quotient morphism and its four
properties supply the target conclusion.
