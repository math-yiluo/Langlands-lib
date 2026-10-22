# Filtered colimits and cohomology of module complexes

Author: Worker 3. These are theorem-statement definitions, not proofs.
Every component remains a separate theorem obligation.

The five propositions concern actual modules over an arbitrary ring, actual
integer-graded cochain complexes, and their categorical colimits:

1. `FilteredColimitExactnessStatement`: the colimit of a short exact sequence
   of filtered module diagrams is short exact.
2. `FilteredColimitCohomologyStatement`: the canonical map
   `colim_j H^q(K_j) -> H^q(colim_j K_j)` is invertible.
3. `ColimitCohomologyNaturalityStatement`: that canonical map commutes with
   a natural transformation between the complex diagrams. This equality
   holds even when the indexing category is not filtered.
4. `FilteredColimitQuasiIsoStatement`: taking a filtered colimit preserves
   a pointwise quasi-isomorphism of complexes.
5. `FilteredColimitCohomologyEquivarianceStatement`: a monoid action on the
   diagram by natural transformations gives an isomorphism of the induced
   actions whose underlying map is exactly the canonical comparison.

`FilteredColimitComparisonStatements` conjoins these five targets. No target
assumes any of the other targets, an exact-colimit hypothesis, or the desired
isomorphism as data.

The ring universe `u` is independent of `v`, which bounds both the small
indexing category and module carriers. The acting monoid has independent
universe `w`. The ring need not be commutative. The complexes are unbounded
and their differential raises degree by one. No finiteness, surjective
transition, or Mittag-Leffler assumption is imposed.

Mathlib constructs colimits of the complexes degreewise. The displayed map is
`colimit.post K (HomologicalComplex.homologyFunctor ... q)`: its composite
with each colimit injection is the cohomology map induced by the corresponding
injection of complexes. Neither its existence nor its definition requires
cohomology to preserve colimits. The naturality equation uses `colimMap`
and whiskering by the actual homology functor.

The action in the fifth target is an actual Mathlib `Action` on the diagram
category. Applying the two functors, respectively cohomology then colimit and
colimit then cohomology, constructs the two action objects. The target demands
an isomorphism of those actions and identifies its underlying morphism.
It supplies no continuity, smoothness, moving-index action or Galois action.
Those remain separate geometric and representation-theoretic obligations.

## Original sources and derived scope

Cartan and Eilenberg, *Homological Algebra*, Princeton University Press,
1956 printing, Chapter V, section 9, Proposition 9.3*, printed p.100
(PDF p.122), states and proves that cycles, the corresponding quotient, and
homology commute with direct limits. The proof induces the comparison from
the maps on homology of the canonical maps to the direct limit, and checks it
using representatives at a common later stage. Section 9, pp.99-100, specifies
the direction of the comparison.
Chapter IV, section 3, pp.58-59, gives the cochain convention.

Registered original:
`provided-4e029ea5216cb6ce6bfc05060277910b86f223b69bc92c508711e3760612bd4e`.
Retained file:
`literature/Cartan-Eilenberg 1956 original- resolution comparison and derived functors.pdf`.
PDF SHA-256:
`1e0915f23ec4a4bd638f469561931f5659a7a47faf92d48468bd290ddd726365`.

The source uses directed systems. Our formulation uses small filtered
categories: common later stages and equalization of parallel arrows provide
the same finite representative arguments. This categorical extension is
explicitly derived, not a quotation of the source's indexing convention.
Exactness follows by applying the cohomology assertion to the three-term
complex of a short exact sequence. Naturality follows from the colimit
injections. The quasi-isomorphism assertion follows from naturality, the
comparison isomorphisms and colimits of a natural isomorphism of cohomology
diagrams. Algebraic equivariance follows by applying naturality to each
monoid operator; the isomorphism conclusion also uses the comparison result.
These are explanations of provenance, not Lean proofs.

Grothendieck, EGA III.0, section 11.2.4, printed p.29 (continuous p.373;
PDF p.25 of the supplied preliminaries), explicitly uses commutation of
cohomology with filtered inductive limits under exactness of those limits.
Its discussion of exhaustive and regular filtrations is additional scope,
not asserted by this pair. Section 11.2.1, p.27, fixes integer grading and
differential degree +1.

Registered source folder:
`provided-bca66cf9ddf1864d04cd9ab13db3799e640164f5476bbe9ed23714ccc825ed03`,
folder SHA-256
`fb65e01feda254662655043bb84b343601696054c02f2c05f42548e66042f1d4`.
Member:
`Grothendieck--Preliminaires (EGA III-1, Chapitre 0, sections 8-13)--1961.pdf`,
SHA-256
`24cb7a75e125f44022411d4b2a86afd2453ab45876945e0ee02b5dd8d5dc5655`.

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed p.306, takes the direct
limit as a compact open subgroup shrinks, obtains the equivariant
quasi-isomorphism (2.6), and deduces the cohomology comparison (2.7).
The present family isolates the algebraic colimit step. It does not construct
those particular complexes, prove projectivity of their terms, or establish
their geometric coefficient and group-action hypotheses. Lemma 2.8 on the
same page instead concerns an inverse limit and has its separate
Mittag-Leffler prerequisites.

Registered source:
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
PDF SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Worker 3 read CE Chapter V pp.75-105 and IV.1-5 pp.53-64, EGA III.0
11.2.1-4 pp.27-29, and Harris 1999 in full. The actual source hashes were
verified, and CE p.100, EGA p.29 and Harris p.306 were visually inspected
for this contribution. The EGA citation does not claim a filtered-colimit
theorem without its printed exactness premise for a general abelian category;
the unconditional targets here concern modules specifically.

## Formal dependencies and checks

The only formal dependency is the pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0. In particular:

- `ModuleCat.Colimits` constructs the module colimits from abelian-group
  colimits, with their induced scalar operations.
- `HomologicalComplexLimits` constructs the colimit complex degreewise,
  including its differential and the equations for a cochain complex.
- `Limits.HasLimits` defines `colimit.post` and its injection equation by
  dualizing the limit construction. It does not assume preservation.
- `QuasiIso`, `ShortComplex.ShortExact`, and `Action` are Mathlib's actual
  predicates and action objects.

In the project environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
(Lean 4.34.0, the Mathlib commit above), development check
`dcb65e39-6f6f-4f88-a796-77c07e119740` passed the Lake build of this module
with no errors or warnings and inspected
`Langlands.Cohomology.FilteredColimitComparisonStatements` as a definition
returning `Prop`, with universe parameters `u`, `v`, `w`, target fingerprint
`f3804ab9599fc8879029da5b78b0e6469ca0c62407fd664351b50b05ae3d77ca`, and
only the axioms `propext`, `Classical.choice` and `Quot.sound`.
The checked Lean source has SHA-256
`4e6f262535e1f8a7eb226e2536542bc9d291c8f6549c425a936eedc79c98c95c`.

All five component definitions and the conjunction were separately printed
with universe annotations in that environment (check
`13323b0b-b557-4aea-8405-aa840490f4d6`) and read. The printed expressions retain the
arbitrary ring, the actual small filtered index, the integer grading, the
specified `colimit.post` map, and the action isomorphism with that underlying
map. The naturality component has no filteredness premise. There are no
project axioms, placeholder theorem proofs, or pending project imports.
These checks establish well-formed statements; they do not prove their truth
or complete the Harris geometric, smooth-equivariant or Shimura application.
