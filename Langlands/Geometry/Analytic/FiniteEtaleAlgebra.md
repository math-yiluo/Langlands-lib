# Algebraically finite étale bounded affinoid maps

Author: Worker 36.

This module constructs a category of actual bounded maps between presented
strict affinoid algebras whose underlying ring maps are finite and étale. It is
local algebraic infrastructure for subsequent analytic finite étale
constructions.

For a `BoundedAlgHom K A B`, the proposition
`BoundedAlgHom.AlgebraicallyFiniteEtale` is the conjunction of Mathlib's
`RingHom.Finite` and `RingHom.Etale` for its underlying ring homomorphism.
Finiteness means finite generation of the target as a module over the source,
using the scalar action supplied by this very ring map. The étale condition is
Mathlib's algebraic étaleness, with finite presentation included. The
characterization lemma expresses the conjunction as module finiteness,
flatness, formal unramifiedness and finite presentation. These conditions
concern the given map, rather than an unrelated algebra structure on its target.
The predicate itself also makes sense for bounded algebra maps between normed
commutative algebras in independent universes.

The actual bounded identity satisfies this condition. Composing two bounded
maps uses the existing `BoundedAlgHom.comp`, which multiplies their positive
norm bounds; the two algebraic properties are retained by Mathlib's composition
theorems. A bijective bounded algebra map also satisfies the algebraic
condition. This last lemma asserts no boundedness of its inverse.

Over a complete ultrametric normed field, `algebraicallyFiniteEtaleProperty`
applies this predicate to the actual category from `Affinoid`. Its
`IsMultiplicative` instance proves identity and composition closure.
`AlgebraicallyFiniteEtaleAffinoidAlgebra` is Mathlib's wide subcategory:
every object is a chosen finite Tate algebra quotient by a closed ideal, and
each morphism consists of an existing bounded algebra map and a proof of the
displayed algebraic condition. Category laws are inherited from the actual
bounded-map category. The inclusion forgets the condition and is faithful.
Objects and maps are therefore constructed from the quotient algebras; no
arbitrary analytic category is supplied as an input.
The algebraic category and inclusion also exist without completeness of the
coefficient field. Completeness is required explicitly by the spectrum functor,
which factors through the existing category of Banach rings.

`AlgebraicallyFiniteEtaleAffinoidSpace` is the opposite category. Its spectrum
functor is the composite of the opposite inclusion with
`strictAffinoidSpectrumFunctor`. An arrow from the spectrum of `B` to that of
`A` acts by pulling a multiplicative seminorm back along its underlying bounded
map `A → B`. The final evaluation lemma verifies this formula definitionally.
Continuity and functor laws come from the existing Banach spectrum functor.
The zero quotient and empty spectra are allowed.

The qualifier “algebraically” records the precise construction boundary.
There is no theorem here identifying module finiteness with an admissible
finite Banach-module presentation, comparing the norm topology with a finite
module quotient topology, or proving stability under restriction to every
analytic affinoid domain. No atlas, structural sheaf, analytic étale or
quasi-étale site, analytic base change, or covering condition is constructed in
this module. In particular, the category is not asserted to be the full
category of analytic finite étale morphisms from the original source.

Original-source correspondence:

- Berkovich, *Non-archimedean analytic spaces*, Trieste lectures (2009),
  Definition 3.3.1(i), printed/PDF p. 17, defines finite affinoid morphisms using
  the canonical bounded map and a finite Banach algebra. Definition 3.3.9(i),
  p. 19, requires algebraic finite étaleness on affinoid domains; part (ii)
  defines analytic étaleness locally on open neighborhoods. These motivate the
  present algebraic predicate. The all-domain requirement and the Banach
  finiteness comparison are explicitly left open. The underlying actual
  affinoid quotients and bounded-map category come from Definitions 2.1.1,
  2.1.2 and 2.1.11, pp. 7–8, as implemented in `Affinoid`. The retained
  registered original is `berkovich-2009-trieste-analytic-spaces`, SHA256
  `8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`,
  available at
  https://www.wisdom.weizmann.ac.il/~vova/Trieste_2009.pdf.

This is a derived construction, not a theorem quoted verbatim from the
lectures. Its intrinsic lemmas apply the pinned Mathlib definitions and results
in `RingTheory.RingHom.Finite` and `RingTheory.RingHom.Etale`; the wide category
and faithful inclusion use `CategoryTheory.Widesubcategory`. The implemented
proofs use bijectivity for the identity case, transitivity of module finiteness
and algebraic étaleness for composition, the algebraic flatness
characterization for the predicate equivalence, and definitional reduction for
the spectrum evaluation formula.
