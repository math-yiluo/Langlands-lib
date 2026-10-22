# Closure embeddings and continuous Galois representation restriction

Author: Worker 41. This module constructs restriction along an explicitly
specified embedding of algebraic closures and proves independence, up to an
actual intertwining equivalence, of that embedding. It imports the published
`Langlands.Galois.CompatibleFamily` and, through it, the coefficient
representation definitions.

## Construction and hypotheses

Let K and E be fields with a specified K-algebra structure on E. For two
K-algebra embeddings iota and kappa from the algebraic closure of K to the
algebraic closure of E, `restrictionAlongClosure` constructs continuous
homomorphisms r_iota and r_kappa from the absolute Galois group of E to that
of K. They satisfy iota(r_iota(g)(x)) = g(iota(x)). The construction installs
iota's algebra structure on the closures and uses Mathlib's
`Field.absoluteGaloisGroup.mapOfAlgebra`, including its continuity proof
for the Krull topologies.

`closureChange iota kappa` is the unique c in the absolute Galois group of K
such that iota(c(x)) = kappa(x). It is constructed with
`AlgHom.restrictNormal'`; the normality of the algebraic closure supplies
an automorphism, rather than merely an endomorphism. The specification
follows from `restrictNormal_commutes`. Injectivity of iota proves
uniqueness and, after applying both sides to x, the relation

    c * r_kappa(g) = r_iota(g) * c.

No finite extension, separability, characteristic-zero or number-field
hypothesis occurs in this general construction. Mathlib uses full algebraic
closures here. The base, extension, coefficient field and representation
carrier have independent universe parameters.

For a coefficient field L with its specified topology and an actual continuous
finite-dimensional L-representation A of the absolute Galois group of K,
`pullbackAlongClosure` composes its action with r_iota. Its continuity is the
composition of the two continuous maps, with the same module topology on
endomorphisms as the published `Objects` definition. The carrier is unchanged.
`pullbackAlongClosureEquiv iota kappa A` is an actual linear intertwining
equivalence from the kappa restriction to the iota restriction. Its forward
map is A(c), its inverse is A(c inverse), and the intertwining identity is
the image of the displayed group identity under A.

The published conjugation-invariance lemmas then give equality of both
characteristic and Euler polynomials at every element of the local group.
Here Euler polynomial means det(1 - A(g) T), as in
`CoefficientRepresentation`; it is the reversal of the characteristic
polynomial. Conjugation preserves the identity endomorphism, so triviality
of the action at each group element is also equivalent for the two
restrictions. In particular, triviality on any specified subgroup agrees.

## Explicit field maps and finite places

For a field homomorphism f : K -> E, `ClosureEmbedding f` is the type of
K-algebra embeddings of the closures using exactly the algebra structure
`f.toAlgebra`. `chosenClosureEmbedding f` constructs Mathlib's selected
`IsAlgClosed.lift` for that structure. This explicit field-map interface
avoids dependence on an implicit choice of algebra instance.

`restrictionAlongClosure_chosen_eq` and `pullbackAlongClosure_chosen_eq`
identify the chosen-lift constructions with the published restriction map
and `pullback f`, respectively, by definitional equality. Their statements
explicitly install `f.toAlgebra`. The Euler polynomial comparison for any
embedding follows by combining this identification with the general
intertwiner. This does not assert equality of the different restriction
homomorphisms themselves.

When K is a number field and v is an actual nonzero prime of its ring of
integers, the finite-place interface takes
`ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)`.
`atFinitePlaceAlongClosure` restricts to the absolute Galois group of the
actual completion. Its chosen-lift version equals the published
`atFinitePlace v`. `atFinitePlaceAlongClosureEquiv` constructs an equivalence
from the specified-embedding restriction to that published restriction.
The Euler polynomials agree at every element of the same local group.
The finite-place signatures do not require consumers to enable a hidden
local algebra instance.

`isUnramifiedAt_iff_alongClosure` identifies the published unramifiedness
condition with triviality of the specified-embedding action on the same
actual inertia subgroup, the kernel of the published residue action.
`hasEulerPolynomialAt_iff_alongClosure` then identifies the published
matching predicate with the conjunction of that inertia condition and the
existence of an actual geometric Frobenius lift having the given Euler
polynomial. The proof rewrites unramifiedness and the polynomial comparison.
The geometric convention is unchanged: the inverse of the lift acts on the
residue field by the absolute-norm power. Existence is retained as an
existential clause, not replaced by a possibly vacuous universal assertion.

## Declaration map

All declarations below lie in `Langlands.GaloisRepresentation`.

| Declarations | Content |
| --- | --- |
| `restrictionAlongClosure`, `restrictionAlongClosure_commutes` | Continuous restriction and its commuting square. |
| `closureChange`, `closureChange_spec`, `closureChange_unique`, `closureChange_intertwines` | Constructed change of closure embedding, uniqueness and conjugacy relation. |
| `pullbackAlongClosure`, `pullbackAlongClosureEquiv` | Actual continuous representation restriction and linear intertwiner. |
| `characteristicPolynomial_pullbackAlongClosure_eq`, `eulerPolynomial_pullbackAlongClosure_eq`, `pullbackAlongClosure_action_eq_one_iff` | Polynomial invariance and equivalent trivial action. |
| `restrictionAlongClosure_chosen_eq`, `pullbackAlongClosure_chosen_eq`, `eulerPolynomial_pullbackAlongClosure_eq_pullback` | Comparison with the existing field-map restriction. |
| `ClosureEmbedding`, `chosenClosureEmbedding` | Explicit field-map interface and selected embedding. |
| `atFinitePlaceAlongClosure`, `atFinitePlaceAlongClosure_chosen_eq`, `atFinitePlaceAlongClosureEquiv`, `eulerPolynomial_atFinitePlaceAlongClosure_eq` | Restriction and comparison at an actual completion. |
| `isUnramifiedAt_iff_alongClosure`, `hasEulerPolynomialAt_iff_alongClosure` | Independence of unramifiedness and existential Euler matching. |

## Provenance and boundaries

This is a derived construction. Its source motivation is Jean-Pierre Serre,
*Local Fields*, English translation by Marvin Jay Greenberg, GTM 67,
Springer, 1979, Chapter X, Section 4, printed pp.155-156 (PDF pp.161-162).
The original defines compatible restriction homomorphisms using a field
embedding and explains that two choices differ by a Galois automorphism.
Serre's Proposition 5 concerns the induced cohomology maps. This module
formalizes the restriction and change-of-embedding construction and derives
representation consequences; it does not claim to prove Proposition 5.
The source uses Galois extensions and separable closures; the general Lean
construction instead uses normality of full algebraic closures and requires
no separability premise. The implemented proof route is described above.

Registered source: `serre-1979-local-fields`, file
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The cited pages were read in the original and this fingerprint was recomputed.
Mathlib is pinned at `5ed2965256430c3649e86755f9576b54eca72435` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.

This contribution proves independence of the global-to-local closure
embedding while retaining the same algebraic closure of the completion and
the same residue-action construction. It supplies no canonical restriction
homomorphism, comparison between different residue-closure models, ramified
Euler factor, automorphic existence theorem, cohomological realization,
Hodge-Tate assertion or multiplicity-removal statement. Independence from
the Frobenius element itself is the separate result already present in
`CompatibleFamily`; lift existence is supplied separately by `FrobeniusLift`.
The full Kottwitz, Clozel, Taylor and Harris statement task remains open.
