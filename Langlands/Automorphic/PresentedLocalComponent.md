# Local components attached to nonzero tensor presentations

This internal construction attaches actual local slices and their smooth
isomorphism classes to a supplied tensor presentation of a nonzero invariant
subspace of automorphic forms. The required nonzero complementary vectors are
proved to exist from the presentation. They are not additional assumptions.

## Inputs and provenance

The inputs are exactly those of `TensorPresentation.lean`: a number field
`F : Type uF`, arbitrary matrix rank `n : ℕ`, complex vector spaces
`V v : Type uV` at each finite place, representations `ρ v` of the actual
completed-local general linear groups, a finite exceptional set `E`, and
reference vectors `e v` fixed by the integral local subgroup outside `E`.
The carrier universes `uF` and `uV` are independent. The carriers need no
topology, dimension hypothesis, or irreducibility hypothesis.

The supplied `P : FiniteTensorPresentation F n ρ E e he S` contains nonzero
reference vectors outside `E` and a genuine global equivariant linear
equivalence onto the prescribed actual finite invariant form space `S`.
`FiniteRealization.IsNonzero F n S` abbreviates `S ≠ ⊥`. This ordinary
nonzeroness condition is required throughout the construction.

There is no new external-literature assertion. The provenance is internal:
the published genuine local tensor equivalence, faithful slice construction,
smoothness inherited from actual forms, and same-model slice equivalences
are combined with elementary algebraic tensor induction and classical choice.

## Derived nonzeroness and smoothness

`exists_nonzero_localTensor` proves that
`V v ⊗[ℂ] LocalTensorTail F E v e` has a nonzero vector. If every tensor were
zero, surjectivity of `P.localEquiv v` would make every vector of `S` zero,
contradicting `S ≠ ⊥`.

`exists_nonzero_localFactor` and `exists_nonzero_tail` then prove that both
tensor factors have nonzero vectors. Each proof argues by contradiction:
if every vector in the relevant factor were zero, every pure tensor would
be zero, and tensor induction would make every tensor zero. These arguments
also apply at the exceptional places, without imposing a nonzero reference
vector there.

`localFactor_isSmooth` uses a derived nonzero tail and the published faithful
slice into actual automorphic forms. Smoothness follows from the injective
intertwiner into the smooth local right action.

## Embedded components and their classes

`chosenTail` selects a nonzero complementary vector using classical choice.
`chosenTail_nonzero` records its proved property. `localComponent` is the
actual embedded slice `P.slice v (P.chosenTail hS v)`, and
`localComponent_le` places it inside the entire local restriction of `S`.
The chosen embedded subspace is not asserted to be independent of the tail.

`localComponentEquiv` is the published faithful slice equivalence from `ρ v`
to the representation on this embedded local copy. `localComponent_ne_bot`
uses a nonzero local-factor vector, its image under this injective equivalence,
and its actual subtype inclusion to prove that the embedded component is
nonzero.

`localComponentClass` takes the smooth isomorphism class of that slice.
Its representative is an actual subspace of forms in universe `uF`,
even when the input factor carrier lives in the independent universe `uV`.
`localComponentClass_eq_slice` identifies it with the class of the slice
defined by any other nonzero tail. `localComponentClass_eq` compares any two
presentations with the same `V, ρ, E, e, he`, possibly into different nonzero
form spaces `S` and `S'`. Both proofs apply the published same-model slice
class equality, obtained by composing genuine equivariant equivalences.

## Conditions retained on the embedded copy

`localComponent_hasCentralCharacter` and `localComponent_isCuspidal` inherit
the corresponding global conditions by containment in `S`. These predicates
refer to the actual embedded forms: the global idele character identity and
vanishing normalized constant terms, respectively. The cuspidal lemma retains
the existing `[CompactSpace (AdeleQuotient F)]` instance parameter. Neither
predicate is here defined on the local isomorphism class.

`localComponent_exists_integral_fixed` uses the nonzero reference vector at
each `v ∉ E`, transports it through the slice equivalence, and applies the
published slice fixed-vector lemma. It gives a nonzero vector fixed by the
actual integral local subgroup. It claims neither uniqueness of this fixed
vector up to scalar nor finite-dimensionality of the fixed space.

## Scope

Every construction depends on a supplied genuine presentation of a nonzero
actual form space. This module does not construct a tensor factorization for
an arbitrary realization, prove uniqueness across different factor families,
or identify one slice with the entire locally restricted representation.
Irreducibility, admissibility, normalized Satake data, archimedean stability,
and descent of embedded global conditions to abstract local classes remain
separate obligations.
