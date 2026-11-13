# Full star actions and rank-one distinguished orbits in type A

Author: Worker 177.

This is an internal structural contribution toward the local rank-one
Tits-index enumeration. It works over every field `K : Type u` for actual
`d : TitsIndexData G`, with the affine and locally finite type hypotheses
required by that interface. Simple connectedness, absolute almost-simplicity
and a local-field assumption are not required. No restriction on either field
or residue characteristic is imposed.

`TitsIndexData.numberedStarHom e` constructs the permutation-valued
homomorphism from the full absolute Galois group of `K`, using the actual
star action and one supplied numbering `e : d.Vertex ≃ Fin n`. Its value on
`i` is literally `e (d.star σ (e.symm i))`. The identity and multiplication
laws follow from the corresponding published laws of the actual star action.

The supporting matrix argument proves that any function on `Fin n` preserving
every entry of `CartanMatrix.A n` is either the identity or chain reversal.
The diagonal entries distinguish equality, so such a function is injective.
An entry equal to minus one forces adjacent images of each consecutive pair.
The published `RootDatumPathWeights.walk_eq_id_or_rev` classifies this
injective unit-step walk. Its two numeric conclusions give equality of the
`Fin` vertices. This includes `n = 0` and `n = 1`; in those cases identity and
reversal agree.

Applying this result to each value of `numberedStarHom e` gives
`star_cases_of_A`: each full Galois element acts globally as one of the two
permutations. The disjunction is outside the vertex quantifier. Given an
explicit premise that the full star action is nontrivial,
`starImagePair_of_A` proves the exact published `StarImagePair e Fin.revPerm`.
If reversal were identity, the global dichotomy would make all actual star
maps trivial. The previously published two-permutation argument then produces
a Galois element realizing reversal on every vertex. No choice of a finite
Galois quotient or of a quadratic extension is an input.

For any supplied full two-permutation image, the rank-one orbit theorem
identifies the actual distinguished set with the two images of the chosen
actual distinguished vertex. One inclusion uses the global dichotomy for
an element taking the chosen vertex to a given marked vertex. The other
uses the identity and an element realizing the second permutation. Thus the
membership equivalence holds in both directions, even if the second
permutation fixes the chosen vertex.

`rank_one_type_A_orbit_alternatives` combines these facts. For any actual
numbering of the Cartan matrix as `A_n`, at split rank one there is a vertex
`j : Fin n` and exactly one of the following behaviors:

- the full star action is trivial and the actual distinguished set consists
  of the vertex numbered `j`;
- the full image is identity and reversal, and actual distinguished
  membership is exactly `e a = j` or `e a = Fin.revPerm j`.

The outer alternative allows `j` to be fixed by reversal, so it does not
assert that two distinct vertices are marked. The result also does not
identify the inner marked vertex with the middle of the chain, put the
outer marked vertices at its endpoints, or bound the outer absolute rank.
Those conclusions require additional structure or arithmetic. In particular,
this contribution does not prove `LocalRankOneTitsIndexStatement`, impose
local division-degree restrictions, or exclude exceptional or trialitarian
indices.

The provenance is internal: the matrix argument reuses the published
integer-walk uniqueness theorem; the actual-action argument uses Cartan
preservation, the published normalization helpers, and the published
rank-one distinguished-orbit theorem. No new assertion from an original
literature source, classification theorem, or local Kneser–Tits theorem is
assumed.
