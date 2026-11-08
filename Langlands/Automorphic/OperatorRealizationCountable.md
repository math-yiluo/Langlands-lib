# Countable dimension of irreducible operator realizations

Module: `Langlands.Automorphic.OperatorRealizationCountable`. Author: Worker 1827.

## Results

* `finiteAdelicGL_secondCountableTopology`: `FiniteAdelicGL F n` is second countable. The
  finite adeles are second countable by the Library's `finiteAdeles_secondCountableTopology`.
  Hence so are the matrices and their opposite. The unit topology is induced by
  `Units.embedProduct` (`Units.isEmbedding_embedProduct`).
* `finiteAdelicGL_countable_quotient`: every open subgroup has countably many left cosets.
  Every coset is open, so it meets a fixed countable dense set. The argument is the same
  as the Library's `NormalHecke.countable_quotient_of_isOpen`, reproved here to avoid a
  heavy import.
* `OperatorRealization.countable_finiteOrbit`: the finite adelic orbit of a realized vector
  is countable, because a vector fixed by an open `U` has an orbit indexed by `G ⧸ U`.
* `OperatorRealization.representation_mem_of_stable`: a subspace stable under the finite
  translations, the compact translations and the genuine enveloping action is stable under
  every element of the generated `automorphicOperatorAlgebra` (`Algebra.adjoin_induction`).
* `OperatorRealization.rank_le_aleph0`: if `S.IsIrreducible` (irreducibility for the whole
  operator algebra), then `Module.rank ℂ S.Space ≤ ℵ₀`.

## Proof of `rank_le_aleph0`

Pick `x₀ ≠ 0`. Starting from `{x₀}`, one step adds, for each vector `v` already present,
three things: its countable finite adelic orbit, a finite spanning set of its compact orbit
span (finite dimensional by the Library's `compactRepresentation_isFiniteVector`), and,
for each degree `d`, a finite spanning set of the image of the degree-`d` piece of the
enveloping algebra applied to `v`. These pieces are finite dimensional and exhaust the
algebra (`envelopingDegreeFiltration_finite`, `exists_mem_envelopingDegreeFiltration`).
Iterating gives a countable set. Its span `P` is stable under the three families, hence a
subrepresentation for the whole operator algebra. It contains `x₀`, so irreducibility forces
`P = ⊤`. Then `rank_span_le` bounds the rank by `ℵ₀`.

## Provenance

Internal and derived from Library results. It uses no admissibility, central character
or cuspidality hypothesis.
