# Cyclic prime-step towers for finite solvable Galois extensions

Worker 109 authored this proof and its explanation. No other worker draft was
reused. The theorem `Langlands.FieldTheory.solvableGaloisPrimeTower.{u,v}` has
exactly the published proposition
`Langlands.FieldTheory.SolvableGaloisPrimeTower.{u,v}` as its type, with no
additional outer hypotheses. It imports the unchanged statement module
`Langlands.FieldTheory.SolvableGaloisTowerStatement`.

## Scope and actual scalar maps

For fields `K : Type u` and `L : Type v`, with independent universes, the
hypotheses are an algebra structure, finite dimensionality, Galoisness of
`L/K`, and solvability of `Gal(L/K)`. The proof constructs a natural number
`n` and actual intermediate fields `T : Fin (n + 1) → IntermediateField K L`,
from bottom to top. Each consecutive extension is finite dimensional, Galois,
and cyclic of prime degree. All four assertions use the same algebra
`(IntermediateField.inclusion h).toAlgebra`, for the supplied inclusion `h`.
There are no local-field or characteristic assumptions. The construction does
not require every intermediate field to be Galois over `K`.

The private proposition-valued definition `PrimeStep A B` packages precisely
that one inclusion and those four assertions. The final theorem unfolds this
package definitionally; it neither supplies a different scalar map nor weakens
the target.

## Implemented proof

The private lemma `exists_prime_quotient` starts with a finite nontrivial
solvable group `G`. Its commutator is proper, so its abelianization is
nontrivial. The finite subgroup lattice of the abelianization has a coatom
`M`. The quotient by `M` is a simple abelian group, hence cyclic and of prime
order. Compose abelianization with this quotient map and let `H` be its
kernel. The first isomorphism theorem identifies the actual quotient `G/H`
with that simple abelian quotient. This transports cyclicity and prime
cardinality to `G/H` and supplies normality of `H`.

The private lemma `exists_prime_step` applies this result to `Gal(L/A)` for a
proper intermediate field `A`. Galois correspondence shows that the fixing
subgroup of `A` is nontrivial: otherwise its fixed field would be top. The
canonical equivalence with `Gal(L/A)` transfers nontriviality and solvability
from this subgroup of `Gal(L/K)`. Finiteness and Galoisness of `L/A` are
inherited from `L/K`; no normality of `A/K` is needed.

Choose the normal subgroup `H` supplied by the group lemma and form its actual
fixed field `F`, an intermediate field of `L/A`. Normality makes `F/A` Galois.
Mathlib's `IsGalois.normalAutEquivQuotient H` identifies its relative
automorphism group with `Gal(L/A)/H`. Thus `F/A` is cyclic, and the Galois
automorphism-cardinality formula makes its degree prime. Restricting scalars
to `K` gives `B := F.restrictScalars K`, with the same underlying field in
`L`. Its inclusion `A ≤ B` comes from `F.algebraMap_mem`. If `B ≤ A`, then
`F` is bottom as an intermediate field over `A`, so its degree is one,
contradicting primality. Therefore `A < B`. Under the literal inclusion
algebra, all four step assertions are definitionally the assertions just
proved for `F/A`.

The private lemma `exists_tower_from` constructs a tower from any intermediate
field `A` to top, by well-founded induction on `Module.finrank A L`. When
`A = top`, choose `n = 0` and the constant one-entry tower; `Fin.elim0`
discharges its empty family of steps. Otherwise the preceding lemma gives
`A < B` and a prime step. The remaining degree strictly decreases by
`IntermediateField.finrank_lt_of_gt`, so induction supplies a tower from `B`
to top. Prepending `A` with `Fin.cons` preserves the final endpoint and gives
the required new first step. `Fin.cases` divides step verification into this
first step and the already constructed steps. Finally, specialize this lemma
to bottom to prove the exact published target. This also covers a trivial
extension, where bottom equals top, by the length-zero case.

## Dependencies and provenance

This is an internal derivation from pinned Mathlib finite-group and finite
Galois-correspondence theorems. The implementation uses successive prime
quotients and degree induction; it does not construct a composition series.
Its direct imports, beyond the target module, are:

- `Mathlib.GroupTheory.QuotientGroup.Simple`, for simple abelian quotients;
- `Mathlib.GroupTheory.Abelianization.Finite`, for finite abelianization;
- `Mathlib.GroupTheory.SpecificGroups.Cyclic`, for cyclicity of simple abelian groups;
- `Mathlib.Data.Fin.Tuple.Basic`, for prepending the finite tower;
- `Mathlib.Order.Atoms.Finite`, for a coatom in the finite subgroup lattice.

The target imports `Mathlib.FieldTheory.Galois.Basic` and
`Mathlib.GroupTheory.Solvable`. Key inherited results include
`Group.IsSolvable.commutator_lt_top_of_nontrivial`,
`QuotientGroup.quotientKerEquivOfSurjective`,
`IsGalois.fixedField_fixingSubgroup`, `IntermediateField.fixingSubgroupEquiv`,
`IsGalois.normalAutEquivQuotient`, `IsGalois.card_aut_eq_finrank`, and
`IntermediateField.finrank_lt_of_gt`. Existing Library and Mathlib files,
including the target's full import closure, are unchanged.

Source motivation is Jean-Pierre Serre, *Local Fields*, Greenberg English
translation, GTM 67 (1979), Chapter V, §4, Proposition 7 and its proof,
printed page 90/PDF page 97. The registered original is
`serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Worker 109 reread that page and visually checked the dévissage paragraph;
no project Serre errata entry was found. Serre uses solvability to reduce
the totally ramified Galois norm argument to cyclic prime degree. The generic
tower here is an internally derived ingredient for that reduction, rather
than a literal transcription of Serre's statement or proof. This module
proves no norm-surjectivity, local solvability, descent, or cohomology theorem.
