# Inversion of the intrinsic relative-Weyl indexing and normalizer sections

This is an internal adapter derived from the published
`RelativeWeylIndexing` and `RelativeWeyl` constructions. It supplies the
elementary inversion and finite-sum operations needed when comparing the
two double-coset conventions. It proves no rational-point orbit enumeration,
geometric filtration or representation comparison.

For any Coxeter system `cs` on a group `W`, inversion sends the literal set
`doubleCoset cs I J w = W_I w W_J` to
`doubleCoset cs J I w⁻¹`. The proof writes an element as `a * w * b`
and takes its inverse, using subgroup closure under inversion.
`inv_mem_doubleCoset_iff` also proves the converse by inverting twice.

The existing `isMinimal_inv` proves that inversion preserves minimum length
with the two subsets exchanged. `isMinimal_inv_iff` applies that theorem
in both directions. With `[Fintype W]`, `inv_mem_minimalReps_iff` then
unfolds the published membership characterization of `minimalReps`.
`minimalRepsInvEquiv cs I J` is the resulting equivalence between the
actual subtypes of `minimalReps cs I J` and `minimalReps cs J I`.
Both maps take the inverse of the underlying element. Their inverse laws
use `inv_inv` and subtype extensionality.

`sum_minimalRepsInvEquiv` reindexes a sum of values in any additive
commutative monoid along this equivalence. Its summand is a function of the
whole minimal-representative subtype, so it supports constructions whose
definitions use the membership witness, as in `GeometricK0ExpansionStatement`.
`sum_minimalReps_inv` gives the corresponding finite-set sum identity for
a function on `W`. The proofs use Mathlib's `Fintype.sum_equiv` and
`Finset.sum_equiv`, respectively. Integer-linear maps between exact
Grothendieck groups are an allowed additive target; no Grothendieck-group
relations or representation identities are assumed.

For any subgroup `T` of any group `G`, `RelativeWeyl.inverseSection`
sends a function `lift : Weyl T → normalizer T` to
`w ↦ (lift w⁻¹)⁻¹`. Here `Weyl T` is the published actual quotient
of the normalizer by the full centralizer. `inverseSection_mk` proves
that if the original function is a section of this quotient, the new
function is also a section. The proof uses the quotient homomorphism's
inverse law and the original section law at `w⁻¹`.
`inverseSection_involutive` proves that applying this construction twice
returns the original function. No multiplicativity of a section, special
choice of representatives, finiteness or Coxeter structure is required
for these section results.

The simple-index, group and additive-target universes are independent.
No assumption that the simple-index type is nonempty, finite, or has
decidable equality is imposed. Only the finite representative-set and sum
constructions require a finite group.

The proof-body dependencies are subgroup multiplication/inversion,
`RelativeWeylIndexing.isMinimal_inv`, its finite membership theorem,
subtype and group inverse laws, the two Mathlib sum-reindexing theorems,
and the actual quotient inverse law. The imported modules add the Coxeter
and quotient constructions; no proof body or import uses a geometric
lemma, adjointness, cuspidal support, character independence, or Langlands
classification.

This adapter does not identify actual rational-point double cosets with
minimal Weyl representatives, prove their ordering or uniqueness, compare
normalizer lifts on representations, or identify normalized graded pieces.
Both Haar corrections, the distinct radicals and their modulus balance,
smooth realization and any compact/full-induction comparison remain
separate obligations of the actual geometric-lemma proof.
