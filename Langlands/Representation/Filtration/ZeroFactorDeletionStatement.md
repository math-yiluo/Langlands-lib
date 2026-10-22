# Deletion of selected zero factors from an actual representation filtration

Author: Worker 177. Provenance: internal algebra.

The proposition definition
`Langlands.ObjectRepFiltration.ZeroFactorDeletionTheorem` states an existence
claim about the Library's actual representation filtrations. This pair does
not prove that claim.

For every commutative ring `R`, monoid `G`, representation `A : Rep R G`,
natural number `m`, filtration `s : ObjectRepFiltration A m`, and predicate
`P : Fin m → Prop`, the only additional hypothesis is that
`s.gradedRepresentation i` has a subsingleton carrier whenever `¬ P i`.
Since each carrier is an additive group, this means the omitted quotient
is zero.

The conclusion supplies a natural number `r`, an equivalence
`e : Fin r ≃ {i : Fin m // P i}`, and a filtration
`t : ObjectRepFiltration A r` of the same ambient representation. For every
`j : Fin r`, it requires an actual equivariant linear equivalence
`Representation.Equiv` from `(t.gradedRepresentation j).ρ` to
`(s.gradedRepresentation (e j).val).ρ`. Each such equivalence is asserted
to exist using `Nonempty`; it is not replaced by equality of constituent
labels or classes.

The equivalence of index types matches every retained occurrence exactly
once. A selected factor may itself be zero, and must still occur. Distinct
selected indices remain distinct even if their representations are
equivalent. The statement does not prescribe the order of this matching.
The predicate `P` has no decidability hypothesis.

The quantifiers include `m = 0`, an empty retained set, and representations
with zero carrier. If the retained set is empty, the index equivalence
forces `r = 0`; the resulting filtration still has both required endpoints.
For a zero ambient representation, all selected indices are still retained
as zero quotients. No hypothesis requires a field, finite dimension, finite
length, irreducibility, nonzero selected factors, splitting, or an already
compressed filtration. The coefficient, acting monoid, and representation
carrier universes `uR`, `uG`, and `uV` are independent.

## Definitions reused and provenance

The sole import is
`Langlands.Representation.Filtration.ObjectDefinitions`. Its
`ObjectRepFiltration` reuses the actual monotone zero-to-full submodule chains
from `Langlands.Representation.Filtration.Definitions`, and
`gradedRepresentation` is their actual successive quotient representation.
No definition of a filtration, quotient, or representation equivalence is
changed or replaced.

This is an internal algebraic statement, motivated by the consumer task's
need to remove known zero pieces from a representation filtration while
keeping every prescribed remaining occurrence. It is not attributed to an
external theorem or assumed as a geometric lemma. Its algebraic rationale
is that a zero successive quotient makes the two adjacent submodules equal;
such a step can be deleted without changing the ambient endpoints or the
other successive quotients. Repeating this only for unselected indices
motivates the stated conclusion, including zero factors at selected indices.
This rationale is not a Lean proof. A proof of this exact proposition is a
separate obligation after statement publication.
