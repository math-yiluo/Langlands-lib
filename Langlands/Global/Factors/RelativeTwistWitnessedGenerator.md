# Existence of a relative witnessed Hecke twist

`WitnessedGenerator.exists_heckeTwist` derives the existence of a complete
relative witnessed generator from the actual determinant-multiple existence,
presented association and local transfer reciprocity statements, together with
a supplied globally unitary Hecke character having the prescribed local
component. The field, Weil-carrier and presentation-factor universes remain
independent.

The proof first obtains an actual cuspidal realization and spectral
presentation from `CuspidalDeterminantMultipleStatement`. It applies
`PresentedDeterminantMultipleAssociationStatement` to the original weak
association and the actual determinant-multiple relation. At the place retained
by the original generator, its place-above certificate supplies the
lies-over instance. `LocalTransferReciprocityStatement` then applies to the
original characterized local map. These witnesses fill every input of
`WitnessedGenerator.heckeTwist`. Its two local lattice fields are definitionally
the required Weil and automorphic character twists, so both final equalities
are reflexive.

`WitnessedGenerator.exists_unitaryCharacterTwist` obtains the supplied Hecke
character from a unitary extension premise at this number field and finite
place. Its premise is precisely the instance of
`UnitaryLocalCharacterExtensionStatement` at that field and place, written out
using the natural completion topology. The target's `QuasiCharacter` instead
uses the canonical topology of the packaged p-adic field. The proof builds the
same monoid homomorphism with continuity in the natural topology by rewriting
`CompletionPadic.completion_topology_eq` in the induced topology on units.
This preserves its values and the norm-one proof. The extension premise then
provides a globally unitary Hecke character and equality of continuous local
homomorphisms. Pointwise evaluation gives the restriction identity consumed by
`exists_heckeTwist`.

`WitnessedGenerator.unitaryCharacterTwist` chooses a complete generator from
that proved existential. Its two simplification lemmas recover exactly the
Weil and automorphic lattice twist identities from the choice specification.
All the prerequisite proof inputs remain explicit arguments of this
definition.

This is an internal composition of the explicit constructions and proposition
interfaces in the imported Library. It proves no new existence statement
about global Hecke characters, cuspidal determinant multiples, their
association or local reciprocity: proofs of those statements remain explicit
inputs of this intermediate theorem. In particular this helper does not prove
`RelativeIsometryOperationStatement`; its use in the final proof requires
discharging all such inputs with proved results.
