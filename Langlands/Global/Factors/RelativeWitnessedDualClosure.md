# Dual closure of actual relative witnessed generators

This internal interface expresses the dual closure needed for the relative
generated-isometry operation proof. It is derived from the actual witnessed
objects and their two existing unitary lattice operations. Its definition was
first used in the relative-isometry assembly draft; this module gives it a
separate home and supplies its explicit-prerequisite deductions.

`Langlands.Global.PoleComparison.RelativeWitnessedDualClosure` means that every
actual relative witnessed generator at the specified finite place has another
actual witnessed generator whose Weil lattice element is its unitary dual and
whose automorphic lattice element is its unitary contragredient. It keeps the
field, Weil-carrier and presentation-factor universes independent, and makes no
choice of an isometry.

The theorem `relativeWitnessedDualClosure_of_unitaryCentralCharacters` assumes
that each original generator's actual cuspidal realization has a unitary central
character. Its four other inputs are proofs of the published statements on
actual cuspidal dual existence, dual spectral-presentation existence, local
smooth-dual compatibility and presented contragredient association, using the
original presentation-factor universe for the output as well as the input.
It applies `WitnessedGenerator.exists_dual` to each generator and retains exactly
the two required lattice identities. The stronger identities about the global
dual, local map and output central character remain available from that
construction but are not part of this closure predicate.

The theorem `relativeWitnessedDualClosure_of_centralComparison` additionally
assumes an arithmetic class family and a proof of the published actual
`AssociatedCentralCharacterStatement`. Each generator records its original
unitary Weil representation and actual weak association. The proved theorem
`hasUnitaryCentralCharacter_of_associatedCentralCharacter` applies to those data:
the central comparison supplies the actual central character and determinant
identity, and arithmetic transfer surjectivity detects global unitarity from
the unitary determinant. The resulting central-character witnesses discharge
the corresponding input of the first closure deduction.

This module introduces no new global comparison or contragredient existence
claim. Both deductions retain all listed prerequisite proofs as arguments. In
particular it does not prove the unconditional `RelativeIsometryOperationStatement`;
using this closure interface there still requires actual proofs of the central
comparison and all four contragredient prerequisites. The source-free internal
provenance is composition of the inspected existing definitions and proved
constructions, rather than a new attribution to external literature.
