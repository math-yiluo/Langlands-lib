# Unitary-component untwists of actual opposite Jacquet subrepresentations

Worker 148. This internal construction combines the published irreducible
Jacquet-subrepresentation selector and positive unramified realization for an
individual exponent of the actual opposite standard Jacquet family. The original
standard Levi, its split component, and its canonical point topology are retained.
The field and representation carrier universes are independent.

`leviJacquetObject` is the actual normalized Jacquet module of the opposite
parabolic, transported to the original standard Levi points. The standard and
opposite Levi point topologies are the same canonical topology.
`unitaryComponentCharacter` is the original exponent divided by the restriction
of its positive unramified realizing character. The published modulus comparison
proves that its value has norm one at every original component point.

`UnitaryUntwist` records an actual irreducible smooth source representation, an
injective smooth map into this Jacquet module, and its inverse twist by the
realizing character. It also retains irreducibility and admissibility of the
untwist, its scalar action by `unitaryComponentCharacter`, and an actual smooth
isomorphism recovering the source after twisting back. The equality of the
inverse-twisted smooth object is part of the record. Unitarity here concerns the split
component character; no invariant positive definite form on the representation
is asserted.

`irreducibleUnitaryUntwist` constructs these data from admissibility of the
ambient representation and an explicit finite-length hypothesis on the chosen
opposite Levi Jacquet module. The published exact exponent comparison
identifies the supplied exponent with a generalized character on the actual
Levi-point module. After transport of actual Jacquet admissibility, the accepted
generic scalar-character existence theorem gives the irreducible source,
injective inclusion and scalar exponent. Private helpers separate these
certificates, and classical choice selects the source from this existence proof.
Admissibility through the injective intertwiner proves source admissibility.
The realizing character and its inverse have open kernels. Twisting therefore
gives a smooth irreducible admissible object on the same carrier. Direct scalar
multiplication gives the quotient component character, and cancellation of
inverse twists gives the recovery isomorphism. A private nonemptiness proof
constructs the full result record, and classical choice supplies the entry
definition; the construction asserts existence rather than canonical selection.

The provenance is internal, through the published selection, realization,
admissibility and twist APIs. This contribution does not prove preservation of
Jacquet finite length, the positive-part cone decomposition, temperedness of the
untwist, an induction quotient, or the Langlands classification.
