# Actual comparisons for a supplied point root-sign Coxeter system

This internal derived module retains an arbitrary supplied Coxeter system on
the actual normalizer/full-centralizer quotient of rational points. Its labels
are the literal simple relative characters of a generic cocharacter. The
hypotheses include the point normalizer and centralizer comparisons, a split
torus, and the actual relative-root-system witness. Whole-character pairing and
standard-Levi conclusions also assume connected reductivity and maximality of
the split torus. The supplied system is required to satisfy the literal
`RootLengthComparison`; no actual reflection premise is assumed for it.

`schemeCoxeterSystem` pulls that system back through the representative-preserving
scheme-to-point quotient equivalence without changing the simple-root labels.
The generator-preserving length lemma identifies its length with the point
length. The character-action comparison transports the root-sign length law.
The scheme generator-uniqueness theorem then identifies every supplied generator
as the actual reflection in its label.

`simpleReflectionPairingInvariance_of_rootLength` applies the whole-character
pairing theorem for an actual root-span reflection and transports its action
back to the point quotient. It proves invariance for every character and every
cocharacter orthogonal to the labelled simple root, without choosing a
complement to the root span.

`positiveSimpleReflectionComparison_of_rootLength` applies the scheme positive
simple-reflection conjugacy theorem and uses injectivity of the quotient
equivalence to transport the group equality. Its conclusion is literal equality
of the image character with the target simple root under the required positivity
premise, including for nonreduced relative root systems.

`actualLeviWeylIdentification_of_rootLength` combines the resulting pairing law
with `actualLeviWeylIdentification_of_simplePairing`. The conclusion uses the
original supplied system and the actual standard-Levi Weyl inclusion, for every
finite subset of the same simple-root type.

The provenance is the internal composition of the quotient transport,
root-sign generator uniqueness, root-span pairing, positive conjugacy, and
pairing-stabilizer standard-Levi identification modules. No representation
expansion or final Aubert compatibility equation is asserted here.
