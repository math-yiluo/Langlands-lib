# Powered Weyl points and transport along simple words

This internal supporting construction transports actual root maps and their
Weyl products along the root bijection of a root-datum isogeny. Its inputs are
the affine powered maps and the published compatibility of root-datum
isogenies with reflections. It imposes no locality, nontriviality, or
reducedness assumption on the coefficient ring.

The inverse root bijection carries a reflection word in the source to the
corresponding word in the target. Root factors remain constant along these
words. Given bases for which the simple roots correspond, `transportSimpleWord`
therefore constructs an actual target simple word from any source simple
word. The assertion about the bases is an explicit input.

The powered root maps agree with the target maps at one. Additivity shows
that they agree at minus one as well, including in characteristic two.
Consequently their three-factor Weyl products are exactly the target Weyl
products at the corresponding roots. No normalizing property of these
products is required for this equality.

`poweredWordMap` first performs the target reflection-word conjugations and
then precomposes with the root power. Induction on the word, using the
equality of the actual Weyl products and associativity, identifies it with
word conjugation of the powered root map.

`targetWordFamily` applies the transported source words to the target simple
maps. Constancy of root factors along each word proves that forming the Weyl
family from the powered simple maps equals applying the prescribed root
powers to this target word family. For corresponding bases, genuine target
simple parametrizations, and normalized target simple Weyl products, the
transported family is proved to consist of genuine target root
parametrizations by the published word-conjugation theorem.

This module supplies transport identities, not compatible commutator
relations. It does not construct normalized simple data, prove an ambient
homomorphism exists, or establish the affine split isogeny theorem.
