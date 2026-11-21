# Indexing norm characters at a unique completion

`DistinguishedNormCharactersStatement` uses a cyclic extension of number fields
with a unique place above the chosen lower place. The lower and upper completions
are identified with a supplied finite extension by compatible field isomorphisms.
Assume the given finite set `X` consists exactly of the characters trivial on the
norms of that extension. The complex characters of the global Galois group index
the Hecke characters trivial on the idelic norm, and finite restriction transported
to the supplied lower field gives an equivalence of that index type with `X`.
For the same Hecke family, restriction at every finite place exhausts the
characters trivial on the norms from an upper completion. Each such character
occurs with multiplicity the number of upper places.

The unit norms commute with the two field identifications, so a character of the
lower completion is trivial on norms exactly when its transported character is.
The global restriction theorem gives every character of the lower completion
trivial on norms. Each restriction fiber has cardinality equal to the number of
upper places. Since that number is one, restriction is injective as well.

This identifies the indices of the global product in the completed equation
(6.15) with those of the local norm-character product at the distinguished
place in Arthur–Clozel, Chapter 1, proof of Proposition 6.9(ii), printed p. 70.
