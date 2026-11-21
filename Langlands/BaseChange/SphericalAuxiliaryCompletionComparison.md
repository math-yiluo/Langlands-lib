# Standard factor comparison at a spherical auxiliary place

`SphericalAuxiliaryCompletionComparisonStatement` uses actual cuspidal spectral
presentations over a cyclic extension of number fields and finite pair-factor choices for
their standard global additive characters. At the chosen lower place the first component
is spherical, and the first component at each upper place is spherical with the
residue-degree power of the lower Satake multiset. The actual local components carry
these spectra. This also allows the calculation for contragredient components whose
spectra are obtained from a local smooth-dual comparison. The second component at these places
is equivalent to the trivial GL₁ action. The finite list of lower determinant twists is
given by Hecke characters whose local restrictions exhaust the norm-trivial characters,
each appearing as many times as there are upper places. `GlobalNormCharacterRestriction`
provides such a list.

The conclusion identifies the products of forward Euler values of the chosen local
factors at every spectral parameter. It also compares the positive bases formed from
the epsilon exponents and residue cardinalities. The proof chooses one twist per local
character. It identifies the factors belonging to repeated restrictions using the
local twist class and the uniqueness of the canonical additive character and self-dual
Haar measure. At each upper place it puts the local factor data over the residue prime
of the lower completion and applies the spherical norm formulas on the original fields.
Multiplying these identities counts each lower restriction once for every upper place.

The calculation implements the spherical case of Arthur–Clozel, Chapter 1, Lemma 6.13.
The hypotheses include the spherical spectrum comparison at every place above the
chosen place, including when the extension is ramified.
