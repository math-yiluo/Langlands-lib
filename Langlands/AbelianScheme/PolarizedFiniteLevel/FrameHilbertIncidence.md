# Incidence of marked sections in a projective closed family

`Langlands.AbelianScheme.PolarizedFiniteLevel.FrameHilbert.incidenceIdeal I σ`
is the supremum of the ideal sheaves pulled back from `I` along the ambient
marks `σ`. Each mark defines an actual section of relative projective space by
pairing it with the identity of the base.

`factorsThrough_incidence_iff` proves the universal property with arbitrary
scheme tests. A factorization through the closed subscheme of an ideal is
equivalent to containment of that ideal in the test morphism's kernel. The
supremum is contained in the kernel exactly when each pulled-back marking
ideal is contained in it. The pushforward and pullback adjunction for ideal
sheaves then gives the same containment on the base-changed family, where it
is again equivalent to factorization through a closed subscheme. This treats
incidence scheme-theoretically.

The base-change square for the closed family is obtained by pasting the square
for the inverse image of a closed immersion with the base-change square for
relative projective space. For a closed embedding that realizes the family,
`Datum.Realizes.subschemeIso` identifies its source with the closed family via
its scheme-theoretic image. The equality of the projective marks follows by
comparing both projections of relative projective space.

This construction supplies incidence in the frame-normalized relative form of
Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, 3rd ed. (1994),
Proposition 7.3, printed pp. 132–134 (PDF pp. 145–147). At the start of that
proof the marks already belong to the family by construction of the pointed
Hilbert scheme. The relative formulation starts with ambient sections, and a
realization marks all level coefficients, so the closed incidence condition is
imposed on every supplied mark. The registered source is
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`.
