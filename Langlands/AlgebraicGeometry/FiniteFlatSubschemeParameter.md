# Flat closed subschemes of a finite flat scheme

Let `X` be finite, flat and locally of finite presentation over the spectrum of a
commutative ring. `FiniteFlatSubschemeParameterStatement` gives a separated and
locally finitely presented parameter scheme for the flat, locally finitely
presented closed subschemes of `X` after base change. Its universal family is
specified by the actual ideal sheaf on the product of `X` and the parameter
scheme. For every test scheme an admissible ideal sheaf is the pullback of the
universal ideal along a unique map to the parameter. The universal family is
finite over the parameter, and evaluating it commutes with successive changes
of test.

The proof embeds the finite scheme in finite projective space using
`Langlands.AbelianScheme.isHProjective_of_isFinite`. The existing equivalence
between such embeddings and presentations by sections provides the input for
`hilbertSchemeUniversalFamily`. The Hilbert scheme's ideal-sheaf classification
then gives the universal family. The comparison of test pullbacks is itself
cartesian, by cancellation of pullback squares.

This derived construction provides the finite-jet parameter used in Raynaud's
SGA 3, Exposé XV, proof of Lemma 5.3 (recomposed pp. 265–266). It classifies
closed subschemes directly through the Hilbert scheme, collecting all possible
locally free quotient ranks in a single parameter.
