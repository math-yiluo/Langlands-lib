# Degree-zero spectra and the diagonalizable action relation

For any commutative ring `R`, abelian character group `M`, and natural
`CharacterAction.Action a` on an `R`-algebra `B`, `invariantAlgebra a` is the
actual degree-zero subring of its coaction, with the inherited `R`-algebra
structure. The scalar map lands in degree zero because the coaction is
`R`-linear. The inclusion in `B` respects this scalar structure.
`quotientScheme a` is its spectrum over `Spec R`, and `spectrumProjection a`
is induced by the inclusion of this actual subring.

Under the explicit strong-grading hypothesis, `invariant_isPushout` identifies
the two copies of this inclusion with the pushout whose two outgoing maps
are the constant-coefficient map and the coaction. The proof transports the
ordinary tensor-product pushout along the previously constructed canonical
isomorphism `B tensor_(B_0) B ≅ B[M]`, checking both tensor inclusions.
Contravariant spectrum then gives `spectrumProjection_isPullback` in the
category of schemes over `Spec R`; the forgetful functor reflects this square.
Thus the spectrum of `B[M]`, with the two coaction-relation projections, is
the fiber product of the coordinate spectrum with itself over `Spec B_0`.

The theorem `spectrumProjection_flat_surjective` applies the previously proved
faithful flatness of the actual degree-zero inclusion and the affine spectrum
criterion for flatness and surjectivity. No field, nonzero-ring, Noetherian,
finite-generation, torsion-free, smoothness or reducedness hypothesis is used.
The action is supplied, and strong grading is still an explicit premise here.
The actual closed-subgroup translation grading supplying that premise is
constructed in `AffineDiagonalizableGraph`.

This is derived internal spectrum and scalar bookkeeping for SGA 3, Exposé
VIII, §§4–5, especially Theorem 5.1 and its comparison with `Spec A_0`.
It constructs the spectrum quotient and its affine relation square; it does
not yet assert the group quotient, all-test coset criterion, or finite
presentation of its projection.
