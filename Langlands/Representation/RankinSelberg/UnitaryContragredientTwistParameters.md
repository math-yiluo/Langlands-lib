# Unitary contragredient twist parameters

This internal construction chooses the exact finite set of contragredient
unramified-twist parameters of two supplied irreducible, admissible,
unitarizable complex representations of `GL_(r+1)(F)`, and records that every
parameter has complex norm one. The field universe and the two representation
carrier universes are independent. Topology and normalized absolute value use
`F.canonicalTopologicalData`, as in `IsContragredientTwistParameter`.

`UnitaryContragredientTwistParameterSet` contains a finite set `parameters`, its
membership equivalence with `IsContragredientTwistParameter F π σ`, and the
norm-one law for every member. `unitaryContragredientTwistParameterSet` constructs
this datum from the actual irreducibility, admissibility, and unitarizability
of both supplied actions. It chooses a finite set using
`exists_finset_contragredientTwistParameters`; its membership equivalence
determines the set exactly, even when the set is empty. Neither representation
is required to be supercuspidal.

The supporting lemma `norm_character_eq_one_of_twisted_bilinear` applies to
arbitrary group representations with supplied unitary central characters.
For a nonzero bilinear form satisfying
`β (π g v) (σ g w) = (χ g)⁻¹ * β v w`, choose an evaluation `β v w ≠ 0`.
At a central element, the two scalar action laws identify `(χ g)⁻¹` with the
product of the two central character values, after cancellation of that
nonzero evaluation. Taking norms proves that `χ g` has norm one.

`IsContragredientTwistParameter.norm_eq_one` applies the published
`unitarizableCentralCharacter` to both actual actions. A parameter supplies a
complex exponent `u`, an unramified character `χ` with values `|x|^(-u)`, and
an equivalence from the determinant twist of `π` to the smooth contragredient
of `σ`. The published
`exists_twisted_bilinear_of_contragredient_equiv` gives the required nonzero
bilinear form. Evaluate it at the scalar inverse uniformizer
`centralSpectralElement F.canonicalTopologicalData (r+1)`.
The determinant-weight identity identifies the character value there with
`(q^(-u))^(r+1)`. Its norm is one by the preceding lemma.
Since `r+1` is positive and a complex norm is nonnegative, `‖q^(-u)‖ = 1`.
The argument uses central characters of both original actions directly.

The provenance is an internal derivation from the imported finite-parameter,
bilinear-covariance, central-spectral-element, and unitary-central-character
results. Worker 1739 supplied the central-character proof route; Worker 1765
implemented the proof and the finite-set construction. This contribution
provides the unit-circle support needed when applying the supercuspidal
factor formula. It does not assert an L-factor identity or prove the host
associated-pair induction statement.
