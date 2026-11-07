# Proof of uniqueness of a normalized gamma decomposition

This internal algebraic result supports the proof of JPSS (1983), Theorem
(8.2), printed pages 444–448. The gcd argument here is a derived proof,
not a transcription of the source's segment induction.

Remove the polynomial gcd of `P` and `B`, writing `P = g D` and `B = g E`
with coprime quotients `D` and `E`. Cancel the nonzero rational image of `g`
in the supplied cross multiplication identity.

If `z` is a root of `D`, it is a nonzero root of `P`, so `‖z‖ ≥ a`.
The strict radius inequality gives `‖δ/z‖ < b`. The dual polynomials do not
vanish there. Evaluating the cancelled rational identity at `z` makes
`E(z) = 0`, contradicting coprimality. The same argument at a root of `E`
makes `D(z) = 0`. Evaluation uses the published regularity API, since a
rational evaluation is not an unrestricted ring homomorphism.

The fundamental theorem of algebra now makes both quotients constant.
Taking constant coefficients of the two factorizations, and using the
normalizations of `P` and `B`, makes those constants equal. Hence `P = B`.

The auxiliary theorem `gammaDecompositionUniqueness_of_ratio` accepts the
corresponding quotient identity directly. The dual root exclusions apply at
zero, so both dual polynomials, their rational images, and their reflections
are nonzero. Cross multiplication reduces this corollary to the main theorem.
