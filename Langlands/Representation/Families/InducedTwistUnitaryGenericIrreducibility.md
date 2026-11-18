# Generic irreducibility of represented induction at unitary twists

`Langlands.Renard.AlgebraicFamily.exists_generic_leviInduction_isIrreducible_of_unitary`
is a supporting theorem for the density proof for actual common-Levi
induction. The field and inducing carrier have independent universes. The
theorem takes a represented rational parabolic with a Levi, its matching
unipotent radical and their product isomorphism, and a split component of
the Levi. For an irreducible admissible unitarizable smooth representation
of the Levi points, it gives a nonzero polynomial in the rational
unramified character coordinates. At each character in the polynomial's
principal open whose values have norm one, the normalized induction of
the twist is irreducible.

## Implemented proof

1. `inducedTwistQuotientExclusion` supplies the polynomial. On its
   principal open, the split-central exponents of the inducing twist are
   excluded from the Jacquet object of any quotient of the induction by
   a nonzero invariant subspace.
2. The twist preserves irreducibility and admissibility.
   `isUnitarizable_twist_iff` preserves unitarizability under the norm-one
   condition. `leviInductionAdmissible` and `leviInductionUnitarizable`
   give admissibility and unitarizability of the induction itself.
   Since compact open subgroups are cofinal, `admissibleUnitarySemisimplicity`
   gives a retraction of each subrepresentation inclusion.
3. If there were a nonzero proper subrepresentation, composing its
   retraction with its inclusion would give a nonzero projection onto it.
   The kernel is nonzero, since injectivity of the projection would force
   the projection to be the identity. Factoring through the quotient by
   this kernel gives a nonzero intertwiner from the quotient into the
   induction. Admissibility descends to that quotient.
4. Admissible Schur supplies a split-central exponent of the inducing
   twist through `exists_isGeneralizedEigencharacter_of_isAdmissible`.
   First adjointness and Jacquet admissibility, through
   `isGeneralizedEigencharacter_jacquet_of_ne_zero_induction`, put that
   exponent in the Jacquet object of the quotient for the same parabolic.
   This contradicts the exclusion in step 1. The induction is nonzero by
   `nontrivial_leviInduction` applied to the irreducible twist.

## Provenance

The exclusion step comes from the Library's derived formulation of the
quotient argument in T. Konno, *A note on the Langlands classification and
irreducibility of induced representations of p-adic groups*, Theorem 4.2,
pp. 402–405 (2003), registered as `konno-2003-langlands-classification`.
The registered PDF has SHA256
`71931493382f2c8aa60734e27328db9a0f39c3af0b9c47bf746adcfa47fc0b42`.
The present lemma combines that exclusion with admissible unitary
semisimplicity for use on the unitary part of the principal open.
