# Two-facet transport between arbitrary restricted apartments

For an existing Tits system, this unit constructs a transporter between any
two restricted apartments containing the same two admissible parabolic
subgroups `P` and `Q`. The transporter belongs to `P ∩ Q` and conjugation by it
carries the first apartment, as a set of subgroups, onto the second.
Consequently it fixes under conjugation every subgroup containing `P` or `Q`.
The construction is universe polymorphic and imposes no finiteness condition.

The proof is an internal extension of
`IsTitsSystem.exists_mem_two_parabolics_restrictedApartment_eq`.
Write the first facet as `t P_X t⁻¹`, where `t = a n₀` and `n₀` is in the
normalizer. Right normalizer invariance means that `t` represents the original
reference apartment. In these coordinates the second facet has the form
`n P_Y n⁻¹`. Conjugate the target apartment by `t⁻¹` and apply the previously
proved comparison for a standard parabolic and a normalizer conjugate.
Conjugating the resulting element by `t` gives the stated transporter.
Apartment equivariance and the elementary subgroup-image identities prove its
transport property and membership in both actual parabolic subgroups.

The source motivation is Kaletha–Prasad, *Bruhat–Tits theory: a new approach*
(2023), Proposition 1.5.6(4)–(5), printed pp.56–57 / PDF pp.87–88. The proof of
(5) uses the parabolic double-coset correspondence to compare apartments while
fixing two facets and their faces. That standard-coordinate group argument is
implemented in the imported `TitsApartmentComparison`; the coordinate change
and chosen arbitrary-reference transporter here are derived content.

These results concern the parabolic model of the existing restricted
apartments. They assert no pointwise fixation in an affine realization, no
distance independence, and no metric on the building quotient.
