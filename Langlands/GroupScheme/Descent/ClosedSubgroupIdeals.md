# Closed subgroup descent through defining ideals

Internal deductions from the existing closed immersion lift and the adjunction
between pullback and pushforward of ideal sheaves.
`DefiningIdealDescent p I` records an actual ideal sheaf on the target of `p`
and an equality between its pullback and `I`. It makes no effectiveness claim.
Membership in a closed
subgroup's image is equivalent to containment of its defining ideal sheaf
in the kernel of the test morphism. This retains arbitrary test schemes.

If the ideal sheaf of a closed subgroup over a base change is the pullback
of an ideal sheaf on the original ambient scheme, canonical overlap transport
preserves vanishing of this ideal. Thus the two actual overlap images are
equal. This module does not yet establish ideal descent from Galois invariance.
The final wrapper applies this result to `DefiningIdealDescent` data.
