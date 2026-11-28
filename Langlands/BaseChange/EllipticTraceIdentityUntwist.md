# Removing determinant norm twists from the elliptic trace identity

`EllipticTraceIdentityDeterminantUntwistStatement` concerns representations `π` of `GL_n(F)`
and `τ` of `GL_n(E)`, where `F` is a topological field and `E` is a topological cyclic
`F`-algebra with chosen generator `σ`. The two general linear groups are Hausdorff, locally
compact and totally disconnected. Let `ω : Fˣ →* ℂˣ`, let `χF` be `ω ∘ det`, and let `χE`
be `ω ∘ N_{E/F} ∘ det`. Assume both characters have open kernel and that `π` and its twist
by `χF` are admissible. An elliptic trace identity for the twisted representations then
gives `HasEllipticTraceIdentity σ l π hπ τ`.

## Proof

`HasEllipticTraceIdentity.of_twist` uses the more general conditions that the character
upstairs is σ-invariant and both characters take equal values on norm-associated pairs.
The twisted intertwiner also intertwines the original representation, since the two
scalar factors in the intertwining relation agree and are invertible. Admissibility of
the original upper representation follows from `isAdmissible_twist_iff`.

Multiply the two test functions by the corresponding inverse characters.
`AreConcordant.mul_characters` preserves their concordance, and the new functions satisfy
the original support conditions. `twistedDistribution_twist_eq_comp` computes the two
traces for the twisted representations, using the identity endomorphism on the ordinary
side. The character and its inverse cancel on each test function and the nonzero constant
is reused. For determinant twists, `IsNormAssociated.norm_determinant_units_eq` gives the
equality on associated pairs, and norm invariance under a base-algebra automorphism gives
σ-invariance.

`HasEllipticTraceIdentity.of_equiv` also transports the identity between equivalent pairs
of representations by conjugating the intertwiner upstairs and using trace invariance
under equivalence on both sides.

These implications are derived from the definitions of the elliptic trace identity and
the integrated traces, together with the Library's character-weighting and determinant-norm
identities.
