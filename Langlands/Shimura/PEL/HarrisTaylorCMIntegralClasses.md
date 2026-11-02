# Exact integral witnesses in the normalized CM class relation

This internal specialization combines the generic criterion in
`PolarizedWeilIntegralClasses` with the existing normalized CM specialization
in `HarrisTaylorCMPolarizedClasses` and the actual integral Harris order and
finite integer basis in `HarrisIntegralOrderActions`.

`classOf_eq_iff_integralPolarizedMultiple` compares two supplied actual
polarized level representatives satisfying the normalized joint determinant
and dimension condition. It also takes integral actions of
`D.harrisHodgePELIntegralOrder C` on these same abelian schemes, with the
agreement field identifying their rationalizations with the restrictions of
the existing rational actions. Existence of these restrictions remains an
input.

The left side is equality of their existing normalized numerical CM classes.
The existing joint-condition equivalence supplies the determinant and numerical
proofs for those classes; it uses the prescribed conjugated reflex scalar map.
The right side retains the original rational action isomorphism `e`, rational
unit multiplier `q`, and actual transport of the same fixed level orbit.
Its integral condition supplies exactly equivariant integral representatives
of both maps of `e`, nonzero denominators, both exact inverse-multiple
identities, and an exact integral polarization cross-multiple equation with
rational ratio equal to the square of the forward denominator times `q`.

The proof rewrites equality using the existing numerical tower criterion and
replaces the rational geometric polarization equation with its generic proved
equivalent. The integral existence direction uses the actual finite Harris
basis to clear finitely many equivariance discrepancies. Proof irrelevance
identifies the reconstructed proof of the original polarization equation in
the unchanged orbit transport. No new orbit, geometric point, isomorphism or
multiplier is chosen in that transport. The positive auxiliary left involution
and the original opposite right-action level convention are retained through
the existing constructions.

This comparison asserts no integral model existence, geometric isogeny,
geometric-point independence, representing scheme, smoothness or projectivity.
All existing geometric prerequisites and the supplied integral restrictions
remain assumptions.
