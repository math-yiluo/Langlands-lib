# Point-independent normalized classes from actual integral Harris Weil levels

This internal construction uses the raw full-action level tower, the existing
actual fixed-orbit point transport, and the original normalized CM class and
compatible-geometric-family constructions. No new literature assertion is made.

The arithmetic, dual-witness, ambient geometric polarization, full-order Rosati
and determinant condition, prescribed relative dimension, torsion and adelic
premises are those of `HarrisIntegralCMLevelClass`. The direct test scheme is
quasi-separated. The point comparison takes actual field-valued points and an
actual isomorphism of their finite-cover fibre functors.

`harrisIntegralCMFullActionLevelPointIso` reindexes the existing Weil level
transport by the original Harris level functor. It retains all original level
transporters. Its path-independence theorem uses the proved path independence
of actual fixed orbits. The representative comparison is definitional: the
family, integral action and polarization stay unchanged, and the actual orbit
is transported. Proof irrelevance identifies the faithfulness proofs derived
from the two supplied orbits.

`harrisIntegralCMFullActionLevelOriginalClassNatTrans` sends a raw level orbit
to the existing normalized CM class of its integral representative. It uses
the unchanged rational-isogeny quotient. The point-comparison square commutes
for every supplied fibre-functor path and every original level transporter.

If the direct test scheme is connected and locally noetherian,
`harrisIntegralCMFullActionLevelFamilyNatTrans` takes an actual geometric point
with its own algebraically closed field and sends its orbit to the existing
compatible family of normalized classes at all actual geometric points. It
composes the preceding map with the inverse of the existing family-evaluation
isomorphism. Evaluation at the original point recovers the unchanged class.
The final theorem proves independence of the starting geometric point when
the starting orbit is canonically transported. Its proof cancels evaluation
at the new point and uses the point-comparison square and the existing
composition law for family evaluation and geometric comparison.

This is a comparison of actual pointed level towers with the existing
point-independent normalized family tower on a fixed connected test scheme.
It does not construct a level scheme or ambient moduli scheme, assert base
naturality, discharge admissibility, or prove smoothness or division
projectivity. Those remain host representability obligations.
