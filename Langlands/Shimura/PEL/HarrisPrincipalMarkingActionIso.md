# Compatible Harris markings under actual polarized action isomorphisms

An actual isomorphism of abelian schemes intertwining the supplied integral
order restrictions also intertwines their full rational actions.
`harrisIntegralActionIso` uses uniqueness of rational extension of the
integral actions to construct this equivariant rationalization.

If the isomorphism pulls the second polarization back to the first,
`harrisIntegralPolarizedActionFrameIso` transports the actual Weil frame
with scalar \(1\). The map on rational Tate modules is induced by the
same actual isomorphism. Its integral Tate map and the map of its
inverse identify the full integral images. This preserves and reflects
the normalization condition. Restricting the full comparison to
torsion gives `harrisIntegralFrameReduction_apply_iso`.

`harrisPrincipalFullLevelCondition_iff_actionIso` compares the
compatible-marking condition when the isomorphism carries the global
ordered torsion sections to one another. The section equation
restricts to each fibre and gives equality on all residue-linear
coordinates. Together with the finite reduction comparison this
carries the normalized lifting condition in both directions, at the
same geometric point.
