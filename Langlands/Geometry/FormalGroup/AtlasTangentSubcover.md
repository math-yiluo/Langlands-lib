# Tangent module restriction to a principal subcover

Retain a subset of the principal generators of a formal atlas whose ideal is the unit ideal. `BasicAtlas.tangentSubcoverEquiv` identifies the two compatible tangent modules over every affine test algebra by restricting their chart coordinates. Its inverse transports the retained vectors into each original chart and glues the coordinates on the image cover of that chart's test ring. The actual tangent transition cocycle gives overlap agreement. Restriction commutes with test coefficient extension.

Every principal cover of an affine ring has a finite principal subcover. Applying the finite-atlas localization theorem on that subcover and transporting it through the two restriction equivalences shows that compatible tangent vectors commute with principal localization for every atlas. `BasicAtlas.tangentAwayEquiv` gives this identification over the localized test ring. It sends a pure tensor to its scalar times the coefficient extension of the original vector.

This is a localization property of the affine tangent construction underlying Drinfeld, *Coverings of p-adic symmetric regions* (1976), §2 B, printed p. 110 (PDF p. 4).
