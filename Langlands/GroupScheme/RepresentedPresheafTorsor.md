# Represented torsor actions and gluing of affine models

This internal helper continues `PresheafTorsor`. A natural simply transitive
action on a represented presheaf produces an actual action on its scheme
representative. The universal pair of points defines the action morphism by
the representing bijection. Naturality identifies its values on every test
with the original action, and the original identity and multiplication laws
give the categorical action laws. Simple transitivity on all tests then
proves that the actual `ModObj.leftSMul` is an isomorphism.

`SmoothAffineModel` records an actual scheme representative with smooth,
affine and surjective structure morphism. Models of the restricted presheaf
over a base open cover glue whenever the original presheaf is a Zariski
sheaf. This uses the published full-slice Zariski representation gluing
theorem; each of the three geometric properties descends on that same open
cover. The action requires no separate gluing choices, since it is recovered
from the resulting representation.

Finally `Action.affineModel` packages the affine cocycle construction as
such a model for a smooth affine group over an affine base and a supplied
local section over an affine surjective étale cover. It additionally assumes
singleton sheaf descent for every surjective étale morphism `p : V → W` in
`Over S`: explicitly, `Presieve.IsSheafFor F (.singleton p)`. This is a
separate premise from the Zariski sheaf condition used by `zariskiGlue`.
This is an internal
descent step for the relative Levi torsor proof, whose geometric provenance
is Conrad, *Reductive group schemes* (2014), Corollary 5.4.6, p.178. It does
not assume a section over the original base.
