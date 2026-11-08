# Restriction on the literal parabolic Jacquet model

This internal derived adapter applies the selected unitary-weight restriction
to the precise literal-subgroup Jacquet functor used by the Plancherel target.
It introduces no external source and does not change the target or its imports.

The field is any nonarchimedean local field in universe `u`. The connected
reductive ambient scheme is affine, with canonical rational-point topology;
its point group is locally compact and nonarchimedean. The actual maps
`p`, `l`, `a`, `n`, root presentation `pres`, geometric-radical witness `hn`,
semidirect decomposition `h` and radical closedness `hU` have the meanings
of the host target. The literal Levi is `parabolicLeviPointSubgroup p l`.
The published closedness theorem supplies its local compactness. Ambient
and target representation carriers have independent universes `uV` and `uW`.

`parabolicJacquet_obj_isAdmissible` transports the published dynamic
contraction basis along the presentation's equalities for the actual radical
and Levi images. The existing normalized-Jacquet admissibility theorem then
applies directly to `jacquetFunctor h hU`. Thus an admissible ambient source
has an admissible Jacquet module in this literal subgroup model. No global
existence of compatible presentations, quotient compactness, ambient
representation temperedness or separate admissibility premise on this Jacquet
module is assumed.

`parabolicJacquetUnitaryRestriction` is the existing
`splitUnitaryWeightRestriction` specialized to this Jacquet action and the
actual `parabolicSplitComponentPointHom pres`. Centrality is the host's
proved split-component range-centrality theorem. The selected part is exactly
the existing `selectedWeightPart` for characters of the actual `A(F)` whose
existing normalized real parameter is zero. No additional weak-Jacquet object
or replacement action is defined. This adapter does not assert a comparison
to the represented-parabolic category's independently bundled unitary module.

The injectivity result combines Jacquet admissibility with a supplied
`UnitaryCentralCharacter` of the Levi target. The rank result instead uses
the host's exact `IsSquareIntegrableModCentralSubgroup` hypothesis on
`C = range(parabolicSplitComponentPointHom pres)`, with its derived normality
and supplied quotient Haar measure. That predicate supplies the target's
unitary central scalar action. The published scalar restriction then bounds
the cardinal rank of Hom from the whole literal Jacquet action by the rank
of Hom from its selected unitary weights. Neither target irreducibility nor
full target temperedness is needed for this restriction step.

For the intended application the ambient source will be the actual induced
representation. Its admissibility still needs to be supplied, for example
from admissibility of the inducing representation and actual parabolic
quotient compactness. The Hom bound on its selected unitary part still
requires a genuine conjugate decomposition or filtration and multiplicity
argument. This module proves neither of those remaining facts and does not
prove generic irreducibility.

Integration gives the local instances used here module-specific names to permit
joint imports. Their types, values, and local scopes are unchanged.
