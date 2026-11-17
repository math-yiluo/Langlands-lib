# Schwartz synthesis from fixed-level derivative estimates

This is an internal conditional construction for the VI.3.1 proof. It does not
prove a derivative estimate or the source-normalized packet target. It uses the
published `OrbitSectionLevel`, `OrbitSectionSpace`, `Level`, and `Space`
topologies without changing or comparing them.

For a function-valued complex-linear map `T` from smooth orbit sections, suppose
that `T` sends the level fixed by `H × H`, with `H` open and contained in the
compact packet subgroup `K`, to functions bi-invariant under the same `H`.
The predicate `OrbitSectionSchwartzEstimates` asks, at every such level and every
real output exponent `r`, for a finite set of input derivative seminorms and a
nonnegative constant bounding the extended output seminorm `nu`. The finite
set and constant may depend on `H` and `r`, and must be uniform in the section.

`orbitSectionCompactLevel` equips `H` with compactness inherited from `K`.
`OrbitSectionSchwartzSynthesis.levelLinear` restricts `T` to the existing
Schwartz level for this same compact open subgroup. The proof first bounds the
extended seminorm by `ENNReal.ofReal` of a finite real expression, establishing
finiteness before taking its real value. Mathlib's
`WithSeminorms.continuous_of_isBounded` and the published seminorm descriptions
then prove continuity of this level map.

Every smooth section belongs to one input level. The fixed-level construction
therefore puts its image in the Schwartz submodule. The definition `linear`
restricts `T` to that submodule; `continuousLinear` uses the existing universal
property `OrbitSectionSpace.mkCLM` and the continuous inclusion of each
Schwartz level into `Space`. Both application laws are definitional: the
constructed maps retain `T`'s original values at every group point.

This construction is derived from the Library definitions and Mathlib's
seminorm continuity criterion. Waldspurger's VI.3.1 proof, printed pp.302–305
(PDF pp.68–71) in the registered 2003 Plancherel paper, motivates the uniform
fixed-level estimates. The implemented topological construction is internal;
it supplies none of the lower-Levi continuation packages, weak-constant-term
identities, positive-part bounds, or actual rational Xi and full-height
estimates needed to discharge its hypotheses for the source-normalized packet.
