# Geometric ingredients for relative Levi base change

This internal module proves the geometric reductions needed to restrict the actual
relative Levi moduli. It does not prove radical stability under an extension of
algebraically closed fields, and therefore does not yet construct the full Levi
functor.

`RelativeLevi.PreservesUnipotentRadicals b P` defines the condition that the
given morphism `b : T → S` preserves every supplied actual relative radical in
`P`. It quantifies over all group schemes `V` over `S` and homomorphisms
`r : V → P` satisfying the unchanged relative-radical predicate. The definition
does not assert that this condition holds; it names the explicit premise used
by the final Levi-preservation reduction.

`isIso_subgroupMultiplication_baseChange` preserves the actual morphism
`L × U → P` after an arbitrary base change. The published
`subgroupMultiplication_baseChange` identifies its pullback with multiplication
of the pulled-back inclusions after the canonical product comparison. Solving
that equality expresses the new multiplication as a composite of isomorphisms.
No commutation between the two subgroups is required.

`IsRelativeLeviSubgroup.smooth_ambient` observes that a relative Levi presentation
makes its ambient group smooth: the source of the multiplication isomorphism is
the product of the smooth Levi and smooth radical. Smoothness transports through
that actual isomorphism. This holds without an affineness or connectedness premise.

`IsRelativeUnipotentRadical.baseChange_of_geometric_extension` separates the
unresolved field input from the remaining geometry. Its explicit premise requires,
for each point of the new base, that the original chosen geometric-fibre radical
remain a radical after the compatible extension to the new chosen algebraic
closure. Closedness, smoothness and normality follow by base change. The actual
geometric-fibre comparison then proves the final field of the existing relative
radical predicate.

`IsRelativeLeviSubgroup.baseChange_of_radical_preservation` assumes
`RelativeLevi.PreservesUnipotentRadicals b P`. It pulls back a
radical witnessing the supplied Levi inclusion and uses preservation of the
multiplication isomorphism. Its premise is an explicit mathematical obligation;
this result does not assert unconditional Levi preservation.

All schemes and group schemes remain in the single arbitrary universe `u`.
These are internal consequences of the published product, smoothness, subgroup
base-change and geometric-fibre comparison APIs, using the unchanged predicates
in `RelativeLevi.Basic`. The module introduces no replacement Levi predicate,
existence hypothesis or proposition asserting the torsor theorem.
