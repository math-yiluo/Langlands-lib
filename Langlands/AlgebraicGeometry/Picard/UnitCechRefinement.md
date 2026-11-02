# Refinement of ordered actual-unit cocycles

For a scheme `X : Scheme.{u}` and open families indexed by `Type u`,
`pairUnits_refine` identifies the transition units of an ordered cochain
refined by `Cech.refine` with `CocycleGluing.refineCocycle` of its original
transition units. It requires neither closedness nor a covering hypothesis.
The proof composes the two restrictions and identifies the reindexed ordered
pair, using the published dependent-tuple restriction identity.

For a closed ordered actual-unit one-cochain, `refinementIso` gives an actual
isomorphism of the original and refined glued module sheaves when the refined
family covers `X`. It applies the published gluing refinement isomorphism after
the transition-unit identity. No finiteness, affineness, compactness or separation
hypothesis is used.

`commonCover` is the product-indexed family `U i ∩ V j`.
`commonCover_eq_top` proves this family covers when both input families cover,
by choosing a member of each family at every point. `commonRefineLeft` and
`commonRefineRight` are the ordered-cochain restriction homomorphisms to this
family. Their product index remains in `Type u`; finite input indices give a
finite product without any further geometric hypothesis.

`nonempty_iso_glued_iff_commonCover` compares closed ordered unit cocycles on
two possibly different full covers: their actual glued module sheaves are
isomorphic if and only if the difference of their restrictions to the product
cover is the differential of an ordered zero-cochain there. The sign is the
second refined cocycle minus the first. To prove this, transport an isomorphism
in either direction through the two refinement isomorphisms and apply the
published fixed-family gauge/coboundary criterion on the common cover.
Closedness on that cover follows because refinement commutes with the
Čech differential. The result also holds for infinite covers.

These are internal compositions of the published ordered-unit and gluing
refinement constructions. They do not yet assert independence of actual H1
classes, naturality or Picard representability.
