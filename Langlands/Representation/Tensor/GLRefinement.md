# GL tensor refinement with exact rank transports

Author: Worker 175.

This module constructs `Langlands.FiniteTensor.glRefinementEquiv`,
an actual representation equivalence between the original external tensor
pulled to the refined Levi and the nested tensor of the original factors after
the specified rank transports. It introduces no representation equivalence as
an assumption.

The data are an algebraic p-adic field `F : PadicField.{uF} p`, its selected
topological data `T`, two shapes `B,D : BlockShape n`, a refinement `S` of `D`,
an equivalence `e : (Sigma (fun j => Fin (S j).length)) ≃ Fin B.length`, and
rank equalities `h a : (S a.1).size a.2 = B.size (e a)`. The factors have type
`σ i : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier)` with independent
field and carrier universes. No positive total rank, irreducibility, dimension,
admissibility, unitarity or ambient coordinate identity is required. Empty
overall shapes at total rank zero are permitted. Each existing inner shape
`S j` has positive total rank `D.size j` and therefore nonzero length. Both
tensor carriers lie in `Type uV` because the coefficient and finite index
universes are zero.

Write `τ j k := (h ⟨j,k⟩).symm ▸ σ (e ⟨j,k⟩)`. The source action is
`(external (fun i => (σ i).representation)).comp
(B.leviRefinementEquiv D S e h F.Carrier).symm.toMonoidHom`.
The target action is
`(external (fun j => external (fun k => (τ j k).representation))).comp
(refinedLeviEquiv F.Carrier D S).symm.toMonoidHom`.
Thus both actions are actions of the actual refined subgroup. The pullbacks
use the inverse coordinate maps. The statement does not replace this subgroup
by a merely isomorphic abstract product.

`rankCastLinearEquiv` constructs the actual carrier map along a rank equality
by equality elimination. `rankCastLinearEquiv_action` uses the same elimination
to identify matrix reindexing by `finCongr h` and prove its intertwining formula.
At reflexive equality the matrix reindexing is the identity, as proved entrywise.

`glRefinementLinearEquiv` first applies `regroupLinearEquiv` and then two
`PiTensorProduct.congr` maps built from the factor carrier maps. Its generator
formula sends `tprod ℂ v` to
`tprod ℂ (fun j => tprod ℂ (fun k =>
rankCastLinearEquiv F T (h ⟨j,k⟩) (σ (e ⟨j,k⟩)) (v (e ⟨j,k⟩))))`.

`glRefinementEquiv` uses this linear equivalence. It proves equivariance by
extensionality of linear maps from the indexed tensor product. On generators,
expanding the external actions and the generator formula reduces the claim to
one factor. `BlockShape.nestedLeviEquiv_symm_apply` identifies that factor's
original group coordinate as the rank-reindexed nested coordinate, and
`rankCastLinearEquiv_action` finishes the equality. Tensor extensionality
establishes equivariance on all vectors, not only generators.

`glRefinementEquiv_toLinearEquiv` exposes the constructed linear equivalence.
`glRefinementEquiv_tprod` gives the preceding formula at representation level,
and `glRefinementEquiv_symm_tprod` proves that the inverse recovers the original
pure tensor from this displayed transported family.

The provenance is internal tensor and equality-transport algebra. The published
`Langlands.Group.GL.RefinementCoordinates` supplies the actual Levi maps and
inverse coordinate formula. The pinned Mathlib implementation
`Mathlib/LinearAlgebra/PiTensorProduct/Basic.lean`, commit
`5ed2965256430c3649e86755f9576b54eca72435`, supplies indexed tensor congruences
and their generator formulas (read at lines 595–616). No additional literature
theorem is asserted.

The generic tensor map is imported from the published
`Langlands.Representation.Tensor.FiniteRegrouping`, whose finite outer
associator and regrouping map are reused without alteration. This module adds
the GL rank transports and compatibility with the concrete refined Levi.
It does not assert an induction-in-stages theorem or the analytic grouping
of square-integrable blocks.
