# Full field-point lifts for locally finite analytic maps

Author: Worker 620.

`StrongHom.IsFiniteAt.fieldPointLift` chooses an actual full field-valued
point of the saturated source presentation above a prescribed target
field point. Its inputs are a saturated strong map `g`, a source point
`y` where `g` is finite, a full target field point `p`, and the equality
`p.point = g.baseMap y`. The coefficient field is complete and
ultrametric. The extension field is complete, algebraically closed and
ultrametric, with its normed coefficient algebra structure.

The construction uses `IsFiniteAt.hasFieldPointLiftAt` with the published
proof `PresentedAffinoidAlgebra.domainCompletedResidueSurjectivity`.
Classical choice selects the witness. The two specification lemmas
`fieldPointLift_point` and `fieldPointLift_map` are the two components of
its witness property: its ordinary point is exactly `y`, and its image
under the actual strong map is exactly the prescribed full field point
`p`. The latter equality retains every chart evaluation and restriction
compatibility. No uniqueness of the chosen source field point is asserted.
The field, space, atlas-index and extension-field universes are independent.

The theorem `SaturatedAtlasPresentation.strongEtaleFieldPointImageLift`
discharges the domain-comparison premise in the published conditional
strong image-lifting theorem. Thus it proves the existing
`StrongEtaleFieldPointImageLiftStatement` with independent field, space
and extension-field universes; that statement uses the same universe for
spaces and atlas indices. It requires only membership of the ordinary
target point in the image of the strong map and concludes existence of
a preimage of the entire full field point. There is no supplied
completed-residue comparison, strictness, nontrivial-valuation,
Hausdorffness or compactness premise.

This is an internal construction and deduction from the imported public
finite full-point lifting and canonical domain completed-residue proofs.
The earlier finite lifting theorem combines a prescribed finite chart
character, extension to all charts and recognition quasi-isomorphisms.
The canonical domain comparison now supplies its formerly explicit
analytic input. The module does not prove localized right cancellation
or either finite-diagram input of the geometric-point theorem. Those
remain needed to obtain the unconditional site-point result.
