# Geometry from connected reductive residue fibres

Worker 717.

This derived module proves three bridges for the actual pullbacks of a group
scheme `G` over an arbitrary scheme `S`, uniformly in universe `u`. The common
hypothesis is that each residue-field fibre
`RelativeIdentityComponent.residueFiber G s` is `IsConnectedReductive`.
The Prop-valued definition `HasConnectedReductiveResidueFibers G` names exactly
this condition.
The proofs use published Library results and add no literature assumptions.

`connectedReductive_residueFibers_baseChange` proves the same condition after an
arbitrary base change `b : S' ⟶ S`. A residue-field fibre over `S'` is compared by
`baseChangeCompIso` with the pullback of `G` along the composite field-valued
point of `S`. The published `fieldReductive_of_residueReductive` gives connected
reductivity of that pullback.

`quasiCompact_of_connectedReductive_residueFibers` proves that `G → S` is
quasi-compact. There is no smoothness hypothesis on the structure morphism and
no quasi-separatedness hypothesis on `S`. The proof passes to the standard
affine open cover of `S`, transfers the residue-fibre hypothesis using the first
lemma, and applies
`RelativeIdentityComponent.quasiCompact_of_residueFibers` there. Its
quasi-separated-base assumption holds on each affine chart. The required
smoothness and connectedness are fields of `IsConnectedReductive`; affineness
of each fibre over its field supplies compactness. Quasi-compactness of a
morphism is Zariski local on the target, so these chartwise conclusions descend.

`isReductive_of_isAffineHom_of_connectedReductive_residueFibers` assumes in
addition that `G → S` is smooth and affine, and proves `IsReductive G`.
For each specified geometric point, the same published field-valued-pullback
lemma gives a connected reductive geometric fibre. Its `isPseudoReductive`
consequence is precisely the geometric-fibre clause of `IsReductive`.

These lemmas do not prove that a group with reductive residue fibres is affine.
That implication is a separate prerequisite.
