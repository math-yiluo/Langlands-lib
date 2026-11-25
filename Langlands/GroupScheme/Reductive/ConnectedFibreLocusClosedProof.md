# Proof: the locus of connected fibres is closed

The theorem `Langlands.GroupScheme.connectedFibreLocusClosed` proves the Library statement
`Langlands.GroupScheme.ConnectedFibreLocusClosedStatement` (Conrad, *Reductive group
schemes* (2014), Proposition 3.1.12) in every universe. Let `G → S` be a smooth `S`-affine
group whose geometric fibres all have reductive identity components. Then the set of points
`s ∈ S` whose residue-field fibre `G_s` is connected is closed. If a generic point of `S`
has connected fibre, then every fibre is connected.

The proof combines two results.

1. `ConnectedFibreLocus.connectedFibreLocusClosed_of_dvrCore`
   (module `ConnectedFibreLocusReduction`) derives the statement from
   `ConnectedFibreLocus.DvrCoreStatement`, the case of a discrete valuation ring. The set
   of points with connected fibre is the geometrically connected fibre locus of the
   structure morphism, so it is locally constructible over any base
   (module `ConnectedFibreLocusFibres`). It is stable under specialization. Over an affine
   open the group descends to a finite-type model over a Noetherian ring, and there every
   nontrivial specialization is realized by a morphism from the spectrum of a discrete
   valuation ring, to which `DvrCoreStatement` applies. A locally constructible set stable
   under specialization is closed. Closedness gives the second clause, because a generic
   point specializes to every point.
2. `ConnectedFibreLocus.dvrCore` (module `ConnectedFibreLocusDvrCoreProof`)
   proves `DvrCoreStatement`. Over a discrete valuation ring `R` the published relative
   identity component `H ⊆ G` is smooth, affine and geometrically connected, and it is
   reductive by `ConnectedFibreDvrGeometry`. If the generic fibre of `G` is connected, the
   generic inclusion `H_K → G_K` is an open and closed immersion with nonempty image,
   hence an isomorphism. The published étale DVR open-subgroup isomorphism theorem then
   makes `H → G` an isomorphism, so the special fibre of `G` is the image of the
   geometrically connected special fibre of `H`, which is connected.

The Lean proof is the one-line application of the first result to the second.

Conrad's own proof follows the same reduction to a discrete valuation ring. It then argues
with a lifted maximal torus, its centralizer and the Weyl group of the special fibre. The
Lean proof of the discrete-valuation-ring case uses the relative identity component and the
étale open-subgroup isomorphism theorem instead.
