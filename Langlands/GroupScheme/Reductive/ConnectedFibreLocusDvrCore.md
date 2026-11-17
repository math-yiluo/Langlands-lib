# The discrete-valuation-ring case of the connected-fibre specialization

This module states, without proof, the local input of the proof of
`Langlands.GroupScheme.ConnectedFibreLocusClosedStatement` (Conrad, *Reductive group
schemes* (2014), Proposition 3.1.12).

## `Langlands.GroupScheme.ConnectedFibreLocus.DvrCoreStatement`

For every discrete valuation ring `R` (a domain), every field `K` with an `R`-algebra
structure making it a fraction field of `R`, and every smooth affine group scheme `G` over
`Spec R` whose geometric fibres all have reductive identity components
(`identityComponentReductiveLocus G = Set.univ`): if the underlying space of the generic
fibre `G_K = G ×_R K` (the base change along `algebraBaseMap R K = Spec (R → K)`) is
connected, then the underlying space of the special fibre `G_k`, `k = R/𝔪` (the base change
along `algebraBaseMap R (IsLocalRing.ResidueField R)`), is connected.

## Provenance

This is the special case of Proposition 3.1.12 over the spectrum of a discrete valuation
ring: its generic point specializes to its closed point, so connectedness of the generic
fibre forces connectedness of the closed fibre. Conrad reduces the general proposition to
this case; the proof of the target statement in this task does the same (local
constructibility of the connected-fibre locus plus stability under specialization, the
latter realized by discrete valuation rings over a Noetherian model). The fibres are stated
as base changes along the ring maps `R → K` and `R → R/𝔪` rather than as residue-field
fibres; these agree with the residue-field fibres at the generic and closed points of
`Spec R` up to extension of the base field, which does not change connectedness of smooth
affine groups.
