# Prescribed-map isogeny rigidity over a strictly Henselian DVR

`Langlands.GroupScheme.StrictHenselianDVRIsogenyRigidityStatement` is an internal
proof interface extracted from the proof of Conrad, *Reductive group schemes*
(2014), Proposition 6.1.10, pp.192–193.

Let `R` be a discrete valuation ring which is Henselian and whose residue field
is separably closed, and let `K` be its fraction field. Let `G` and `H` be
reductive group schemes over `Spec R`. For a specified homomorphism `f : G → H`,
assume that its base change to every residue-field fibre is an isogeny, meaning
a finite flat surjection. If its base change along `Spec(R/𝔪) → Spec R` is an
isomorphism, then its base change along `Spec K → Spec R` is an isomorphism.
All rings, fields and schemes are quantified in the same arbitrary universe.

This is a statement only. It does not provide a proof or assert that `f` itself
is finite. Its conclusion concerns the actual base change of `f`, rather than
the existence of an abstract isomorphism between the two generic-fibre groups.
The special fibre uses the quotient homomorphism `IsLocalRing.residue R`;
the other residue fibres use the canonical residue-field maps of `Spec R`.

The provenance is internal because this packages one step of Conrad's proof
as a separate implication. After reduction to a strictly Henselian DVR and
passage to a quotient by a finite flat normal subgroup, the proof on pp.192–193
establishes exactly the needed generic-fibre rigidity for the induced map with
isomorphic special fibre. The interface retains fibrewise isogeny as an explicit
hypothesis and imposes no splitting, centrality, or characteristic assumption.
