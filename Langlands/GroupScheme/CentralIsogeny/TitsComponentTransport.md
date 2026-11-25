# Component realization reduces to simply connected groups

This derived internal module uses the actual Cartan/star equivalence constructed
for a central isogeny. It preserves and reflects Cartan connectivity, restricts
the vertex bijection to the entire component, and identifies the full
absolute-Galois stabilizer subgroup exactly. These statements use every
ordered Cartan entry and the action of each Galois element; they do not use
zero restrictions to maximal split tori.

`componentFactorOfCentralIsogeny` transports a complete component witness
from a simply connected `C` through a central isogeny `π : C → G`.
The factor and complement remain the actual group schemes in the supplied
witness, and their covering map is composed with `π`. The original covering
map onto `C` is an isomorphism by simple connectedness of `C`, so the composite
retains the full scheme-theoretic central-kernel condition. The component
bijection preserves every ordered Cartan entry. Both existential Galois lifts
remain outside the quantification over vertices. Finally, finiteness of `π`
bounds the split rank of `C` by that of `G`, so the original witness's
anisotropy implication gives the required one.

`SimplyConnectedTitsComponentFactorStatement` is the original realization
obligation restricted to simply connected semisimple groups, over every field
and at every universe parameter. It is a stated premise in this module.
`semisimpleTitsComponentFactor_of_simplyConnected` derives the unchanged
published full target from it: take an actual simply connected central cover,
choose actual Tits-index data on that cover, use the exact central-isogeny
Cartan/star comparison, realize the preimage vertex under the supplied
premise, and apply the complete witness transport. No unconditional component
realization theorem is claimed here.

The connectivity and simultaneous-lift transport proofs adapt the existing
full-index transport constructions to the weaker Cartan/star
comparison; the missing zero-vertex field is unnecessary for this purpose.
