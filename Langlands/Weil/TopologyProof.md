# Generic Weil inertia topology and uniqueness

`Langlands.Weil.topologyProperties` proves the complete accepted proposition
`Langlands.Weil.TopologyProperties` in arbitrary universe `u`. The hypotheses
are a group `Gamma`, a topology making it a topological group, and a continuous
homomorphism `phi` into Mathlib's actual profinite completion of the integers.
There are no separation, compactness, surjectivity, or Frobenius-lift hypotheses.

The pullback is the existing subgroup of `Gamma` times the discrete group
`Multiplicative Int`, consisting of pairs `(g,n)` with
`phi(g) = frobenius(n)`. Its original topology is the product-subtype topology.
Original inertia is `ker(phi)` with the subgroup topology from `Gamma`;
its inclusion is `g -> (g,1)`, where multiplicative `1` means integer degree
zero. All group operations and topologies are those of the accepted definitions.

## Implemented proof

1. The degree kernel is the inverse image of the singleton `{1}` under the
   continuous degree map. The integer degree group is discrete, so that
   singleton and its inverse image are open.
2. The image of the inertia inclusion equals the degree kernel. An included
   inertia element has degree one by definition. Conversely, a pullback pair
   `(g,n)` in the degree kernel has `n = 1`. Its defining equation then gives
   `phi(g) = frobenius(1) = 1`, so `g` lies in original inertia and maps back
   to the pair. This argument is proved locally in this file; it does not
   assume a separately stated algebraic-properties target.
3. The inertia inclusion followed by the first-coordinate projection is
   the ordinary subgroup inclusion into `Gamma`. That composite is an
   embedding. Both maps are continuous, so `Topology.IsEmbedding.of_comp`
   proves that the inertia inclusion is an embedding. Its image is open by
   steps 1 and 2, yielding `Topology.IsOpenEmbedding`.
4. The original pullback is a topological group by the existing product and
   subgroup instances.
5. Fix any alternative topology `t` on the same underlying pullback group
   satisfying the two accepted hypotheses: it is a group topology and the
   same inertia inclusion is an open embedding from the fixed original
   inertia topology. For each of the two open embeddings,
   `Topology.IsOpenEmbedding.map_nhds_eq` identifies the image of inertia's
   identity-neighborhood filter with the target identity-neighborhood filter.
   The source filter and underlying inclusion are identical, so the two
   target filters agree. The inclusion preserves the identity.
   `IsTopologicalGroup.ext` now proves `t` equals the original topology.
   That Mathlib theorem uses group translations to recover every neighborhood
   filter from the identity filter.

The last step compares two different topology parameters explicitly. The
original topology and original inertia topology were captured in the accepted
target before its alternative-topology binder. The conclusion therefore
establishes genuine uniqueness against that fixed original topology.

## Exact dependencies and provenance

This is an internal proof of accepted statement
`9e116c5c-4503-4f92-8dec-62ce6615b117`, version 1, whose checked target
fingerprint is
`a576f184cee0734c48f60eddb94643507ae69122daedb8c32953b5ee613514e8`.
The sole project definition dependency is the accepted pullback artifact
`993e4326-4390-4fc8-94a7-82829061b1ea`, version 1. Both pairs were verified
accepted, published, and current before this proof was developed.
The proof imports the unchanged statement and Mathlib's group-neighborhood
interface. It does not assume the separate algebraic or universal-property
targets as theorems.

The motivating original source is Guy Henniart, *Representations du groupe
de Weil d'un corps local* (1980), Section 2.1, printed page 158 / PDF page 5.
That passage prescribes that inertia is open in the local Weil group and
carries its Galois-induced topology. It was read in the retained original:
`C:/Central-Library/Henniart--Representations du groupe de Weil dun corps local--1980.pdf`,
literature ID `henniart-1980-weil-representations`, SHA256
`451a8bd31a58be9bf5ce49588503c2d229b1a73bf3e65ae0c7b2f491c1c4e017`.
The generic uniqueness result here is derived from the explicit pullback and
Mathlib interfaces; it is not quoted as a theorem from that passage.
No local-field identification or claim that the Weil topology is the subgroup
topology from the ambient Galois group is made.

The environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1:
Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, and Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`. Worker 10 authored this proof
and its explanation, using Worker 2's independently accepted definitions and
statement. Compilation is a development check; registered independent proof
checking and independent semantic review and publication establish acceptance.
