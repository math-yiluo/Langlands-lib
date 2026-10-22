# Open normalizer stabilizer of a compact open subgroup

For a topological group `G`, a subgroup `U : Subgroup G`, an open subgroup
`K : OpenSubgroup U`, and `hK : IsCompact (K : Set U)`, this module constructs

```lean
Langlands.compactOpenNormalizerStabilizer U K hK :
  OpenSubgroup (Subgroup.normalizer (U : Set G))
```

The only ambient instances are `[Group G]`, `[TopologicalSpace G]`, and
`[IsTopologicalGroup G]`. The topologies on U and its actual normalizer are
the induced subgroup topologies. Compactness and openness of K are in U.
No Hausdorff, local compactness, nonarchimedean, or closed-subgroup assumption
is imposed, and K is not assumed open in G.

## Exact membership and subgroup construction

Write `L = K.toSubgroup.map U.subtype` for K's image as a subgroup of G. The
underlying subgroup is the pullback of `Subgroup.normalizer (L : Set G)`
along the subtype homomorphism from the normalizer of U to G. Consequently
its identity, multiplication, and inversion laws are inherited from
Mathlib's normalizer and subgroup preimage constructions.

For `g : Subgroup.normalizer (U : Set G)`, the intrinsic theorem
`Langlands.mem_compactOpenNormalizerStabilizer_iff` proves exactly

```lean
g ∈ Langlands.compactOpenNormalizerStabilizer U K hK ↔
  (K.toSubgroup.map U.subtype).map (MulAut.conj (g : G)).toMonoidHom =
    K.toSubgroup.map U.subtype
```

Here `MulAut.conj (g : G)` sends x to `g * x * g⁻¹`. This characterization
is Mathlib's `Subgroup.mem_normalizer_iff_map_conj_eq` applied to L.

The additional theorem
`Langlands.mem_compactOpenNormalizerStabilizer_iff_smul` proves the equivalent
pointwise criterion `∀ u : U, u ∈ K ↔ g • u ∈ K`. The action is Mathlib's
canonical action of U's normalizer on U, defined by the element of U with
ambient value `(g : G) * (u : G) * (g : G)⁻¹`. It is not an arbitrary action
or an additional instance parameter.

The private proof of this pointwise characterization identifies membership
of `(u : G)` in L with membership of u in K. The forward direction then
uses the normalizer condition. Conversely, forward conjugation carries
witnesses in K to witnesses in L, while inverse conjugation recovers a
witness in K whenever the conjugate lies in L. This proves the normalizer
condition on every element of G, including elements outside U.

## Implemented openness proof

The map `(g,u) ↦ g • u` from `N_G(U) × U` to U is continuous: after
inclusion in G it is the product of the two continuous subtype projections
and the inverse of the first projection. Continuity into the subgroup
follows from `Continuous.subtype_mk`.

The inverse image of K under this map is open and contains `{1} × K`.
Mathlib's `generalized_tube_lemma`, applied to the compact singleton and
compact K, produces open sets V and W with `1 ∈ V`, `K ⊆ W`, and
`V × W` contained in that inverse image. Thus every g in V carries K into K.

The open identity neighborhood `V ∩ inv ⁻¹' V` has the same property for g
and its inverse. Applying the inverse property to `g • u` proves the
reverse implication in `u ∈ K ↔ g • u ∈ K`. This neighborhood therefore
lies in the stabilizer subgroup. Finally,
`Subgroup.isOpen_of_mem_nhds` makes the subgroup open. The construction
bundles this proof as the `OpenSubgroup.isOpen'` field.

## Provenance and scope

This is an internal derived definition, with its intrinsic membership and
openness proofs, for the normalizer Haar-modulus development. It does not
formalize a separately cited numbered literature result. Worker 76 supplied
the compactness/tube-lemma strategy in the task specification; Worker 128
authored the Lean implementation and this explanation. Both are credited.

The construction imports only the pinned Mathlib modules
`Mathlib.Topology.Algebra.OpenSubgroup`,
`Mathlib.Topology.Compactness.Compact`, and
`Mathlib.GroupTheory.Subgroup.Centralizer`. The principal existing tools are
`generalized_tube_lemma` in the compactness module, the actual normalizer
action in the centralizer module, and `Subgroup.isOpen_of_mem_nhds` in the
open-subgroup module. The algebraic conjugate-image criterion comes from
`Mathlib.Algebra.Group.Subgroup.Basic` through these imports.

No Haar measure, modulus character, or HaarModulus module is used or
constructed here. Independent semantic review, machine validation, and
Library publication are separate from development compilation.
