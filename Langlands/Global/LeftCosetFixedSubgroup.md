# Closed quotient embeddings for fixed subgroups

For subgroups `Γ` and `H` of a topological group `G`,
`LeftCosetSpace.subgroupInclusion Γ H` is the natural map

```text
(Γ ∩ H) \ H → Γ \ G.
```

The source uses `Γ.subgroupOf H`, the original subgroup of `H` consisting of
elements whose values lie in `Γ`. Both sides are the existing left coset spaces
with their quotient topologies. The map is defined for any subgroups; it is
injective, continuous, and sends the class of `h` to the class of its
underlying element of `G`.

`isClosedEmbedding_subgroupInclusion_fixed` proves that this exact map is a
closed topological embedding under the following hypotheses:

- `G` is a Hausdorff topological group whose topology is sequential;
- `Γ` is closed in `G` and carries the discrete subspace topology;
- `f : I → G →ₜ* G` is a finite family of continuous endomorphisms, each sending
  `Γ` into itself;
- `H` consists exactly of the elements fixed by every `f i`.

No local compactness, normality of either subgroup, invertibility of the
endomorphisms, or group action structure on the family is assumed.

This is an internal topological derivation intended for use in a Galois
scalar-extension argument. It does not construct an adelic Galois action or
identify its fixed subgroup with scalar-extended points.

The proof first shows that `H` is closed as an intersection of the equalizers
of `f i` and the identity. The central lemma
`isClosed_saturation_fixed` treats a closed set `E ⊆ H` invariant under left
multiplication by `Γ ∩ H`. It proves that its saturation
`⋃ γ : Γ, γ E` is closed in `G`.

Since the ambient topology is sequential, consider a sequence
`zₙ = γₙ eₙ` in that saturation converging to `x`. For each `i`,

```text
zₙ (f i zₙ)⁻¹ = γₙ (f i γₙ)⁻¹ ∈ Γ.
```

Continuity gives convergence of these expressions to `x (f i x)⁻¹`.
Closedness of `Γ` puts the limit in `Γ`; discreteness then makes the sequence
eventually equal to that limit. Finiteness of `I` provides a common index `N`.
For every later `n`, equality of these expressions implies that
`γ_N⁻¹ γₙ` is fixed by every `f i`. It belongs to `Γ ∩ H`, so invariance gives
`γ_N⁻¹ zₙ ∈ E`. Closedness of `E` yields `γ_N⁻¹ x ∈ E`, and hence `x ∈ γ_N E`.

Finally, lift any closed set in `(Γ ∩ H) \ H` to its closed, invariant
preimage in `H`, and then to a closed subset `E` of `G`. The inverse image
in `G` of its quotient image is exactly the saturation just proved closed.
The target quotient topology therefore makes `subgroupInclusion` a closed
map. Its previously established continuity and injectivity give the closed
embedding.
