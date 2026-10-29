# The Levi upper-unipotent group inside a minimal orbit stabilizer

Author: Worker 379.

## Scope and conventions

Fix a field `K : Type uK`, a rank `n`, an ordered block shape `B : BlockShape n`, and
`v : Geometric.MinimalRepresentatives B (BlockShape.singletons n)`. Put

- `r = GeneralLinear.permutation n K v.val`,
- `P = B.parabolic K` and `U = GeneralLinear.upperUnipotent n K`,
- `UM = Subgroup.pi Set.univ (fun i : Fin B.length => upperUnipotent (B.size i) K)`.

`UM` is the actual subgroup of the Levi product `B.Levi K` whose blocks are all upper
unipotent. The stabilizer is the published carrier `Geometric.orbitStabilizer P U r`.
It consists of the `q ∈ U` with `r⁻¹ * q * r ∈ P`, and
`Geometric.stabilizerToInducing P U r` sends such a `q` to `r⁻¹ * q * r ∈ P`. This
file introduces no new carrier types: it uses only these published subgroups, written
out in full in every signature.

The file constructs only the embedding of `UM` and proves its elementary properties.
It does not determine the full stabilizer, classify orbits, prove any localization or
finiteness result, or use a representation.

## Containment

`permutation_conj_leviEmbedding_mem_upperUnipotent B K v m` proves

```lean
permutation n K v.val * B.leviEmbedding K (m : B.Levi K) *
    (permutation n K v.val)⁻¹ ∈ upperUnipotent n K
```

for every `m : UM`. The proof works entry by entry and does not assume the containment.
The published `permutation_conjugate_entry` rewrites entry `(x, y)` of the conjugate as
entry `(v⁻¹ x, v⁻¹ y)` of the block-diagonal matrix. Both indices are then written as
block coordinates `B.index i a` and `B.index j b` using `B.indexEquiv`.

- If `i ≠ j`, the entry vanishes by `B.leviEmbedding_apply_ne`.
- If `i = j` and `y < x`, the entry is entry `(a, b)` of the block `m i`.
  `v.property.1 i` says that `a ↦ v (B.index i a)` is strictly monotone, which is the
  first clause of `IsMinimalRepresentative`. Since
  `v (B.index i b) = y < x = v (B.index i a)`, we get `b < a`. The entry therefore
  vanishes because `m i` is upper unipotent (`UpperUnipotent.entry_eq_zero`).
- On the diagonal the entry is a diagonal entry of some block `m i`, so it equals
  `1` (`UpperUnipotent.entry_diag`).

## The maps

`minimalLeviUpperUnipotentEmbedding B K v : UM →* upperUnipotent n K` is the raw
homomorphism. It is the composite of the subgroup inclusion of `UM`, the Levi embedding
`B.leviEmbedding K` and conjugation `MulAut.conj r`, corestricted to `U` by the
containment lemma. Its ambient law `minimalLeviUpperUnipotentEmbedding_val` holds by
`rfl`:

```lean
(minimalLeviUpperUnipotentEmbedding B K v m : GeneralLinear n K) =
  r * B.leviEmbedding K (m : B.Levi K) * r⁻¹
```

A caller can compose any character `θ : upperUnipotent n K →* G'` with this raw map.

`minimalStabilizerLeviEmbedding B K v` is the principal map

```lean
UM →* orbitStabilizer (B.parabolic K) (upperUnipotent n K) (permutation n K v.val)
```

It corestricts the raw map to the stabilizer. Membership holds because
`r⁻¹ * (r * ι m * r⁻¹) * r⁻¹⁻¹ = ι m`, by `group`, and `ι m` is the value of the
published section `B.leviInParabolic K m`, which lies in `P`. Here `ι` is
`B.leviEmbedding K`.

## Laws

All statements below are for an arbitrary `m : UM`. In Lean, `(m : B.Levi K)` is
`m.val`.

- `minimalStabilizerLeviEmbedding_val`: the underlying element of `U` is the raw
  embedding (`rfl`).
- `minimalStabilizerLeviEmbedding_val_val`: the ambient evaluation law. The underlying
  matrix is exactly `r * B.leviEmbedding K m.val * r⁻¹` (`rfl`).
- `minimalStabilizerLeviEmbedding_mem_upperUnipotent`: that matrix lies in
  `upperUnipotent n K`.
- `stabilizerToInducing_minimalStabilizerLeviEmbedding`: the exact equality
  `stabilizerToInducing P U r (minimalStabilizerLeviEmbedding B K v m) = B.leviInParabolic K m.val`.
  It is proved by `Subtype.ext`, `stabilizerToInducing_apply`, `leviInParabolic_val`
  and `group`.
- `leviProjection_stabilizerToInducing_minimalStabilizerLeviEmbedding`: the exact
  equality `B.leviProjection K (stabilizerToInducing P U r (minimalStabilizerLeviEmbedding B K v m)) = m.val`.
  It follows from the previous law and the published `leviProjection_section`.
- `minimalLeviUpperUnipotentEmbedding_injective` and
  `minimalStabilizerLeviEmbedding_injective`: injectivity. Cancelling `r` on both sides
  reduces it to the published `B.leviEmbedding_injective` and `Subtype.ext`.

## Topology

Assume `[TopologicalSpace K] [IsTopologicalRing K]`. Every group carries its published
topology:

- `GeneralLinear n K` carries the published topology; `U` and the stabilizer carry
  inherited subgroup topologies;
- `B.Levi K` carries the product topology and `UM` the subgroup topology.

`continuous_minimalLeviUpperUnipotentEmbedding` composes four continuous maps: the
subtype inclusion, `(B.leviEmbeddingContinuous K).continuous`, multiplication by the
two constant matrices `r` and `r⁻¹`, and `Continuous.subtype_mk`.
`continuous_minimalStabilizerLeviEmbedding` adds one more `subtype_mk` for the
stabilizer. No local compactness or field-inversion continuity is used.

## Half modulus

Let `p` be prime, `F : PadicField p` (universe arbitrary) and `T : F.TopologicalData`.
For `B`, `v` and `m` as above over `F.Carrier`,
`parabolicHalfModulus_stabilizerToInducing_minimalStabilizerLeviEmbedding` proves

```lean
T.parabolicHalfModulus B
    (stabilizerToInducing (B.parabolic F.Carrier) (upperUnipotent n F.Carrier)
      (permutation n F.Carrier v.val) (minimalStabilizerLeviEmbedding B F.Carrier v m)) = 1
```

The proof follows these steps:

1. Rewrite with the stabilizer law above and the published
   `parabolicHalfModulus_section`.
2. `leviHalfModulus_eq_one` reduces the claim to `T.leviModulus B m.val = 1`.
3. `normOneLevi_le_ker_leviModulus` and `mem_normOneLevi` reduce this to
   `T.determinantNorm (B.size i) (m.val i) = 1` for every block `i`.
4. Since `determinantNorm = normalizedAbsUnits.comp determinant`, the auxiliary lemma
   finishes the proof.

The auxiliary lemma is `pi_upperUnipotent_determinant_eq_one`, proved for any
commutative ring. It states that every block of an element of `UM` has determinant one.
The proof uses `Matrix.det_of_isUpperTriangular` and the unit diagonal. No
modulus-triviality, smoothness, finiteness or representation-theoretic premise is
used.

## Source correspondence and provenance

Original source: `bernstein-zelevinsky-1976-representations-gln`, I. N. Bernshtein and
A. V. Zelevinskii, *Representations of the group GL(n,F) where F is a
non-Archimedean local field*, Russian Math. Surveys 31:3 (1976), proof of Theorem 7.12,
steps (2)–(4), printed p.61 (PDF SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`; printed p.61 is
PDF page 61). I read pp.59–62 for this file and checked the formulas of p.61 on the
rendered page image. No erratum for this source is recorded in the literature index,
the Library or the project notes.

The source defines the following objects:

- `W^(β)`: the set of `w` whose permutation `ω` has `ω⁻¹` preserving the order inside
  every segment `I_k` (step (2));
- `X_w`: the `U`-orbit of `P_β w`, with stabilizer `H_w = U ∩ w⁻¹ P_β w` (step (3)).

Step (4) asserts `ʷH_w ⊃ U ∩ G_β`, where `ʷH = w H w⁻¹`. This is the conjugation
`h ↦ w h w⁻¹` that also defines `ρ_w` in step (3). The source proves the inclusion by
noting that `U ∩ G_β ⊂ ʷU` follows from the definition of `W^(β)`.

In the Library, the representative of the orbit `P r⁻¹ U` is `r = w⁻¹`.
`orbitStabilizer P U r` is then `U ∩ r P r⁻¹ = H_w`, and the source's inclusion
`w⁻¹ (U ∩ G_β) w ⊂ H_w` becomes the map `m ↦ r m r⁻¹` constructed here. `UM` is the
Library's `U ∩ G_β`, written as a subgroup of the Levi product. In the Library, the
order condition on `W^(β)` is the clause "`a ↦ v (B.index i a)` strictly increasing" of
`IsMinimalRepresentative`. Under the convention of `permutation_conjugate_entry`, this
is the source's condition that `ω⁻¹` preserves order inside each segment. The Lean
proof uses only the Library clause, so this dictionary is explanatory. Worker 330
recorded it when publishing the task.

The following are derived interfaces, not literal assertions of the source:

- the arbitrary-field scope;
- the explicit homomorphism and its laws;
- the injectivity and continuity statements;
- the triviality of the half modulus for an arbitrary supplied `T`.

They are the reusable form of private steps in the published proof
`Langlands.Representation.Whittaker.ParabolicInducedCoinvariantFinitenessProof`, whose
proof scripts this file follows.
