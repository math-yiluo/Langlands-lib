# p-adic JPSS factors along an isomorphism of p-adic fields

Author: Worker 5731. This is a supporting lemma module for the proof of
`Langlands.Global.PoleComparison.HenniartCompositeFactorStatement` (Task 5230).
It states no new published mathematics. It specializes
`FieldTransport.Factors` to isomorphisms of p-adic fields, where the Haar
measure hypotheses of that module hold, and so shows that the published p-adic
Rankin–Selberg relations `IsPadicPairLPolynomial`, `IsPadicPairEpsilonFactor`
and their symmetric versions are invariant under isomorphisms of p-adic fields.

## Normalized Haar measures

- `normalizedCompactOpenHaar_map Θ K hK K' hK' hKK'`: for a topological group
  isomorphism `Θ : G ≃ₜ* G'` of Borel topological groups and compact open
  subgroups `K` of `G` and `K'` of `G'` with `Θ g ∈ K' ↔ g ∈ K`, the pushforward
  along `Θ` of the published Haar measure `normalizedCompactOpenHaar K hK`
  (the Haar measure giving `K` mass `1`) is `normalizedCompactOpenHaar K' hK'`.
  `G'` is locally compact because `K'` is a compact neighbourhood of `1`. The
  pushforward is a regular left-invariant measure, so Mathlib's uniqueness
  theorem `isMulLeftInvariant_eq_smul_of_regular` makes it a scalar multiple of
  `normalizedCompactOpenHaar K' hK'`. Both measures give `K'` mass `1`
  (`Θ⁻¹ K' = K`), so the scalar is `1`.

Next fix nonarchimedean local fields `F` and `E`, `σ : F ≃+* E` with `hσ`, `hσs`
as in `FieldTransport.Integrals`, and
`hO : ∀ x, σ x ∈ O_E ↔ x ∈ O_F`, where `O_F` and `O_E` are the integer rings
of the valuations of the `ValuativeRel` structures.

- `fieldEquiv_mem_levelOpenSubgroup_zero_iff`: `T g` lies in the published
  level-zero subgroup `Conductor.levelOpenSubgroup E n 0` exactly when `g` lies
  in `Conductor.levelOpenSubgroup F n 0`. By the published
  `Conductor.levelSubgroup_zero` and `Conductor.mem_integralSubgroup` this
  subgroup is `GL_{n+1}(O)`, the matrices with integral entries and integral
  inverse, and `T` commutes with inversion.
- `generalLinearHaar_map` and `unipotentHaar_map`: the published normalized Haar
  measures `generalLinearHaar E n` of `GL_{n+1}(E)` and `unipotentHaar E n` of
  its upper unipotent subgroup are the pushforwards along `fieldEquiv` and
  `unipotentEquiv` of the corresponding measures over `F`. Both measures are
  defined in `Langlands.Representation.RankinSelberg.Measures` as
  `normalizedCompactOpenHaar` of the level-zero subgroup (intersected with the
  unipotent subgroup in the second case), so this is the first item applied to
  the previous one.

## p-adic fields

Now `F` and `E` are p-adic fields (`PadicField p`, with their canonical
topological data) and `f : F.Carrier ≃ₐ[ℚ_p] E.Carrier`.

- `algEquiv_mem_integers_iff`: `f x` is a canonical integer of `E` exactly when
  `x` is a canonical integer of `F`. Both directions are the published
  restriction `Weil.Local.extensionIntegerMap` of a `ℚ_p`-embedding to integer
  rings, applied to `f` and `f.symm`.
- `padicGeneralLinearEquiv F E f n : GL_n(F) ≃* GL_n(E)` is the entrywise
  isomorphism, i.e. `fieldEquiv n f.toRingEquiv` with the continuity of `f` and
  `f.symm` supplied by the published
  `VirtualRepresentation.PadicSupercuspidal.continuous_algEquiv`.
  `padicGeneralLinearEquiv_apply` gives its entries.

The main results take additive characters `ψ` of `F` and `ψ'` of `E` and
additive Haar measures `ν` of `F` and `ν'` of `E` (for the canonical topologies
and Borel σ-algebras), related by

- `hψ : ∀ x, ψ' (f x) = ψ x` and
- `hν : ν'.measure = ν.measure.map f`.

For `π` a representation of `GL_{r+1}(E)` and `τ` one of `GL_{n+1}(E)`, write
`π ∘ f` for `π.comp (padicGeneralLinearEquiv F E f (r + 1)).toMonoidHom`.

- **`isPadicPairLPolynomial_comp_iff`**:
  `IsPadicPairLPolynomial E ψ' ν' π τ P ↔ IsPadicPairLPolynomial F ψ ν (π ∘ f) (τ ∘ f) P`.
- **`isPadicPairEpsilonFactor_comp_iff`**:
  `IsPadicPairEpsilonFactor E ψ' ν' π τ e ↔ IsPadicPairEpsilonFactor F ψ ν (π ∘ f) (τ ∘ f) e`.
- `isPadicSymmetricLPolynomial_comp_iff` and
  `isPadicSymmetricEpsilonFactor_comp_iff`: the same for the published
  symmetric relations `IsPadicSymmetricLPolynomial` and
  `IsPadicSymmetricEpsilonFactor`, which apply the pair relation in the order
  of decreasing rank. Both sides split on the same condition `n ≤ r`.

Proof of the two main results. The published p-adic relations use the residue
cardinality `q` and the normalized absolute value of the canonical data; the
published `PadicField.CanonicalTransport.residueCardinality_eq` and
`PadicField.CanonicalTransport.normalizedAbs_map` show that they agree on the two
sides (the latter is the hypothesis `habv` of `FieldTransport.Factors`).
`algEquiv_mem_integers_iff` provides `hO`, hence the Haar hypotheses `hG`, `hU`
of `FieldTransport.Factors`. The epsilon statement is then
`isPairEpsilonFactor_comp_iff`. The L-polynomial relation
`IsPadicPairLPolynomial` asks for right invariance of `unipotentHaar` and a
compatible quotient measure, and that `IsPairLPolynomial` holds for every
compatible quotient measure. The first clause transfers by
`isMulRightInvariant_unipotentHaar_iff` and
`compatibleMeasureExists_unipotentHaar_iff`. For the second, every quotient
measure over `E` is a pushforward of one over `F` (`exists_map_eq`), its
compatibility transfers by `isCompatible_unipotentHaar_map_iff`, and the
L-polynomial relation by `isPairLPolynomial_comp_iff`.
