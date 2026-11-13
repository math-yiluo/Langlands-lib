# Proof of the top-layer norm–trace congruence (DH81 Corollary 3.12(i))

`Langlands.LocalFactor.NonabelianSystem.DeligneHenniart.TopLayer.topLayerNormTrace`
proves the published proposition
`Langlands.LocalFactor.NonabelianSystem.DeligneHenniart.TopLayerNormTraceStatement.{u,v,w}`
(module `Langlands.LocalFactor.DeligneHenniartTopLayerStatement`). Its type is
exactly that proposition. The statement and its correspondence with
Deligne–Henniart 1981 are described in `DeligneHenniartTopLayerStatement.md`,
which this proof leaves unchanged. No hypothesis is added. The theorem uses only
the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

The proof does not follow the dévissage of DH81 3.8–3.11 (cyclic extensions of
degree `p`, towers, tame base change). It works directly inside the Galois
extension `M`: the different and Hilbert's formula, plus an orbit decomposition
of the norm. It uses these helper modules, each with its own Markdown:

- `DeligneHenniartTopLayerOrders`: `ord_M = |G_0| ord_K` on `K`, Galois
  invariance of `ord_M`, and `|G_0| e_K = e_M`.
- `DeligneHenniartTopLayerDifferent`: Hilbert's formula
  `different(O_M/O_K) = m_M^{Σ_{i<N} (|G_i| - 1)}`.
- `DeligneHenniartTopLayerTrace`: the trace bound `trace_mem_additiveLattice`
  for an intermediate field `F`.
- `DeligneHenniartTopLayerOrbits`: ramp-sum estimates, fixed fields as p-adic
  fields with `|Gal(M/F_J)_i| = |J ∩ G_i|`, and stabilizer inequalities.
- `DeligneHenniartOrbitAlgebra` (written by Worker 126): sums over invariant
  sets via orbit sums, the orbit–stabilizer sum identity, norm and trace as
  products and sums over embeddings into a normal extension, and the
  extension of embeddings to automorphisms.

## Notation

The theorem introduces the binders of the target. Write:

- `G = Gal(M/K)`, with lower groups `G_i = lowerRamificationGroup TM K i`;
- `X = L →ₐ[K] M`, the `K`-embeddings of `L` into `M`, with the action
  `g • x = g ∘ x` (`embeddingAction`) and the inclusion `ι`;
- `H = Stab_G(ι)`; by `stabilizer_inclusion_eq_range` this is the image of
  `Gal(M/L)`, and `lowerGroupOrder TM L i = |H ∩ G_i|`
  (`lowerGroupOrder_eq_card_stabilizer_inf`);
- `t = herbrandPsi TM K n > 0`, `c = ⌈t⌉ ≥ 1`, and
  `N = ramificationCutoff TM K + ramificationCutoff TM L + c`, so `t ≤ c ≤ N`
  and both cutoffs are at most `N`.

Every `x ∈ X` is `g • ι` for some `g ∈ G` (`exists_smul_inclusion`, from
`exists_automorphism_extending_embedding`). In particular
`ord_M(x(a)) = ord_M(a)` for `a ∈ L` (`ord_embedding_apply`).

## The ramification hypothesis

The target supplies `w < n` such that every element of
`upperRamificationGroup TM K w` fixes `L`. Since `ψ` is strictly increasing,
`ψ(w) < ψ(n) = t ≤ c`. By antitonicity of the real lower numbering, `G_c` lies
in `upperRamificationGroup TM K w = G_{⌈ψ(w)⌉}`. Hence `G_c ⊆ H` (`hcH`).

## The order of `y`

`herbrandPhi_eq_sum` writes the target's bound `φ_{M/L}(t) ≤ ord_L y` as
`rampSum (|H ∩ G_i|) N t / |H_0| ≤ ord_L y`. By `ord_algebraMap_eq` for `M/L`,
`ord_M(y) = |H_0| ord_L(y)`, so

`rampSum (lowerGroupOrder TM L ·) N t ≤ ord_M(y)` (`hyR`).

## Conclusion 1: the trace

Write `n = m + 1` and `t' = ψ(m)`, so `0 ≤ t' < t`. Since all lower group
orders are at least `1`, `sub_le_rampSum_sub` gives
`rampSum (…) N t' ≤ rampSum (…) N t - (t - t') < ord_M(y)`. The trace bound
`trace_mem_additiveLattice` for `F = L` at level `m` gives
`Tr_{L/K} y ∈ TK.additiveLattice (-(m + 1)) = TK.additiveLattice (-n)`.

## Conclusion 2: the norm

Let `R = N_{L/K}(1 + y) - 1 - Tr_{L/K} y`.

**Expansion.** `algebraMap_norm_eq_prod_embeddings_normal` and
`algebraMap_trace_eq_sum_embeddings_normal` express the norm and the trace in
`M` through the embeddings. `prod_one_add_sub_one_sub_sum` then gives

`R = Σ_{S ⊆ X, |S| ≥ 2} P_S`, with `P_S = Π_{x ∈ S} x(y)`.

**Orbits.** The family of subsets with at least two elements is `G`-stable,
since `|g • S| = |S|`. By `sum_mem_of_orbit_sums` it suffices that each orbit
sum `Σ_{T ∈ G·S} P_T` is the image of an element of `TK.additiveLattice
(-(n + 1))`. This is `exists_orbit_sum_eq`. Fix `S` with `k = |S| ≥ 2`, its
stabilizer `J = Stab_G(S)` and `F = fixedPadicField J`.

1. `g(P_S) = P_{g•S}` (`algEquiv_prod_embeddings`), so `P_S` lies in `F`.
   `P_S ≠ 0` and `ord_M(P_S) = k ord_M(y)` (`prod_embeddings_ord`).
2. Lower groups of the stabilizer: by `lowerGroupOrder_fixedPadicField`,
   `card_stabilizer_finset_inf_le` and the description of `H`, for every `i`,
   `lowerGroupOrder TM F i = |J ∩ G_i| ≤ k |H ∩ G_i| = k lowerGroupOrder TM L i`.
   At `i = c`, `G_c ⊆ H` fixes every embedding (`le_stabilizer_finset`), so
   `J ∩ G_c = G_c = H ∩ G_c`.
3. The weight `k |H ∩ G_c| - |J ∩ G_c| = (k - 1) |H ∩ G_c|` is positive, and
   `c - 1 < t`. So `rampSum_pos` gives
   `rampSum (lowerGroupOrder TM F ·) N t < k · rampSum (lowerGroupOrder TM L ·) N t ≤ k ord_M(y) = ord_M(P_S)`.
4. `trace_mem_additiveLattice` for `F` gives
   `Tr_{F/K}(P_S) ∈ TK.additiveLattice (-(n + 1))`.
5. `sum_action_eq_card_stabilizer_nsmul` gives
   `Σ_{g ∈ G} g(P_S) = |J| · Σ_{T ∈ G·S} P_T`, and
   `sum_algEquiv_apply_eq_card_mul_trace` gives
   `Σ_{g ∈ G} g(P_S) = |J| · Tr_{F/K}(P_S)`. Since `M` has characteristic
   zero, `|J|` cancels: the orbit sum is `Tr_{F/K}(P_S)`.

Hence `algebraMap R` lies in the image of `TK.additiveLattice (-(n + 1))`, and
`R` lies in that lattice by injectivity.

**Units.** Let `z = 1 + y` and `u = 1 + Tr y` be the given units.
`v(Tr y) ≤ exp(-n) < 1`, so `v(u) = 1` (`Valuation.map_one_add_of_lt`).
`v(R) ≤ exp(-(n + 1)) < 1` and `N(z) = u + R`, so `v(N(z)) = 1`. Then
`v(N(z) u⁻¹) = 1`, and `N(z) u⁻¹ - 1 = R u⁻¹` has valuation
`v(R) ≤ exp(-(n + 1))`. These are the two conditions of
`TK.principalUnits (n + 1)`.

## Relation to the source

DH81 Corollary 3.12(i) is the commutativity of the diagram (3.4.1) for integers
`n > α(L/K)`. The two conclusions are the well-definedness of the trace row and
the commutativity, as explained in `DeligneHenniartTopLayerStatement.md`. DH81
derive it from Proposition 3.8. Here it follows from the different bound
(DH81 3.3 and Serre, *Local Fields*, IV §1, Proposition 4) applied to
the orbit sums of the norm expansion. The proof route differs from the source;
the proved proposition is exactly the published target.
