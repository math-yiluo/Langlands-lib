# Completeness of the Harish-Chandra Schwartz space `C(G)` (III.6)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.Completeness`, namespace
`Langlands.HarishChandraSchwartz`. It builds on
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.Basic` (the levels `Level Ξ σ K` = `C_K`,
the space `Space Ξ σ` = `C(G)`, its inductive-limit topology, the universal property
`Space.continuous_iff_continuous_comp` = III.6(1), `Space.continuous_eval_level`) and on the
Library theorem `Langlands.compactOpenSubgroupBasis` (compact open subgroups form a
neighborhood basis of `1` in a weakly locally compact nonarchimedean group).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082.

- III.6 (printed p. 271, PDF p. 37), after the definition of `C(G) = ⋃_H C_H` with the
  inductive-limit topology of the topologies of the `C_H`: "L'espace `C(G)` est un espace
  vectoriel topologique localement convexe et complet [B, § 4.6, Proposition 9]." Here
  [B] is Bourbaki, *Espaces vectoriels topologiques*, ch. II. Waldspurger gives no proof.

The Lean proof below is the classical argument for the strict inductive limit of a
sequence of complete locally convex spaces, written out for `C(G)`. It does not rely on
the text of Bourbaki.

## Scope: generic weights and a countability hypothesis

As in `Basic`, `G` is an arbitrary topological group and `Ξ σ : G → ℝ` are arbitrary
weights. The results that need properties of the weights assume `Ξ > 0` and `σ ≥ 0`
(true for Waldspurger's weights by II.1 and I.1). No other property of `Ξ` or `σ` is
used.

The uniform structures are the canonical ones of the topological additive groups `C_K`
and `C(G)` (`IsTopologicalAddGroup.rightUniformSpace`, which for commutative groups is a
uniform additive group). Completeness is `CompleteSpace` for these structures.

The main theorem `Space.completeSpace` assumes that some sequence `H n` of compact open
subgroups is cofinal: every compact open subgroup contains some `H n`. Then, after
replacing `H n` by its running intersections, `C(G)` is the union of the increasing
sequence of levels `C_{H n}`, each carrying the subspace topology (`isInducing_ofLevel`).
The module does not prove that the topology of `C(G)` is the inductive-limit topology of
this sequence alone; the proof does not need it. For Waldspurger's `G` (the points of a
reductive group over a nonarchimedean local field) this holds because `G` is
nonarchimedean, locally compact and first countable;
`Space.completeSpace_of_firstCountable` records this case. These three properties of
Waldspurger's `G` are not proved here; they are hypotheses of that theorem. Waldspurger's remark in the
same paragraph that `C(G)` is not metrizable is not formalized.

## Definitions

- `Level.uniformSpace K`, `Space.uniformSpace`: the uniform structures above (instances),
  with `Level.isUniformAddGroup`, `Space.isUniformAddGroup`.
- `Level.evalLinear K g : C_K →ₗ[ℂ] ℂ`, `f ↦ f(g)`.
- `Space.SeminormTop q`, for a seminorm `q` on `C(G)`: an auxiliary copy of `C(G)` with
  the topology of the single seminorm `q`, with its instances
  (`IsTopologicalAddGroup`, `ContinuousSMul ℂ`, `LocallyConvexSpace ℝ`),
  `SeminormTop.ofSpace q` (the identity map from `C(G)`), `SeminormTop.seminorm q`,
  `SeminormTop.seminormFamily q` and `SeminormTop.withSeminorms q`. It is used only to
  apply III.6(1) in `continuous_seminorm_of_forall`.
- `Space.seminorm Ξ σ r : Seminorm ℂ (Space Ξ σ)`: Waldspurger's `ν_r` on `C(G)`,
  `f ↦ (nu Ξ σ r f).toReal`.
- `CompactOpenSubgroup.accumulate H n`: the running intersection `H 0 ∩ ⋯ ∩ H n` of a
  sequence of compact open subgroups (for `G` a topological group).

## Results

- `Level.completeSpace K hΞ hσ`: every level `C_K` is complete.
- `Space.continuous_seminorm_of_forall`: a seminorm `q` on `C(G)` is continuous if
  `q ∘ ofLevel K` is continuous on `C_K` for every compact open `K`.
- `Space.mem_nhds_zero_of_forall` (`G` a topological group with a compact open subgroup):
  a set `U ⊆ C(G)` that is balanced over `ℂ` and convex over `ℝ`, and whose trace
  `ofLevel K ⁻¹' U` is a neighborhood of `0` in `C_K` for every compact open `K`, is a
  neighborhood of `0` in `C(G)`.
- `Space.nu_lt_top`, `Space.nu_ne_top`: `ν_r(f) < ∞` for `f ∈ C(G)` and all `r`.
  `Space.seminorm_apply` gives the value of `Space.seminorm`.
- `Space.continuous_seminorm r`: `ν_r` is continuous on `C(G)`.
- `Space.comap_nhds_zero_le K`, `Space.isInducing_ofLevel K`: the inductive limit is
  strict. `C(G)` induces on `C_K` its own topology, i.e. the inclusion `C_K → C(G)` is an
  inducing map.
- `convex_balancedCore`: in a complex vector space, the `ℂ`-balanced core of an
  `ℝ`-convex set containing `0` is `ℝ`-convex.
- `CompactOpenSubgroup.accumulate_le` (`accumulate H n ≤ H n`) and
  `CompactOpenSubgroup.accumulate_antitone` (`m ≤ n → accumulate H n ≤ accumulate H m`).
- `exists_seq_compactOpenSubgroup_le` (`G` nonarchimedean, weakly locally compact, first
  countable): some sequence of compact open subgroups is cofinal.
- `Space.completeSpace hΞ hσ hH` (`G` a topological group, `hH` a cofinal sequence of
  compact open subgroups): **`C(G)` is complete** (III.6).
- `Space.completeSpace_of_firstCountable hΞ hσ` (`G` nonarchimedean, weakly locally
  compact, first countable): `C(G)` is complete.

## Proof notes

1. `Level.completeSpace`. Let `F` be a Cauchy filter on `C_K`. Evaluation at `g` is a
   continuous additive map (`Space.continuous_eval_level`), hence uniformly continuous,
   so its image of `F` converges in `ℂ` to a value `φ(g)`. For `r` and `ε > 0`, the
   Cauchy property gives `A ∈ F` with `ν_r(f' - f) < ε` for `f, f' ∈ A`. Letting `f'` tend
   to the limit along `F` in `|f(g) - f'(g)| w_r(g) ≤ ν_r(f - f')` gives
   `ν_r(f - φ) ≤ ε` for `f ∈ A`. Hence `φ` is `K`-bi-invariant (limit of bi-invariant
   functions), `ν_r(φ) ≤ ν_r(f) + ν_r(f - φ) < ∞`, so `φ ∈ C_K`, and `F` converges to `φ`
   in every `ν_r`, which is convergence in `C_K` (`WithSeminorms.tendsto_nhds`).
2. `continuous_seminorm_of_forall`. The identity `C(G) → SeminormTop q` is linear, and its
   restriction to each `C_K` is continuous because `q ∘ ofLevel K` is
   (`WithSeminorms.continuous_of_continuous_comp`). `SeminormTop q` is a locally convex
   complex topological vector space, so the identity is continuous by III.6(1), and
   `q` is the continuous seminorm of `SeminormTop q` composed with it.
3. `mem_nhds_zero_of_forall`. `0 ∈ U`, and `U` is absorbent over `ℝ`: each `x ∈ C(G)`
   lies in some `C_K`, where the trace of `U` is a neighborhood of `0`, hence absorbent.
   So the gauge `p` of `U` is a seminorm (`gaugeSeminorm`). On each `C_K`, `p ∘ ofLevel K`
   is at most `1` on the trace of `U`, a neighborhood of `0`; so it is continuous
   (`Seminorm.continuous'`). By step 2, `p` is continuous on `C(G)`, and the open set
   `{p < 1}` contains `0` and lies in `U` (`setOfPred_gauge_lt_one_subset_self`).
4. `nu_lt_top` follows by induction over the supremum of the levels. The restriction of
   `Space.seminorm Ξ σ r` to `C_K` is `Level.seminorm K r`, so step 2 gives
   `continuous_seminorm`. For strictness, a neighborhood of `0` in `C_K` contains a set
   `{f : ν_r(f) < ε for r ∈ s}` with `s` finite (`WithSeminorms.mem_nhds_iff`), which is
   the trace of `⋂_{r ∈ s} {ν_r < ε}`, a neighborhood of `0` in `C(G)`. With continuity
   of `ofLevel K` this gives `isInducing_ofLevel`
   (`IsTopologicalAddGroup.isInducing_iff_nhds_zero`).
5. `convex_balancedCore`. The balanced core of `s ∋ 0` is `⋂_{|c| ≥ 1} c • s`
   (`balancedCore_eq_iInter`), and each `c • s` is `ℝ`-convex because complex scalars
   commute with real ones.
6. `exists_seq_compactOpenSubgroup_le`. Take a decreasing countable basis `U n` of
   neighborhoods of `1` and, by `compactOpenSubgroupBasis`, compact open subgroups
   `H n ⊆ U n`. A compact open subgroup `K` is a neighborhood of `1`, so it contains some
   `U n ⊇ H n`.
7. `Space.completeSpace`. Replace the cofinal sequence by its running intersections, so
   that `E n = C_{H n}`, viewed as subspaces of `C(G)`, increase and every element of
   `C(G)` lies in some `E n`. Let `F` be a Cauchy filter on `C(G)` and let
   `F' = F + 𝓝 0`, the image of `F × 𝓝 0` under addition. It is Cauchy, and `F ≤ F'`.
   - Some `E n` meets every set of `F'`. Otherwise, for each `n` there are `A_n ∈ F`
     and a neighborhood `V_n` of `0` with `(A_n + V_n) ∩ E_n = ∅`. Shrink `V_n` to a
     neighborhood that is `ℂ`-balanced and `ℝ`-convex (the balanced core of a convex
     neighborhood, step 5), called `B_n`, and put `W_n = B_0 ∩ ⋯ ∩ B_n ⊆ V_n`, which
     decreases. Put
     `U = ⋂_N (E_N + W_N)`. It is balanced and convex. Its trace on `C_K` contains the
     trace of `W_m` when `H m ≤ K`: an element of `W_m ∩ C_K` lies in `E_N` for
     `N ≥ m` and in `W_m ⊆ W_N` for `N < m`. So `U` is a neighborhood of `0` by step 3.
     By the Cauchy property there is `C ∈ F` with `C - C ⊆ U`. Pick `a ∈ C`, say
     `a ∈ E_k`, and `y ∈ C ∩ A_k`. Then `a - y = e + v` with `e ∈ E_k`, `v ∈ W_k ⊆ V_k`,
     so `y + v = a - e ∈ E_k ∩ (A_k + V_k)`, a contradiction.
   - The trace of `F'` on `C_{H n}` (`comap (ofLevel (H n)) F'`) is therefore a proper
     filter. It is Cauchy because `ofLevel (H n)` is uniformly inducing (step 4 and
     `AddMonoidHom.isUniformInducing_of_isInducing`), so it converges to some `φ ∈ C_{H n}`
     by step 1. Then `φ` is a cluster point of the Cauchy filter `F'`, so `F'`, and hence
     `F ≤ F'`, converges to `φ` (`le_nhds_of_cauchy_adhp`).

## Not covered here

The non-metrizability of `C(G)` is not formalized. The inclusion and density of
`C_c^∞(G)` in `C(G)` are treated in `TestFunctions`, not here.
