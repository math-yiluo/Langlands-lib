# Exchanging two Iwasawa integrals of a Levi-invariant function

Worker 5. Supporting module for the proof of
`Langlands.Plancherel.ConditionalDynamicOppositeHermitianAdjunctionStatement`
(module `DynamicOppositeHermitianAdjunctionProof`). It is generic: it works in
an arbitrary topological group and mentions no group scheme. Namespace
`Langlands.Plancherel.LeviInvariantIwasawaExchange`.

## Setting

`G` is a second countable topological group with its Borel σ-algebra. `M`, `U`,
`V` are subgroups of `G`, and `M` normalizes `U` and `V`
(`M ≤ normalizer U`, `M ≤ normalizer V`). `K` is an open subgroup. The
hypotheses on `K` are:

- factorizations `G = M U K` and `G = M V K` (`hfacU`, `hfacV`: every `g` is
  `m u k`, resp. `m v k`, with `k ∈ K`);
- splittings `m u ∈ K ↔ m ∈ K ∧ u ∈ K` and `m v ∈ K ↔ m ∈ K ∧ v ∈ K`
  (`hsplitU`, `hsplitV`).

The measures are: an s-finite left-invariant measure `μ` on `G`; an s-finite
measure `μM` on `M` that is invariant under both left and right translations,
with `μM(M ∩ K) = 1`; s-finite left-invariant measures `μU`, `μV` with
`μU(U ∩ K) = μV(V ∩ K) = 1`. `U` and `V` are second countable. The Borel
structures on `M`, `U`, `V` are arbitrary `BorelSpace` instances.

## Results

**Iwasawa formula** (section `Iwasawa`).

- `measurePreserving_shift`: in the coordinates `(m, w) ∈ M × W`, left
  translation of `M W` by an element of `M W` preserves `μM × μW`.
- `lintegral_eq_iwasawa`: for a measurable `F : G → [0, ∞]`,
  `∫_G F dμ = ∫_K ∫_M ∫_W F(m w k) dμW dμM dμ`, under `G = M W K`,
  `m w ∈ K ↔ m ∈ K ∧ w ∈ K` and `μM(M ∩ K) = μW(W ∩ K) = 1`. The proof is the
  proof of the Library's `HarishChandraSchwartz.lintegral_eq_lintegral_levi_unipotent`
  (module `HarmonicAnalysis.HarishChandraSchwartz.IwasawaIntegration`), repeated
  for arbitrary Borel structures on `M` and `W`. It applies
  `CompactFactorization.lintegral_restrict_lintegral_mul` to the coordinates
  `(m, w) ↦ m w`. The splitting identifies the preimage of `K` with
  `(M ∩ K) × (W ∩ K)`, of mass `1`.

**Cutoffs** (section `Cutoff`). `cutoffSet W K = W K` and
`cutoff W K = 1_{W K}`.

- `mem_cutoffSet_iff`, `cutoff_mul`: for `k ∈ K`, `m w k ∈ W K ↔ m ∈ K`, so
  `1_{W K}(m w k) = 1_{M ∩ K}(m)`. Only the normalizing property and the
  splitting are used.
- `isOpen_cutoffSet`, `measurable_cutoff`, `measurableSet_leviCompact`.
- `lintegral_cutoff_mul`: for measurable `Θ ≥ 0` with `Θ(m g) = Θ(g)` for
  `m ∈ M`, `∫_G 1_{W K} Θ dμ = ∫_K ∫_W Θ(w k) dμW dμ`. This is the Iwasawa
  formula with `F = 1_{W K} Θ` followed by `cutoff_mul`, `M`-invariance and
  `μM(M ∩ K) = 1`.
- `lintegral_cutoff_inv_mul`: `∫_M 1_{W K}(m⁻¹ g) dμM(m) = 1` for every `g`.
  It uses left invariance of `μM`.
- `lintegral_cutoff_mul_left`: `∫_M 1_{W K}(m g) dμM(m) = 1` for every `g`.
  It uses right invariance of `μM`.

**Exchange** (section `Exchange`).

- `lintegral_cutoff_exchange`: for `Θ ≥ 0` measurable and left
  `M`-invariant, `∫_G 1_{V K} Θ dμ = ∫_G 1_{U K} Θ dμ`. The proof inserts
  `∫_M 1_{U K}(m⁻¹ g) dm = 1`, exchanges the integrals over `G` and `M`
  (Tonelli), substitutes `g ↦ m g` (left invariance of `μ`), uses
  `Θ(m g) = Θ(g)`, exchanges back and evaluates `∫_M 1_{V K}(m g) dm = 1`.
- `lintegral_exchange`: for the same `Θ`,
  `∫_K ∫_V Θ(v k) dμV dμ = ∫_K ∫_U Θ(u k) dμU dμ`, by `lintegral_cutoff_mul`
  for `V` and for `U`, and `lintegral_cutoff_exchange`.

**Complex form** (section `Complex`).

- `LeviQuotient M` is the orbit space `M \ G` of left translations by `M`
  (`Quotient (QuotientGroup.rightRel M)`) with Mathlib's quotient σ-algebra. No
  topology on it is used. `leviQuotientMk`, `leviQuotientMk_mul`,
  `measurable_leviQuotientMk`, `leviQuotientLift` (a left `M`-invariant
  function as a function on `M \ G`), `leviQuotientLift_mk`,
  `measurable_leviQuotientLift`.
- `iwasawaPush M μ K μW` is the image of `μ|_K × μW` under
  `(k, w) ↦ M w k ∈ M \ G`; `measurable_iwasawaCoordinates`.
- `iwasawaPush_eq`: `iwasawaPush M μ K μV = iwasawaPush M μ K μU`. It is
  `lintegral_exchange` applied to `Θ = f ∘ leviQuotientMk` for measurable
  `f ≥ 0` on `M \ G`.
- `integral_exchange`: let `Θ : G → ℂ` be measurable and left `M`-invariant,
  and let `(k, v) ↦ Θ(v k)` be integrable on `K × V` for `μ|_K × μV`. Then
  `(k, u) ↦ Θ(u k)` is integrable on `K × U` and
  `∫_K ∫_V Θ(v k) dμV dμ = ∫_K ∫_U Θ(u k) dμU dμ`. Both sides are integrals of
  the lift of `Θ` against the two equal pushforwards (`integral_map` and
  Fubini, `integral_prod`). Integrability transfers the same way
  (`integrable_map_measure`).

**Integrability** (section `Integrability`).

- `continuous_of_mul_right_invariant`: a function invariant under right
  translation by an open subgroup is continuous.
- `integrable_iwasawaCoordinates`: let `K` be compact open, `μ` finite on
  compact sets and `μW` s-finite. Let `Θ : G → ℂ` be invariant under right
  translation by an open subgroup, with `w ↦ Θ(w k)` integrable for every
  `k ∈ K`. Then `(k, w) ↦ Θ(w k)` is integrable on `K × W`. The function
  `k ↦ ∫_W ‖Θ(w k)‖` is invariant under the same right translations, so it is
  continuous and hence integrable on the compact `K`
  (`integrable_prod_iff`).

## Source and provenance

`lintegral_eq_iwasawa` is a form of the first integration formula of
J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
I.1 (2), printed p.240 (registered `waldspurger-2003-plancherel`). There,
`∫_G f(g) dg = ∫_{U×M×K} f(umk) δ_P(m)⁻¹ dk dm du`, with Haar measures giving
`H ∩ K` mass one. Here the coordinates are ordered `m w k`, so no modulus
appears. In Waldspurger the normalization `mes(H ∩ K) = 1` is consistent with
the formula because his `K` is in good position, so `K ∩ P = (K ∩ M)(K ∩ U)`.
This module assumes the splitting `m w ∈ K ↔ m ∈ K ∧ w ∈ K` instead.

The exchange identity is an internal lemma. Waldspurger states IV.1 (11)
without proof. The cutoff argument (average of `1_{V K}` over `M`) is the
route suggested in the context of Task 6449. The cutoffs make the integrals
over `G` usable: a left `M`-invariant `Θ` is in general not integrable over
`G`. All results hold for an arbitrary universe of `G`.

## Axioms

No `sorry` and no new axioms. The main theorem that uses this module depends
only on `propext`, `Classical.choice` and `Quot.sound`.
