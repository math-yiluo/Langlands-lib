# Proof of the Bruhat Haar measure statement

Authors: Worker 919, Worker 117.

This module proves `Langlands.Whittaker.bruhatHaarMeasure`, whose type is exactly the
published proposition `Langlands.Whittaker.BruhatHaarMeasureStatement.{uF}` from
`Langlands/Representation/Whittaker/BruhatHaarMeasureStatement.lean`. For every prime
`p`, every `F : PadicField.{uF} p` with its canonical norm topology and every `n`, it shows
that the actual upper unipotent group `U = upperUnipotent (n + 1) F.Carrier` with the Borel
sigma algebra has a Haar measure, and that every Haar measure on `U` is sigma finite, right
invariant and preserved by `weylTransposeUnipotent n F.Carrier`. For every permutation `w`,
the actual Bruhat fiber subgroup `P = permutationUnipotentPlus (n + 1) F.Carrier w` with its
Borel sigma algebra has a Haar measure, and every Haar measure on `P` is sigma finite and
right invariant. No regularity hypothesis on the Haar measures is used.

The proof route is not Shalika's; it uses Mathlib's uniqueness of Haar measure in second
countable groups (`MeasureTheory.Measure.isMulLeftInvariant_eq_smul`), which holds for all
left invariant measures finite on compacts, without regularity.

## Generic lemmas

Let `G` be a second countable, locally compact topological group with its Borel sigma
algebra.

- `isMulRightInvariant_of_compactOpenCover`: if every `g : G` lies in a compact open
  subgroup, every Haar measure `μ` on `G` is right invariant. For fixed `g`, the pushforward
  of `μ` under `x ↦ x * g` is left invariant and finite on compacts, so it equals
  `c • μ` with `c = haarScalarFactor`. Take a compact open subgroup `K` containing `g`;
  its preimage under right multiplication by `g` is `K` itself. Evaluating both measures on
  `K` gives `μ K = c * μ K`, and `μ K` is nonzero (open, nonempty) and finite (compact), so
  `c = 1`.
- `map_eq_self_of_antiInvolution`: if `τ : G ≃ₜ G` satisfies `τ (x * y) = τ y * τ x` and
  `τ (τ x) = x`, then `Measure.map τ μ = μ` for every right invariant Haar measure `μ`.
  The pushforward `map τ μ` is left invariant, since left translation by `g` after `τ` is
  `τ` after right translation by `τ g`, and `μ` is right invariant. It is finite on compacts
  and positive on open sets, so `map τ μ = c • μ`. Applying `τ` again and using `τ ∘ τ = id`
  gives `μ = c ^ 2 • μ`. Evaluating on a positive compact set (finite, nonzero measure)
  gives `c ^ 2 = 1`, so `c = 1` because squaring is strictly monotone on `ℝ≥0∞`.
- `compactOpenCover_of_le`: if `H ≤ H'` are subgroups of a topological group, `H` is
  closed, and every element of `H'` lies in a compact open subgroup of `H'`, then every
  element of `H` lies in a compact open subgroup of `H`. The inclusion `H → H'` is a
  closed embedding (its composite with the subtype map of `H'` is the closed embedding of
  `H`), so the preimage `OpenSubgroup.comap` of a compact open subgroup of `H'` is a compact
  open subgroup of `H`.

## Main theorem

After introducing `p`, `F`, `n` and `U`, the proof installs the canonical normed field
structure, the valuative relation and nonarchimedean local field structure from
`F.canonicalTopologicalData` (whose topology is the canonical norm topology), and the Borel
sigma algebra on `U`. The general linear group is locally compact
(`PadicField.TopologicalData.generalLinearLocallyCompactSpace`) and second countable
(`PadicField.TopologicalData.generalLinearSecondCountableTopology`). Since `U` is closed
(`UpperUnipotent.isClosed`), it is locally compact, and it is second countable as a
subspace.

- Existence on `U`: Mathlib's `Measure.haar`.
- Sigma finiteness: instance inference from the Haar measure on a second countable locally
  compact space.
- Right invariance on `U`: `RankinSelberg.unipotent_exists_compact_open` places every
  element of `U` in a compact open subgroup; apply `isMulRightInvariant_of_compactOpenCover`.
- Transpose invariance: apply `map_eq_self_of_antiInvolution` to
  `weylTransposeUnipotent n F.Carrier`, with the anti-multiplicativity from
  `weylTransposeHomeomorph_mul` and the involution property
  `weylTransposeUnipotent_involutive`.
- Fiber clauses: for `w`, the subgroup `P` is closed (`isClosed_permutationUnipotentPlus`)
  and contained in `U` (`permutationUnipotentPlus_le_upperUnipotent`), hence locally compact
  and second countable. `compactOpenCover_of_le` transfers the compact open cover of `U` to
  `P`; existence is `Measure.haar`, sigma finiteness is inferred, and right invariance is
  `isMulRightInvariant_of_compactOpenCover`.

## Credits

Worker 117 independently proved the fiber clause in a shared draft (via the same compact
open cover pulled back along the closed inclusion `P → U`) and supplied the elaboration
details for the canonical local field structure used here.

## Checks

`lean_check` with Lake build: 0 errors, 0 warnings; axioms `propext`, `Classical.choice`,
`Quot.sound`; universe parameter `uF`.
