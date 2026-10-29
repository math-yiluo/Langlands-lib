# Proof: the Haar modulus of a refined product-Levi radical

Author: Worker 799.

This module proves the published proposition
`Langlands.Geometric.PadicRefinedUnipotentHaarModulus.{uF}` of
`Representation/Geometric/RefinedUnipotentHaarStatement`. The closing theorem is

`Langlands.Geometric.padicRefinedUnipotentHaarModulus :
  PadicRefinedUnipotentHaarModulus.{uF}`.

It is unapplied, has the single universe `uF`, and uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`. The statement's Lean/Markdown
pair and everything it imports are unchanged.

## What is proved

The theorem keeps every quantifier of the statement:

- every prime `p`, every p-adic field `F : PadicField.{uF} p` and every
  supplied realization `T : F.TopologicalData`, with exactly the topology
  `T.topology`;
- every rank `n`, including `n = 0`, every ordered block shape
  `B : GeneralLinear.BlockShape n`, and every refinement
  `S : Geometric.BlockRefinement B`. Here `S i` is an arbitrary ordered block
  shape of the `i`-th block of `B`. There is no minimality, properness,
  admissibility, representation or rank hypothesis.

The groups are the published ones, inside `G = B.Levi F.Carrier`, the product
of the groups `GL_{n_i}(F)`:

- `U = Geometric.refinedUnipotent F.Carrier B S`, the subgroup of `G` whose
  `i`-th component lies in the strictly upper block unipotent subgroup of
  `S i`, with the subspace topology;
- `M = Geometric.refinedLevi F.Carrier B S`, the subgroup of `G` whose `i`-th
  component lies in the block-diagonal Levi subgroup of `S i`;
- `Geometric.refinedLeviNormalizer F.Carrier B S : M →* normalizer U`, which
  keeps the underlying element.

For `m : M` write `a_m = HaarModulus.normalizerConj U
(refinedLeviNormalizer F.Carrier B S m)`. This is conjugation `u ↦ m u m⁻¹`
on `U`. Write `c(m) = T.refinedLeviModulus B S m`. The statement installs
`T.topology`, `T.leviTopologicalGroup B` and the published helper
`T.refinedUnipotentLocallyCompactSpace B S`. Under these instances the theorem
proves both parts.

1. **Measure law.** For every `m : M`, every measurable structure on `U` that
   is its Borel σ-algebra, and every measure `μ` on `U` with
   `μ.IsHaarMeasure`:
   `μ.map a_m = (c(m) : ℝ≥0)⁻¹ • μ`.
   The measure `μ` is arbitrary. It is not assumed regular, normalized or of
   product form.
2. **Character equality.** As homomorphisms `M →* ℝ≥0ˣ`:
   `(HaarModulus.normalizerCharacter U).comp (refinedLeviNormalizer F.Carrier B S)
     = T.refinedLeviModulus B S`.
   This is the published actual character. It is built from Mathlib's
   `mulEquivHaarChar` with the canonical Borel structure `borel U`.

## Proof of part 1

The proof follows the plan recorded in the statement's Markdown.

**Instances from the actual topology.** The proof installs the field
instances `T.valuativeRel` and `T.localField`. With them `F.Carrier` is a
topological ring, which the continuity of the block actions needs. Second countability comes from the published
`T.generalLinearSecondCountableTopology k` for every `k`. It passes to the
finite product `B.Levi F.Carrier`. It then passes to the subspaces `U`,
`(S i).parabolic F.Carrier` and `(S i).unipotentRadical F.Carrier`, by
`Topology.IsEmbedding.subtypeVal.secondCountableTopology`. Each block radical
`P_i = (S i).unipotentRadical F.Carrier` is a topological group by
`T.unipotentRadicalTopologicalGroup (S i)` and locally compact by
`T.unipotentRadicalLocallyCompactSpace (S i)`. Nothing here is a hypothesis;
each fact is a published theorem about the actual p-adic topology.

**Borel structures.** The supplied measurable structure on `U` equals
`borel U` by `BorelSpace.measurable_eq`, and the proof substitutes it. Each
`P_i` gets its Borel σ-algebra. The product `∀ i, P_i` then carries a Borel
product σ-algebra, by `Pi.borelSpace`; this uses second countability of the
factors.

**Block laws.** Let `ν_i = haar` be Mathlib's Haar measure on `P_i`, and let
`m_i = PadicField.TopologicalData.refinedLeviBlock B S i m`. The published
`Langlands.glBlockModulusHaar` of `Group/GL/BlockModulusHaarProof`, applied to
`p, F, T`, the shape `S i`, the measure `ν_i` and `m_i`, gives

`ν_i.map ((S i).leviAction F.Carrier m_i) = (T.leviModulus (S i) m_i)⁻¹ • ν_i`.

**Finite-product scaling.** Let `Φ` be the coordinatewise map
`x ↦ (i ↦ (S i).leviAction F.Carrier m_i (x i))` on `∀ i, P_i`. Each
coordinate action is continuous, by `(S i).continuous_leviAction`, so it is
measurable. Mathlib's `Measure.pi_map_pi` and the block laws give
`(Measure.pi ν).map Φ = Measure.pi (i ↦ (T.leviModulus (S i) m_i)⁻¹ • ν_i)`.
The published `HarmonicAnalysis.pi_nnreal_smul` pulls the scalars out as a
product. By `T.refinedLeviModulus_apply B S`, `Units.coe_prod` and
`Finset.prod_inv_distrib`, that product is `(c(m) : ℝ≥0)⁻¹`. Hence

`(Measure.pi ν).map Φ = (c(m))⁻¹ • Measure.pi ν`.

**Coordinate conjugacy.** Let `e = Geometric.refinedUnipotentRadicalEquiv B S
F.Carrier : U ≃ₜ* ∀ i, P_i`, the published continuous group isomorphism. The
proof shows `a_m ∘ e.symm = e.symm ∘ Φ`. After applying `e`, it compares the
`i`-th coordinates as matrices in `GL_{n_i}(F)`. The left side is
`m_i' · x_i · m_i'⁻¹`, where `m_i'` is the `i`-th component of `m` in `G`.
The right side is the block Levi conjugation,
`leviEmbedding (S i) m_i · x_i · (leviEmbedding (S i) m_i)⁻¹`. The two agree
because `leviEmbedding (S i) m_i = m_i'`. This holds since
`refinedLeviBlock B S i m` is the inverse of `(S i).leviEquiv F.Carrier`
applied to the `i`-th component (`MulEquiv.apply_symm_apply`).

**A reference Haar measure on `U`.** Let `ρ = (Measure.pi ν).map e.symm`. It is
a Haar measure on `U`, by Mathlib's `ContinuousMulEquiv.isHaarMeasure_map` and
the Haar property of `Measure.pi ν` (`Measure.pi.isHaarMeasure`). Then
`ρ.map a_m = (c(m))⁻¹ • ρ`. The proof rewrites with `Measure.map_map`, the
coordinate conjugacy, the product scaling and `Measure.map_smul`.

**Every Haar measure.** `U` is locally compact (the helper) and second
countable (above). So Mathlib's uniqueness theorem
`MeasureTheory.Measure.isMulLeftInvariant_eq_smul` gives `μ = κ • ρ` for the
scalar `κ = haarScalarFactor μ ρ`. Regularity is not assumed: this theorem
derives it from second countability. Then
`μ.map a_m = κ • ρ.map a_m = κ • (c(m))⁻¹ • ρ = (c(m))⁻¹ • μ`.

## Proof of part 2

Both sides are homomorphisms into `ℝ≥0ˣ`, so it suffices to compare values in
`ℝ≥0` at each `m : M`. Equip `U` with `borel U`, which is the measurable
structure used inside `normalizerCharacter`. Choose a positive compact set
`K₀` of `U`, which exists because `U` is locally compact and nonempty. Let
`μ = haarMeasure K₀`. It is a regular Haar measure with `μ K₀ = 1`.

Write `χ(m)` for `normalizerCharacter U (refinedLeviNormalizer F.Carrier B S m)`
in `ℝ≥0`. The published `HaarModulus.normalizerCharacter_smul_map` gives
`χ(m) • μ.map a_m = μ`. Part 1 for this `μ` gives `μ.map a_m = (c(m))⁻¹ • μ`.
So `(χ(m) · c(m)⁻¹) • μ = μ`. Evaluating at `K₀` gives
`χ(m) · c(m)⁻¹ = 1`. Since `c(m)` is a unit, it is nonzero, and
`mul_inv_eq_one₀` gives `χ(m) = c(m)`.

## Direction and source

I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472. Registered source
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. The PDF
page is the printed page minus 439.

- **Section 1.7, printed page 444.** For an automorphism `σ` of an l-group `U`
  and a Haar measure `μ`, the module is defined by
  `∫_U f(σ⁻¹(u)) dμ(u) = mod_U σ · ∫_U f(u) dμ(u)`. For `g` normalizing `U`,
  `mod_U(g)` is the module of `u ↦ g u g⁻¹`. The left side is the integral of
  `f` against the image measure `(σ⁻¹)_* μ`. So `(σ⁻¹)_* μ = mod_U(σ) μ`, that
  is, `σ_* μ = mod_U(σ)⁻¹ μ`: the forward pushforward has the inverse scalar.
  With `σ = a_m`, part 1 says `mod_U(m) = c(m)`, and part 2 says the same for
  the Library's packaged character. Its convention is
  `χ(m) • μ.map a_m = μ`, so `χ(m) = mod_U(m)`.
- **Sections 2.1–2.2, printed page 446.** Parabolic triples `(P, M, U)` with
  `P = MU`. For `GL(n, F)` the standard subgroups correspond to ordered
  partitions, and `G_β < G_α` exactly when `β` is a subpartition of `α`. A
  refinement `S` of `B` is such a subpartition. The refined parabolic, refined
  Levi `M` and refined radical `U` in `B.Levi F` form the corresponding
  parabolic triple, built block by block.
- **Section 6.3, printed page 468.** The intersections
  `(M ∩ w⁻¹(Q), M ∩ w⁻¹(N), M ∩ w⁻¹(V))` form a parabolic triple in `M`. This
  is the downstream motivation only.

There is no project errata note for this source.

## Provenance

The result is an internal finite-product consequence of the standard block
Haar law `Langlands.glBlockModulusHaar`, read with the BZ77 section 1.7
convention. It is not a named theorem of the source. The proof route is the
one described above, not a route from the source.

## Not claimed

The module proves nothing about intersection subgroups `M ∩ w⁻¹(V)`. It does
not prove the actual-intersection Haar-character bridge, quotient integrals,
or the full normalized orbit comparison of the geometric lemma. Those are
separate obligations.
