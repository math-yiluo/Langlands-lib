# Quotient measures on the open lower-triangular cell

Author: Worker 936.

This module relates measures on the left coset space `N_m \ GL_m` to right
Haar measures on the group `B̄_m` of invertible lower triangular matrices,
through the open cell `β_m : B̄_m → N_m \ GL_m`, `b ↦ [b]`. It proves:

1. Uniqueness of right-invariant measures. On a second countable, locally
   compact topological group, two nonzero right-invariant measures that are
   finite on compacts differ by a positive real factor.
2. A right-invariant quotient measure `μ` that is finite on compacts pulls
   back to a right-invariant measure `comap β_m μ` on `B̄_m` that is finite on
   compacts. If the range of `β_m` is `μ`-conull, then
   `map β_m (comap β_m μ) = μ`.

All declarations are in the namespace `Langlands.RankinSelberg`.

## Provenance

Internal (derived infrastructure). It supports the proof of the published
proposition `LowerBlockQuotientDisintegrationStatement`, whose source is
H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
convolutions*, Amer. J. Math. 105 (1983), section 9.3. There the measure on
`N_{a+d} \ GL_{a+d}` is computed in lower-block coordinates. Here such
quotient measures are reduced to right Haar measures on `B̄_m`. The source
states no lemma of this form. Item 1 is the standard uniqueness of Haar
measure, transported from left to right invariance by inversion. Item 2 is
elementary measure theory for an open embedding.

## Conventions

- `lowerTriangularQuotientMap m F.Carrier` is the published open cell map
  `β_m` from `Langlands.Group.GL.LowerTriangularQuotientCell`. Its openness is
  the published `isOpenEmbedding_lowerTriangularQuotientMap T m`.
- `LeftQuotient H` is the published left coset space `H \ G` with the
  quotient topology. `rightTranslate H g` is the published right action
  `[k] ↦ [k g]`.
- The topology is `T.topology` from a p-adic field's `F.TopologicalData`.
  `B̄_m` carries the subspace topology and the Borel σ-algebra
  `borel (lowerTriangularSubgroup m F.Carrier)`. The quotient carries
  `borel (LeftQuotient (upperUnipotent m F.Carrier))`. These are installed by
  `letI` inside each statement, as in the target proposition.

## Theorems

- `exists_pos_smul_eq_of_isMulRightInvariant ρ₁ ρ₂`: for a group `G` with
  `[IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [BorelSpace G]`, take measures `ρ₁ ρ₂` with `IsFiniteMeasureOnCompacts` and
  `IsMulRightInvariant`, both nonzero. Then there is a real `C > 0` with
  `ρ₁ = ENNReal.ofReal C • ρ₂`. Proof: the inverse measures `ρᵢ.inv` are left
  invariant and finite on compacts, so `isMulLeftInvariant_eq_smul` gives
  `ρᵢ.inv = cᵢ • haar` with `cᵢ = haarScalarFactor ρᵢ.inv haar`. Each `cᵢ`
  is nonzero because `ρᵢ ≠ 0`, and `ρᵢ = ρᵢ.inv.inv`. Take `C = c₁ / c₂`.
- `lowerTriangularQuotientMap_mul T m b c`:
  `β_m (b c) = rightTranslate _ c.val (β_m b)`, by `rfl`.
- `lowerTriangularQuotientMap_measurableEmbedding T m`: `β_m` is a measurable
  embedding for the Borel σ-algebras, because it is an open embedding
  (`Topology.IsOpenEmbedding.measurableEmbedding`).
- `comap_lowerTriangularQuotientMap_properties T m μ hfin hinv`: let
  `μ` be a measure on `N_m \ GL_m` with `IsFiniteMeasureOnCompacts μ` and
  `MeasurePreserving (rightTranslate _ g) μ μ` for every `g`. Put
  `ρ := μ.comap β_m`. Then:
  - `ρ.IsMulRightInvariant`. Proof: for measurable `S`, `β_m` maps the
    preimage `S c⁻¹` onto the preimage of `β_m S` under `rightTranslate _ c`,
    by `lowerTriangularQuotientMap_mul`. Right-translation invariance of `μ`
    then gives `ρ (S c⁻¹) = ρ S`.
  - `IsFiniteMeasureOnCompacts ρ`. Proof: `ρ K = μ (β_m K)`, and `β_m K` is
    compact.
  - If `μ (range β_m)ᶜ = 0`, then `ρ.map β_m = μ`. Proof:
    `MeasurableEmbedding.map_comap` gives `μ.restrict (range β_m)`, which is
    `μ` because the range is conull.

The compatibility certificate `IsCompatible` of the target proposition
supplies the right-translation invariance hypothesis (its `right_invariant`
field). Its `regular` field supplies finiteness on compacts.
