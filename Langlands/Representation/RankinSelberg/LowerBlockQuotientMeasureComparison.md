# Lower-block comparison of quotient measures

Author: Worker 234 (shape requested by Worker 936 for task 7b088130).

This module proves that every compatible quotient measure on
`N_{a+d} \ GL_{a+d}` is a positive multiple of the pushforward, along the
published lower-block chart

`([g], x, h) ↦ [[[g, 0], [x, h]]]`,

of the product `D μ_a × dx × ρ`. Here `μ_a` is any compatible quotient measure
on `N_a \ GL_a`, `D [g] = |det g|^(-d)` is the published determinant density,
`dx` is the rectangular Haar measure on `d × a` matrices and `ρ` is a nonzero
right-invariant measure on the lower triangular group `B̄_d`. The constant is a
real number `C > 0` and is not computed.

All declarations are in the namespace `Langlands.RankinSelberg`. Neither
theorem introduces a new definition.

## Provenance

Internal (derived infrastructure). It supports the proof of the published
proposition `LowerBlockQuotientDisintegrationStatement`, whose source is
H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
convolutions*, Amer. J. Math. 105 (1983), section 9.3, printed pp. 456-457.
There an integral over `N_{a+d} \ GL_{a+d}` is rewritten in the coordinates
`[[g, 0], [x, h]]` with `g ∈ N_a \ GL_a`, `x` a `d × a` matrix and `h` lower
triangular, with measure `dg d_r(h) dx` and "up to a positive constant
factor". As the Markdown of the target statement explains, comparing the
`|det g|` exponents shows that the change of variables is
`dg' = |det g|^(-d) dg dx d_r(h)` up to that constant. The source states no
lemma of this form. This module proves the
measure identity behind that change of variables: the two measures agree up to
a positive constant. The route below (open lower triangular cell, block
coordinates, uniqueness of right Haar measure) is our own and is not taken
from the source.

## Conventions

- `T : F.TopologicalData` supplies the topology `T.topology` on the p-adic
  field `F.Carrier`. Every space carries the Borel σ-algebra of its topology,
  installed by `letI` inside each statement, as in the target proposition.
- `LeftQuotient (upperUnipotent m F.Carrier)` is the published left coset
  space `N_m \ GL_m`. `lowerTriangularSubgroup m F.Carrier` is the published
  group `B̄_m` of invertible lower triangular matrices, with the subspace
  topology.
- `lowerTriangularQuotientMap m F.Carrier` is the published open cell
  `β_m : B̄_m → N_m \ GL_m`, `b ↦ [b]`.
- `IsCompatible (upperUnipotent m F.Carrier) μG μH μ` is the published
  compatibility of a quotient measure `μ` with Haar measures `μG` on `GL_m`
  and `μH` on `N_m`. Its fields include `nonzero`, `regular` and
  `right_invariant` (invariance under every right translation `[k] ↦ [k g]`).
- `lowerBlockQuotientChart` is the published chart above, on
  `LeftQuotient (upperUnipotent a F.Carrier) × Matrix (Fin d) (Fin a) F.Carrier
  × lowerTriangularSubgroup d F.Carrier`.
- `lowerBlockQuotientDensity T a d` is the published density
  `[g] ↦ |det g|^(-d)` on `N_a \ GL_a`, with the residue-normalized absolute
  value of `T`. `rectangularMeasure η d a` is the published product of the
  additive Haar measure `η` over the `d · a` entries.

## Theorems

### `lowerTriangularQuotientMap_comap_of_isCompatible`

For every `m`, regular Haar measures `μG` on `GL_m` and `μH` on `N_m` with
`μH` right invariant, and every quotient measure `μ` on `N_m \ GL_m` with
`IsCompatible (upperUnipotent m F.Carrier) μG μH μ`, the measure
`ρ := μ.comap β_m` on `B̄_m` satisfies:

- `ρ.IsMulRightInvariant`;
- `IsFiniteMeasureOnCompacts ρ`;
- `SigmaFinite ρ`;
- `ρ ≠ 0`;
- `ρ.map β_m = μ`.

Proof. Right invariance, finiteness on compacts and the conditional
pushforward identity are `comap_lowerTriangularQuotientMap_properties` from
`LowerTriangularQuotientCellMeasure`, fed with the `regular` and
`right_invariant` fields of `IsCompatible`. Its hypothesis
`μ (range β_m)ᶜ = 0` is `padic_lowerTriangular_leftQuotient_conull` from
`LowerTriangularBigCellConull`, after rewriting the complement of the range as
the set of cosets with no representative in `B̄_m`. σ-finiteness follows from
finiteness on compacts, because `B̄_m` is closed in `GL_m`
(`lowerTriangularSubgroup_isClosed`) and hence locally compact and second
countable. Finally, if `ρ = 0` then `μ = ρ.map β_m = 0`, which contradicts the
`nonzero` field.

### `lowerBlockQuotient_eq_smul_map_chart`

For every `a d : ℕ`, take:

- an additive Haar measure `η` on `F.Carrier`;
- regular Haar measures `μGa` on `GL_a` and `μHa` on `N_a`, with `μHa` right
  invariant;
- regular Haar measures `μGad` on `GL_{a+d}` and `μHad` on `N_{a+d}`, with
  `μHad` right invariant;
- quotient measures `μa` on `N_a \ GL_a` and `μad` on `N_{a+d} \ GL_{a+d}`
  with `IsCompatible (upperUnipotent a F.Carrier) μGa μHa μa` and
  `IsCompatible (upperUnipotent (a + d) F.Carrier) μGad μHad μad`;
- a measure `ρ` on `B̄_d` that is σ-finite, finite on compacts, right
  invariant and nonzero.

Then there is a real `C > 0` with

`μad = ENNReal.ofReal C • map lowerBlockQuotientChart
  ((μa.withDensity (lowerBlockQuotientDensity T a d)).prod
    ((rectangularMeasure η d a).prod ρ))`.

Proof.

1. Apply the first theorem to `μa` and to `μad`. This gives right-invariant,
   nonzero measures `ρa := μa.comap β_a` on `B̄_a` and
   `ρad := μad.comap β_{a+d}` on `B̄_{a+d}`, finite on compacts, with
   `ρa.map β_a = μa` and `ρad.map β_{a+d} = μad`.
2. Let `w = lowerTriangularBlockDensity T a d`, the density
   `b ↦ |det b|^(-d)` on `B̄_a`. It is `lowerBlockQuotientDensity T a d ∘ β_a`
   by definition, so `μa.withDensity (lowerBlockQuotientDensity T a d)` is
   the pushforward of `ρa.withDensity w` along `β_a` (`setLIntegral_map`).
3. Let `θ = lowerTriangularBlockMap a d F.Carrier`, the block-coordinate map
   `(b, x, h) ↦ [[b, 0], [x, h]]` from `B̄_a × M_{d×a} × B̄_d` to
   `B̄_{a+d}`. The chart applied to `(β_a b, x, h)` is `β_{a+d} (θ (b, x, h))`
   by definition. With `P := (ρa.withDensity w).prod (dx.prod ρ)` and
   `map_prod_map`, the measure on the right-hand side, without `C`, equals
   `(P.map θ).map β_{a+d}`.
4. `P.map θ` is right invariant. Every element of `B̄_{a+d}` is `θ (g, y, h)`
   for some `g`, `y`, `h`, because `θ` is an equivalence
   (`lowerTriangularBlockEquiv`). By `lowerTriangularBlockMap_mul`, right
   multiplication by `θ (g, y, h)` becomes
   `(b, x, h') ↦ (b g, x g + h' y, h' h)` in block coordinates. The published
   `measurePreserving_lowerBlockWeightedProduct_mulRight` says this map
   preserves `P`.
5. `P.map θ` is finite on compacts: `θ` is a homeomorphism
   (`lowerTriangularBlockHomeomorph`), so the preimage of a compact set is
   compact. `P` is locally finite there because `w` is continuous and finite
   (`IsLocallyFiniteMeasure.withDensity_coe`), and `dx` and `ρ` are locally
   finite.
6. `P.map θ` is nonzero. The density `w` never vanishes, so
   `ρa.withDensity w ≠ 0`. The measure `dx` gives positive mass to the open
   set `univ`. `ρ ≠ 0` by hypothesis. The product of three nonzero measures
   gives positive mass to `univ ×ˢ univ ×ˢ univ`.
7. Uniqueness of right-invariant measures on `B̄_{a+d}`
   (`exists_pos_smul_eq_of_isMulRightInvariant` from
   `LowerTriangularQuotientCellMeasure`) gives `C > 0` with
   `ρad = ENNReal.ofReal C • P.map θ`. Push forward along `β_{a+d}`; scalars
   commute with `map` (`Measure.map_smul`), and `ρad.map β_{a+d} = μad`.

## Dependencies

- Library: `LowerBlockQuotientDisintegrationStatement` (density and its
  measurability), `LowerBlockQuotientCoordinates` (chart and its
  continuity), `LowerBlockQuotientMeasureSupport`
  (`lowerTriangularSubgroup_isClosed`), `LowerBlockWeightedProductInvariance`
  (weighted density and right invariance of the weighted product),
  `LowerTriangularQuotientCell` (the open cell `β_m`).
- Candidate modules of task 7b088130: `LowerTriangularBlockCoordinates` and
  `LowerTriangularQuotientCellMeasure` (Worker 936). Candidate module of task
  2940cb7d: `LowerTriangularBigCellConull` (Worker 234).
