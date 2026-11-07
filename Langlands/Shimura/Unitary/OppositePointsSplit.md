# The splitting of the opposite finite adelic points at the places dividing an integer

This internal construction passes the published splitting of finite adelic
points at the places dividing an integer (`Langlands.Shimura.Unitary.PointsSplit`)
to the opposite groups. The opposite groups are the ones used for the levels
of the published CM towers. It also gives a condition on a level `K₀` at the
places dividing the integer that makes every level `e⁻¹ (K₀ × K')`
sufficiently small, in the sense of the published
`Langlands.Shimura.Unitary.SufficientlySmallLevels`.

## Motivation and scope

The published CM towers are indexed by the compact open levels of the
opposite group `σ.FiniteAdelicPointsᵐᵒᵖ`, and their moduli schemes are
indexed by the sufficiently small levels. To fix the component of the level
at the places dividing `m` and let the prime-to-`m` component vary, as
Harris (1999), Proposition 4.10 on printed p. 311, does for the places over
`ℓ` and `p`, one needs the splitting of the opposite group. One also needs a
condition on the fixed component under which every level `e⁻¹ (K₀ × K')` is
sufficiently small. This module gives both. It does not show that levels
satisfying the condition exist. Harris's passage is motivation only; no
statement from it is formalized.

## Inputs

The published `Langlands.Shimura.Unitary.PointsSplit` provides, for a
`ℚ`-algebra `A` with `[Ring A]` and `[Module.Finite ℚ A]`,
`σ : AlgebraInvolution ℚ A`, a natural number `m` and `hm : m ≠ 0`, the
groups `σ.DividingPoints m` (points with coefficients in the product of the
completions of `ℚ` at the finite places `v` whose prime ideal contains `m`)
and `σ.PrimeToPoints m` (points with coefficients in the prime-to-`m` finite
adeles). It also provides the isomorphism of topological groups
`σ.finiteAdelicPointsSplit m hm : σ.FiniteAdelicPoints ≃ₜ* σ.DividingPoints m × σ.PrimeToPoints m`,
the local projections `σ.dividingLocalMap m v : σ.DividingPoints m →ₜ* σ.Points (FiniteCompletion ℚ v.1)`,
and `dividingLocalMap_finiteAdelicPointsSplit`, which states that the local
projection at `v` of the first component of the splitting of `g` is
`σ.finiteLocalMap v.1 g`.

The published `Langlands.Shimura.Unitary.SufficientlySmallLevels` provides
`σ.LevelSmallAt U v` for a level `U` of `σ.FiniteAdelicPointsᵐᵒᵖ` and a
finite place `v`: every `g ∈ U` whose local image at `v` has finite order
has trivial local image. It also provides
`σ.LevelSufficientlySmall U`, this condition at some finite place.

The published `Langlands.Shimura.PartialLevelTower`,
`Langlands.Shimura.PEL.TraceSimilitudesLevels` and
`Langlands.Shimura.SplitLevelTower` provide, in namespace
`Langlands.Shimura.CompactOpenLevel`, the product level `prod K K'`, the
transported level `transport e K`, and `mem_transport_symm_prod`:
`g ∈ transport e.symm (prod K K')` exactly when `(e g).1 ∈ K` and
`(e g).2 ∈ K'`. We write `e⁻¹ (K × K')` for `transport e.symm (prod K K')`.

## The opposite splitting

In namespace `Langlands.Shimura.CompactOpenLevel`, for groups with
topologies `G`, `H` and `H'`:

- `oppositeSplit e : Gᵐᵒᵖ ≃ₜ* Hᵐᵒᵖ × H'ᵐᵒᵖ` for `e : G ≃ₜ* H × H'` sends
  `g` to `(op (e g.unop).1, op (e g.unop).2)`; its inverse sends `(h, h')`
  to `op (e.symm (h.unop, h'.unop))`. The simp lemmas
  `oppositeSplit_apply_fst`, `oppositeSplit_apply_snd` and
  `oppositeSplit_symm_apply` record these formulas, by `rfl`.

## The rational case

The following declarations are in namespace
`Langlands.Shimura.AlgebraInvolution`. Let `A`, `σ` and `m` be as in the
inputs, and write `v` for an element of
`{v : FinitePlace ℚ // (m : 𝓞 ℚ) ∈ v.asIdeal}`.

- `σ.finiteAdelicPointsOpSplit m hm` is
  `oppositeSplit (σ.finiteAdelicPointsSplit m hm)`, an isomorphism of
  topological groups
  `σ.FiniteAdelicPointsᵐᵒᵖ ≃ₜ* (σ.DividingPoints m)ᵐᵒᵖ × (σ.PrimeToPoints m)ᵐᵒᵖ`.
- `σ.DividingLevelSmallAt m K₀ v`, for a level `K₀` of
  `(σ.DividingPoints m)ᵐᵒᵖ`: for every `h ∈ K₀`, if
  `σ.dividingLocalMap m v h.unop` has finite order, it is `1`. This is the
  condition `LevelSmallAt` at `v`, stated for the factor at the places
  dividing `m`.
- `σ.DividingLevelSufficientlySmall m K₀`: `σ.DividingLevelSmallAt m K₀ v`
  for some `v`.
- `DividingLevelSmallAt.mono` and `DividingLevelSufficientlySmall.mono`: both
  conditions pass from `L₀` to every level `K₀` with `K₀ ≤ L₀`.
- `levelSmallAt_transport_prod hm hK₀ K'`: if
  `hK₀ : σ.DividingLevelSmallAt m K₀ v`, then for every level `K'` of
  `(σ.PrimeToPoints m)ᵐᵒᵖ` the level `e⁻¹ (K₀ × K')` of
  `σ.FiniteAdelicPointsᵐᵒᵖ`, for `e = σ.finiteAdelicPointsOpSplit m hm`,
  satisfies `σ.LevelSmallAt _ v.1`.
- `levelSufficientlySmall_transport_prod hm hK₀ K'`: if
  `hK₀ : σ.DividingLevelSufficientlySmall m K₀`, then every such level
  `e⁻¹ (K₀ × K')` satisfies `σ.LevelSufficientlySmall`.

## Proof outline

The group laws of `oppositeSplit e` follow from those of `e` by `simp`, and
its continuity from the continuity of `e`, `e.symm`, `op`, `unop` and the
product projections. For `levelSmallAt_transport_prod`, an element
`g ∈ e⁻¹ (K₀ × K')` has first component `op (σ.finiteAdelicPointsSplit m hm g.unop).1`
in `K₀` by `mem_transport_symm_prod`. Its local image at `v.1` is
`σ.finiteLocalMap v.1 g.unop`, which by
`dividingLocalMap_finiteAdelicPointsSplit` is the local image at `v` of this
first component, so the hypothesis on `K₀` applies.
`levelSufficientlySmall_transport_prod` takes the same place `v.1`.

## Provenance

This is an internal construction from the published `PointsSplit`,
`SufficientlySmallLevels`, `PartialLevelTower`, `TraceSimilitudesLevels` and
`SplitLevelTower`. The sufficiently small condition is the published one of
Harris–Taylor (2001), Chapter III, section 1, printed p. 90, as formalized
in `SufficientlySmallLevels`; its restriction to the factor at the places
dividing `m` is an implementation choice. Harris (1999), Proposition 4.10 on
printed p. 311, is motivation only.
