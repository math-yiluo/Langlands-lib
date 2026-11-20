# Left continuity of the Moy–Prasad Lie filtration on supplied data

`KPLieGradedAction` introduces the predicate `IsLeftContinuousAt x t`: there is
`s < t` with `𝔤_{x,u} ⊆ 𝔤_{x,t}` for every `u` with `s < u ≤ t`. Under this
hypothesis at `-r`, triviality on `𝔤_{x,-r}/𝔤_{x,(-r)+}` transfers to
`𝔤*_{x,r}/𝔤*_{x,r+}`. This module derives the hypothesis at every real depth
from two conditions on the supplied data:

- left continuity of the supplied centralizer lattices `z_r`;
- the Library's bounded finiteness of the actual affine roots, which holds under
  `RelativeRoot.HasOppositeFactorPairs`.

## Setting

`F` is a nonarchimedean local field with ring of integers `𝒪 = 𝒪[F]` and
maximal ideal `𝔪 = 𝓂[F]`. `G` is a group scheme over `Spec F` with
`[IsAffineHom G.X.hom]`. `P : ParahoricBuildingData G` and
`L : P.LieFiltrationData` are supplied data. From the Library it uses:

- `L.centralizerLie r` (the supplied lattice `z_r` in `Lie(Z)`, a decreasing
  family in `r ≥ 0`), `L.affineRootLie ψ` and
  `L.lieFiltration x r = image of z_r ⊔ ⨆_{ψ(x) ≥ r} u_ψ`
  (`Geometry.Building.KPLieFiltration`, KP 13.3.3);
- the real-depth extension `L.lieFiltrationReal x r`, characterized by
  `mem_lieFiltrationReal`: `X ∈ 𝔤_{x,r}` if and only if `a • X ∈ 𝔤_{x,r+n}` for
  all `a ∈ 𝔪^n`, where `n = indexShift r = ⌈-r⌉₊` and
  `shiftedIndex r = r + n`; and the periodicity `L.IsPeriodic`, which says
  `𝔤_{x,r+1} = 𝔪 • 𝔤_{x,r}` for `r ≥ 0` (`Geometry.Building.KPLieFiltrationDual`);
- `IsLeftContinuousAt`, `ActsTriviallyOnGraded`, `ActsTriviallyOnDualGraded` and
  `actsTriviallyOnDualGraded_of_isLeftContinuousAt`
  (`Geometry.Building.KPLieGradedAction`);
- `ValuationBuildingData.finite_bounded_affineRoots_of_oppositePairs`
  (`Geometry.Building.ActualAffineRootLocalFiniteness`). Under
  `RelativeRoot.HasOppositeFactorPairs P.i`, it says that for every point `x`
  and every bound, only finitely many affine roots `ψ` satisfy
  `|ψ(x)| ≤ bound(ψ̇)`.

All declarations are in the namespace
`Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData`.

## Cancelling a uniformizer

- `mem_of_smul_mem_maximalIdeal_smul hϖ h`: for an `𝒪`-submodule `M` of `𝔤`
  and a uniformizer `ϖ`, if `ϖ • Z ∈ 𝔪 • M` then `Z ∈ M`. Since `𝔪 = (ϖ)`,
  `𝔪 • M = ϖ • M` (`Submodule.ideal_span_singleton_smul`), so `ϖ • Z = ϖ • Y`
  for some `Y ∈ M`. Since `𝔤` is an `F`-vector space and `ϖ ≠ 0` in `F`,
  `Z = Y`.

## From non-negative to real depths

- `isLeftContinuousAt_of_lieFiltration hL hN t`: assume periodicity and that,
  for every `τ > 0`, there is `s < τ` with `𝔤_{x,u} ⊆ 𝔤_{x,τ}` for all
  non-negative `u` with `s < u ≤ τ`. Then `IsLeftContinuousAt x t` holds for
  every real `t`. Write `n = indexShift t`. There are two cases.
  - If `t + n > 0`, then every `u` in `(max(s' - n, -n), t]` has the same
    shift `n`, where `s'` comes from the hypothesis at `τ = t + n`. So
    `a • X ∈ 𝔤_{x,u+n} ⊆ 𝔤_{x,t+n}` for `a ∈ 𝔪^n`. This case does not use
    periodicity.
  - If `t + n = 0`, then `t = -n`, and every `u` in
    `(max(s' - (n+1), t - 1), t)` has shift `n + 1`, where `s'` comes from the
    hypothesis at `τ = 1`. For `b ∈ 𝔪^n`, `ϖb ∈ 𝔪^{n+1}`, so
    `ϖ • (b • X) ∈ 𝔤_{x,u+n+1} ⊆ 𝔤_{x,1} = 𝔪 • 𝔤_{x,0}`, using periodicity. By
    the cancellation lemma, `b • X ∈ 𝔤_{x,0}`.

## Left continuity of the supplied lattices

- `lieFiltration_le_of_forall x hz hψ`: if `z_u ⊆ z_τ`, and every affine root
  with `ψ(x) ≥ u` also has `ψ(x) ≥ τ`, then `𝔤_{x,u} ⊆ 𝔤_{x,τ}`. This follows
  by comparing the two supremum descriptions.
- `exists_lt_forall_affineRoots_of_oppositePairs hF x τ`: under
  `HasOppositeFactorPairs`, for every real `τ` there is `s < τ` such that every
  affine root with `ψ(x) > s` has `ψ(x) ≥ τ`. In other words, no affine-root
  value at `x` lies in `(s, τ)`. Only finitely many roots satisfy
  `|ψ(x)| ≤ |τ| + 1`, so the values in `(τ - 1, τ)` form a finite set. Take `s`
  to be the maximum of these values and `τ - 1`.
- `IsCentralizerLieLeftContinuous L` (definition): for every `τ > 0` there is
  `s < τ` with `z_u ⊆ z_τ` for all `u` with `s < u ≤ τ`. Since the family is
  decreasing, this means `z_u = z_τ` on `(s, τ]`.
- `exists_lieFiltration_le_of_oppositePairs hF x τ hz`: under
  `HasOppositeFactorPairs`, left continuity of `z` at `τ` gives left continuity
  of `𝔤_{x,·}` at `τ`. Take the larger of the two `s`.
- **`isLeftContinuousAt_of_oppositePairs hL hF hz x t`**: under periodicity,
  `HasOppositeFactorPairs` and `IsCentralizerLieLeftContinuous L`,
  `IsLeftContinuousAt x t` holds for every point `x` and every real `t`.
- `actsTriviallyOnDualGraded_of_oppositePairs hL hF hz hN`: under the same
  hypotheses, `ActsTriviallyOnGraded x (-r) N` implies
  `ActsTriviallyOnDualGraded x r N`.

## Comparison with Kaletha–Prasad

Kaletha–Prasad, §13.3.1 (printed p. 470, PDF p. 501), define `𝔤_{x,r}` for
`r ≥ 0` as the Lie algebra of the group scheme `𝒢_{x,r}` of the constant
concave function `r` (§8.5). They extend it to all real `r` by
`𝔤_{x,r+n} = 𝔪^n · 𝔤_{x,r}` (Proposition 8.5.16) and set
`𝔤_{x,r+} = ⋃_{s>r} 𝔤_{x,s}`. The Library's `lieFiltration` reads §13.3.3 as
the span of the lattices `z_r` and of the `u_ψ` with `ψ(x) ≥ r`, for supplied
lattices (`KPLieFiltration`). KP do not state left continuity separately. For
their filtration it comes from the non-strict inequalities `ψ(x) ≥ r` (and the
corresponding valuation conditions on the torus part) together with the
discreteness of the jumps. The theorems here record this deduction for the
supplied data. Discreteness of the affine-root values at `x` comes from the
Library's finiteness theorem. The corresponding property of the torus part is
the hypothesis `IsCentralizerLieLeftContinuous`. The corrections of
1 November 2024 have no entry for §13.3.

## Provenance

Derived. The deduction is internal. It was written for this program, and no
published statement or proof is transcribed. Besides the Library declarations
listed in the Setting, the Lean code uses `indexShift`, `shiftedIndex`,
`centralizerLieImage` (through the definition of `lieFiltration`), and from
Mathlib
`IsDiscreteValuationRing.exists_irreducible`,
`IsDiscreteValuationRing.irreducible_iff_uniformizer`,
`Submodule.ideal_span_singleton_smul`,
`Submodule.mem_smul_pointwise_iff_exists`, `algebraMap_smul`,
`smul_right_injective`, `Nat.ceil_le`, `Nat.lt_ceil`, `Set.Finite.image` and
`Finset.max'`. No external code is adapted.

## Not claimed

- Left continuity of the supplied centralizer lattices is a hypothesis. It is
  not derived from a construction of KP's `𝔱_r`.
- `HasOppositeFactorPairs` and periodicity are hypotheses.
- Left continuity is not claimed for arbitrary supplied data, and
  `IsCentralizerLieLeftContinuous` is a real restriction: for a nonzero lattice
  `W`, the decreasing family `z_r = ϖ^{⌊r⌋} W` fails it at every positive
  integer. The right-continuous family in `KPLieGradedAction` shows that
  periodicity alone does not give the transfer to the dual graded pieces.
