# Renard VI.9.1, bound and Remarks 1–2, from the uniform stabilization

Author: Worker 167. Module
`Langlands.Representation.Exponents.GeneralizedJacquetRemarksReduction`, namespace
`Langlands.Aubert.General.RationalPointFamily`.

This is an intermediate reduction for proof task `7a03c792-1d54-4a95-89b7-dd1aa5e82a5e`,
whose first target is the unchanged Library proposition
`GeneralizedJacquetRemarksStatement.{u, v}` (module
`Langlands.Representation.Exponents.GeneralizedJacquetRemarksStatements`). It does **not**
prove that target, nor `UniformCompressionStabilizationStatement` (the Proposition of
VI.9.1, proof task `47e556e6-6b2a-40dc-ba66-d6a0585f5220`), nor the Remark 3 target
`RepresentedParabolic.GeneralizedJacquetContractingRangeStatement`.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, VI.9.1: the last sentence of the Proposition (`b ≤ c(G, K)`) and
Remarques 1 and 2 with their proof, printed pp.197–198 / PDF pp.203–204. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## Statement

```lean
def GeneralizedJacquetRemarksReductionStatement : Prop :=
  UniformCompressionStabilizationStatement.{u, v} → GeneralizedJacquetRemarksStatement.{u, v}
```

Both sides are the published Library propositions, used unchanged, at the same independent
universes `u` (field and group) and `v` (representation carriers). The statement says that
the Proposition of VI.9.1 (one exponent `b` for all smooth representations, stationary
ranges and kernels from `b` on, and the splitting `V^K = V^K_0 ⊕ V^K_*`, for every
`M`-central Iwahori contraction of the dynamic parabolic of a cocharacter) implies, in the
same dynamic setting, the bound "`b` may be taken to be any `c` bounding `dim V^K` on
irreducible smooth representations", Remark 1 (independence of the contracting element)
and Remark 2 (`V^K_0 = V^K ∩ ker e_C` and `V^K_* = e_K e_{C̄} V` for fixed compact open
`C ≤ N`, `C̄ ≤ N̄`). The derived implication is ours; Renard derives the bound inside the
proof of the Proposition and the Remarks after it.

## Declarations and implemented proofs

* `generalizedJacquetRemarks_of_uniformStabilization (hstab) :
  GeneralizedJacquetRemarksStatement.{u, v}`. After introducing the field `k`, the group
  `G`, the statement's `pointTopology` and instances, the cocharacter `χ`, `K`, `g`, and the
  hypotheses (`g` central in `M = Dynamic.centralizer χ`, Iwahori contraction for
  `N = Dynamic.unipotent χ`, `N̄ = Dynamic.unipotent χ⁻¹`), the proof gathers:
  - `N` and `N̄` are closed (`BruhatTits.DynamicUnipotentContainment.isClosed_unipotentPoints`
    for `χ` and `Dynamic.inverseCocharacter χ`);
  - `M` normalizes `N` and `N̄` (`Dynamic.centralizer_le_normalizer_unipotent`, with
    `Dynamic.centralizer_inverseCocharacter` for `N̄`);
  - `G(k)` is second countable (`reductiveRationalPoint_secondCountable`), so the discrete
    quotient `G(k) ⧸ K` is separable, hence countable.

  Bound: `hstab` applied to `g` gives the splitting for every smooth representation;
  `Jacquet.stabilization_bound_of_separation` (module
  `Langlands.Representation.Jacquet.CompressionSeparationBound`) with the separation
  theorem `Jacquet.fixedVectorsSeparatedByIrreducibles K hK` (module
  `Langlands.Representation.Jacquet.FixedVectorIrreducibleSeparation`) gives the
  stationary equalities from any `c` on.

  Remarks 1 and 2: `Jacquet.remarks_of_uniformStabilization` (module
  `Langlands.Representation.Jacquet.IwahoriContractionRemarks`), whose uniform hypothesis
  is `hstab` applied to each `M`-central Iwahori contraction `g'`.
* `generalizedJacquetRemarksReduction : GeneralizedJacquetRemarksReductionStatement.{u, v}`
  is that theorem, at arbitrary independent universes `u` and `v`.

The dynamic-parabolic hypotheses enter only through closedness of `N`, `N̄`, normality
under `M`, and the call to `hstab`. No admissibility, finite length, finite generation or
finite-dimensional fixed-vector premise is added. The proof uses only the standard axioms.
