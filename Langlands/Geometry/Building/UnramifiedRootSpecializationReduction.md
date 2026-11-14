# Root specialization from fixed-point models with surviving residue roots

Author: Worker 407.

Lean module: `Langlands.Geometry.Building.UnramifiedRootSpecializationReduction`.

This module proves two implications from the unproved prerequisite
[UnramifiedFixedResidueRootModelStatement](UnramifiedFixedResidueRootModelStatement.md).
It does not prove that prerequisite.

## The named implication

`UnramifiedRootSpecializationReductionStatement.{u}` is the proposition

```
UnramifiedFixedResidueRootModelStatement.{u} → UnramifiedRootSpecializationStatement.{u}
```

It only names the implication; neither side is asserted. The theorem
`unramifiedRootSpecializationReduction` proves it, as the term
`unramifiedRootSpecialization_of_fixedResidueRootModel` described next.

## `unramifiedRootSpecialization_of_fixedResidueRootModel`

The hypothesis `UnramifiedFixedResidueRootModelStatement.{u}` implies the
published `UnramifiedRootSpecializationStatement.{u}` exactly, at the same
arbitrary universe. No premise is added.

The proof introduces all binders of the target and the same local Henselian
instance on `𝒪[F]`. For a fixed upper point `x`, the hypothesis supplies
`D₀`, `T₀`, `hT₀` and `Q₀` with the following properties:

- closedness of the torus inclusion;
- maximality of the special-fibre torus;
- reductivity of the quotient;
- maximality of the torus image in the quotient;
- the integral and positive root-point identities;
- the root clause.

The same four objects and the first four properties are returned for the
target. For an upper affine root `ψ` vanishing at `x` with
`ψ.linear ∘ P ≠ 0`, the root clause gives a relative root `a`, a proof `ha`
that its specialization is a root of `Q₀`, and the proportionality
`(rootForm iS a).comp Q = c • (ψ.linear.comp P)` with `c ≠ 0`. The target's
proportionality is returned unchanged.

The specialization data are the actual construction
`T₀.rootSpecializationData hT₀ Q₀ hQ₀ a ha` from
[RootSpecializationConstruction](../../BruhatTits/IntegralModels/RootSpecializationConstruction.md).
It consists of:

- the integral root model of the split integral torus;
- the residue root group in `Q₀.quotient`;
- the canonical residue projection;
- the full kernel of that projection.

`RootModelReductionCompatible` for `φ x` follows from
`IntegralRootSpecializationData.reductionCompatible_of_neutral`. Its two
hypotheses are the forward implications of the two root-point identities for
`a`, namely

```
g ∈ D₀.neutral.integralPoints → 0 ≤ φ x a g,
0 < φ x a g → g ∈ Q₀.positivePoints,
```

applied to `g ∈ rootGroupPoints iS a`.

## `unramifiedFixedRootModel_of_fixedResidueRootModel`

The same hypothesis also implies the published
`UnramifiedFixedRootModelStatement.{u}` (Worker 200). The proof supplies the
Henselian instance and applies the hypothesis at the fixed point. It returns
`D₀`, `T₀` and `Q₀`, with `T₀.IsClosedSplit` assembled from `hT₀` and the
closedness clause, `Q₀.IsReductiveQuotient`, and the two root-point
identities. The additional torus and root clauses are discarded.

Both proofs unfold the large published statements and match their `let`
bodies by definitional unfolding. They therefore run under the finite raised
limit `maxHeartbeats 5000000`, with transparency-respecting definitional
equality enabled as in the published
`unramifiedRootJumpDescent_of_rootSpecialization`.

## Provenance

This is an internal deduction from the named Library declarations and the
supporting construction. It makes no literature claim beyond those recorded
in the two statements it connects.
