# Solvability after arbitrary field extension

Worker 1370 authored the Lean proof and its initial explanation. Worker 1449
assessed the reused proof and expanded this explanation.

`Langlands.GroupScheme.solvableFieldExtensionStatement` proves exactly
`Langlands.GroupScheme.SolvableFieldExtensionStatement.{u}`. Thus, for arbitrary
fields `k K : Type u`, every actual morphism `b : Spec K ⟶ Spec k`, and every
smooth affine group scheme `G` over `Spec k`, the existing predicate
`IsSolvableGroupScheme G` implies that predicate for the actual pullback
`(GroupScheme.baseChange b).obj G`. The theorem adds no assumptions to the
published proposition.

The implementation first proves a stronger intermediate fact: there is one
natural number `n` such that the abstract derived series of `T ⟶ G.X` vanishes
at depth `n` for every test scheme `T` over `Spec k`.

The lemma `SolvableFieldExtensionProof.geometricPoints_isSolvable` starts from
the definition of `IsSolvableGroupScheme`, namely solvability of the chosen
algebraic-closure points of the pullback to `AlgebraicClosure k`. The published
multiplicative equivalence `baseChangePointsEquiv` identifies that group with
the group of morphisms from `Spec (AlgebraicClosure k)` to `G` over `Spec k`.
The abstract solvability criterion supplies a depth `n` at which its
`derivedSeries` is the bottom subgroup.

For each finite term `t : DerivedTerm n`, `evaluation_eq_one` proves that its
actual evaluation morphism `DerivedTerm.evaluation G t` is the unit morphism.
The published `DerivedTerm.evaluation_mem` places its value at every geometric
input in that vanishing derived subgroup. To upgrade this equality of values
to equality of morphisms, the proof applies
`SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat`.
The domain is smooth by `DerivedTerm.smooth_domain`, hence flat and locally
of finite type. It is reduced by
`Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field`.
The affine structural morphism of `G` supplies the separated target needed by
extensionality. These facts apply to all finite term domains, including the
terminal domain for a constant unit term.

The lemma `exists_uniform_derivedSeries_eq_bot` now uses
`DerivedTerm.exists_evaluation`: every element of the depth-`n` derived
subgroup of `T ⟶ G.X` is the value of some such finite term. Since its
evaluation morphism is the unit, the element is the identity. This works for
every `T : Over (Spec k)`, without an affineness or reducedness condition on
`T`. The lemma `allPoints_isSolvable` records the resulting solvability.

For the final theorem put `H = (GroupScheme.baseChange b).obj G` and let `T`
be `Spec (AlgebraicClosure K)` over itself. Write `cK` for
`toAlgebraicClosure K`, `U = (Over.map cK).obj T`, and
`V = (Over.map b).obj U`. Two applications of `baseChangePointsEquiv` give
multiplicative equivalences

```text
(T ⟶ ((GroupScheme.baseChange cK).obj H).X)
  ≃* (U ⟶ H.X)
  ≃* (V ⟶ G.X).
```

The last group is solvable by `allPoints_isSolvable`, so injective transport
along these equivalences makes the first group solvable. That first group is
exactly the chosen-geometric-point group in `IsSolvableGroupScheme H`.
This explicitly accounts for the further chosen algebraic closure in the
conclusion. The proof works directly with the given spectrum morphism `b`;
it needs no chosen embedding between the two algebraic closures.

The dependencies are the published exact statement, the internal finite-term
construction in `DerivedTerm`, the smooth-reduced theorem, geometric-point
extensionality, the point equivalences, and Mathlib's abstract derived series.
The argument uses no parabolic or Borel field-extension theorem,
`ParabolicDynamic`, or connected-reductivity extension. It constructs no
scheme-theoretic derived subgroups and makes no Borel-maximality claim.

The source motivation is Milne, *Algebraic Groups* (2017), Proposition 6.30
and Corollary 6.31, printed p.132 / one-based PDF p.148, registered source
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Milne uses algebraic derived subgroups; this implementation instead proves
finite term identities directly. The registered official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` has no correction to 6.30–6.31.
There is no separate finite-type premise: smoothness gives local finite type,
and affineness gives quasi-compactness, hence finite type. No infinite-type
extension is asserted. The result includes disconnected and trivial groups,
arbitrary characteristic, and inseparable or transcendental extensions.
