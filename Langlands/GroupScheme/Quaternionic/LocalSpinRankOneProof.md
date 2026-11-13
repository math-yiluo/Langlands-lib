# Quaternionic spin groups of rank one over local fields

Author: Worker 5397.

This module proves the published proposition
`Langlands.GroupScheme.Quaternionic.LocalSpinRankOneStatement.{u}` at an arbitrary
universe `u`, with its hypotheses unchanged. The theorem is
`Langlands.GroupScheme.Quaternionic.localSpinRankOne`.

## What is proved

Let `K` be a nonarchimedean local field of any characteristic, including residue
characteristic 2. Let `D` be a central quaternion division algebra over `K`, and let `σ` be
an involution of the first kind with `dim_K D^σ = 3`. Let `m = 4` or `m = 5`, and let `q` be
a nondegenerate `σ`-quadratic form on `D^m`, in the sense of Tits, of Witt index 1. Then:

1. there is a spin cover `π : S ⟶ σ.isometryGroup q` over `Spec K`, and
2. every spin cover `S` of `q` is simply connected and almost simple, and has split rank 1.

These are exactly the two conjuncts of `LocalSpinRankOneStatement`. The statement's
Markdown, `LocalSpinRankOneStatement.md`, gives the meaning of the data and the source in
Prasad–Raghunathan (1985), §2, family (iii).

## Implemented proof

The proof is a single term. It applies three published Library theorems:

- `localSpinRankOneReduction : LocalSpinRankOneReductionStatement.{u}` (module
  `Langlands.GroupScheme.Quaternionic.LocalSpinRankOneReduction`). It proves the implication
  `OrdinaryOrthogonalGeometryStatement.{u} → QuaternionicMoritaIsometryStatement.{u} →
  LocalSpinRankOneStatement.{u}`.
- `ordinaryOrthogonalGeometry : OrdinaryOrthogonalGeometryStatement.{u}` (module
  `Langlands.GroupScheme.Quaternionic.OrdinaryOrthogonalGeometryProof`). Over every field, the
  orthogonal group scheme of a nondegenerate quadratic form of rank `2m ≥ 6` is smooth, and
  its identity component is absolutely almost simple.
- `quaternionicMoritaIsometry : QuaternionicMoritaIsometryStatement.{u}` (module
  `Langlands.GroupScheme.Quaternionic.QuaternionicMoritaIsometryProof`). This is the
  isometry-group part of Tits (1968), §3, Proposition 6. After base change to
  `AlgebraicClosure K`, the quaternionic isometry group of `q` becomes isomorphic, as a group
  scheme, to the ordinary orthogonal group of a nondegenerate scalar quadratic form of rank
  `2m`.

The theorem is `localSpinRankOneReduction ordinaryOrthogonalGeometry
quaternionicMoritaIsometry`. All three results are stated at the same universe `u`, so
Lean checks the application directly.

The reduction's paired Markdown, `LocalSpinRankOneReduction.md`, explains how it combines the
two inputs:

1. The Morita comparison and the ordinary orthogonal result, together with
   `IdentityComponent.smooth_and_isAbsolutelyAlmostSimple_of_fieldExtension_iso`, show that
   `σ.isometryGroup q` is smooth and `σ.connectedIsometryGroup q` is absolutely almost simple.
   Both `m = 4` and `m = 5` satisfy `m ≥ 3`.
2. An almost simple group is semisimple, so
   `FirstKindInvolution.exists_isSpinCover_of_isSemisimple` produces a spin cover.
3. A nonarchimedean local field is infinite. With nondegeneracy and Witt index 1, this gives
   `FirstKindInvolution.splitRank_connectedIsometryGroup_eq_one`.
4. `IsSpinCover.properties_of_connectedIsometryGroup` then shows that every spin cover is
   simply connected, almost simple and of split rank 1.

## Scope and provenance

No premise is added, and no restriction is placed on the characteristic. All objects and
predicates come unchanged from the statement module and the modules it imports. This module
only composes published theorems. It makes no claim about the original literature beyond
those theorems, whose sources are given in their own Markdown files.
