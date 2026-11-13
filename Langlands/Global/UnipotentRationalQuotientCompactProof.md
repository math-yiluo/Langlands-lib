# Compactness of `U(F) \ U(𝔸_F)` for smooth connected unipotent groups

Worker 126, task 5462 (`08c16c96-da45-41e6-87a2-ca639d48e73d`). The task context records
that Worker 3659 of the previous instance had already type-checked the same composite term
as development evidence.

## What is proved

The theorem `Langlands.Global.AdelicGroupPoints.unipotentRationalQuotientCompact.{u}` has
exactly the type of the published proposition
`Langlands.Global.AdelicGroupPoints.UnipotentRationalQuotientCompactStatement.{u}`
(`Langlands/Global/TriangularRationalQuotientCompact.lean`). The proposition is unchanged
and keeps its universe parameter `u`. It says: for every number field `F : Type u`, every
group scheme `U` over `Spec F` with `IsAffine U.X.left` and
`LocallyOfFiniteType U.X.hom`, if `U.X.hom` is smooth, `U.X.left` is connected and
`IsUnipotent U` holds, then `RationalQuotient F U` is a compact space.
`RationalQuotient F U` is the Library's left coset space `U(F) \ U(𝔸_F)` of the adelic
points `AdelicGroupPoints F U`, with the actual adele ring `AdeleRing (𝓞 F) F`, its
coordinate-evaluation topology and the quotient topology, as described in
`TriangularRationalQuotientCompact.md`. The proof assumes no further hypothesis. It uses
only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## The proof

The proof is one term:

```lean
unipotentRationalQuotientCompact_of_split perfectFieldUnipotentSplit
  splitUnipotentAffineTorsorStatement
```

It combines three theorems that are already in the Library.

1. `Langlands.Global.AdelicGroupPoints.unipotentRationalQuotientCompact_of_split`
   (`Langlands/Global/SplitUnipotentRationalQuotientCompact.lean`) proves
   `PerfectFieldUnipotentSplitStatement.{u} → SplitUnipotentAffineTorsorStatement.{u} →
   UnipotentRationalQuotientCompactStatement.{u}`. Its argument is as follows. A number
   field has characteristic zero, so it is a perfect field. The first input then gives a
   split series of `U`: a finite normal series whose successive represented fppf quotients
   are one-dimensional vector groups. The second input gives a scheme section of each
   quotient map in the series. Induction along the series then gives a compact set of
   adelic points that meets every rational coset. The base case is the trivial group. The
   one-dimensional vector-group case comes from the Library's triangular-coordinates
   theorem, which rests on the compactness of `F \ 𝔸_F`. The image of this compact set in
   `RationalQuotient F U` is compact and is the whole quotient. The details are in
   `SplitUnipotentRationalQuotientCompact.md`.
2. `Langlands.GroupScheme.perfectFieldUnipotentSplit`
   (`Langlands/GroupScheme/Unipotent/PerfectFieldSplitProof.lean`) proves
   `PerfectFieldUnipotentSplitStatement.{u}`: over a perfect field, every smooth
   connected affine unipotent group scheme is split unipotent
   (`RelativeRoot.IsSplitUnipotent`). This is the non-equivariant part of Milne,
   *Algebraic Groups* (2017), Corollary 16.24. See `PerfectFieldSplitProof.md`.
3. `Langlands.GroupScheme.splitUnipotentAffineTorsorStatement`
   (`Langlands/GroupScheme/SplitUnipotentAffineTorsorProof.lean`) proves
   `SplitUnipotentAffineTorsorStatement.{u}`: every fpqc torsor under the base change of
   a smooth affine split-unipotent group over a field has a section over every affine
   scheme over that field. See `SplitUnipotentAffineTorsorProof.md`.

Applying item 1 to the theorems of items 2 and 3 gives the target. All three use the same
universe `u` as the target. The hypothesis `LocallyOfFiniteType U.X.hom` is part of the
statement but is not needed by this route; item 1 discharges the statement with it present.

## Provenance

The mathematical result is the unipotent case of J. R. Getz and H. Hahn, *An Introduction
to Automorphic Representations* (2024), Theorem 2.6.3, printed p. 69 (registered source
`getz-hahn-2024-automorphic-representations`). For smooth connected `G`, that theorem says
`G(F) \ G(𝔸_F)¹` is compact if and only if `T_F̄ ≤ R(G_F̄)` for every `F`-split torus
`T ≤ G`. Here `R` is the solvable radical, the maximal connected normal solvable subgroup.
It is not the unipotent radical `R_u`. Both radicals are defined in Getz–Hahn
Definition 1.5.6, printed pp. 14–15. The norm-one subgroup `G(𝔸_F)¹` is the intersection
of the kernels of `|χ|` over the characters `χ` of `G`, equation (2.19), printed p. 68.

For a smooth connected unipotent `U`, two facts specialize this theorem to the statement
proved here:

- Every character of `U` is trivial, so `U(𝔸_F)¹ = U(𝔸_F)`. This is J. S. Milne,
  *Algebraic Groups* (2017), Corollary 14.18(a), printed p. 284: there is no nontrivial
  homomorphism from a unipotent group to a group of multiplicative type.
- The compactness criterion holds. By Milne Corollary 14.18(b), a homomorphism from a
  torus to `U` is trivial, so the only split torus in `U` is the trivial one. The
  criterion `T_F̄ ≤ R(U_F̄)` then holds for every split torus `T`. (It also holds directly,
  because a unipotent group is solvable, Getz–Hahn p. 15, so `R(U_F̄) = U_F̄`.)

The Lean proof does not use Theorem 2.6.3 or the facts above. It uses the split-series
induction described in the previous section. This module adds no new definition or
statement.
