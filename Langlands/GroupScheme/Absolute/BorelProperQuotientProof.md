# Proof that some Borel subgroup has proper homogeneous quotients

Authors: Worker 1396 (route, reduction and this assembly) and Worker 1399 (the stabilizer and
reduced-subgroup helpers used by the reduction, and the proof of the flag input).

The module proves

```
theorem Langlands.GroupScheme.someBorelQuotientProper :
    SomeBorelQuotientProperStatement.{u}
```

for the published proposition of `Langlands.GroupScheme.Absolute.BorelProperQuotientStatement`,
at arbitrary universe `u`. For every algebraically closed field `k`
and every smooth, affine, connected group scheme `G` over `Spec k`, there is a Borel subgroup
`i : B ⟶ G` with the following property. Every separated, locally finite type, quasi-compact
`Q` over `Spec k` is proper over `Spec k` if it receives a smooth, surjective, quasi-compact
`q : G.X ⟶ Q` whose fibers on every test scheme are exactly the left cosets of `B`.

## Implemented proof

The proof is a single term. It applies the published reduction
`someBorelQuotientProper_of_prerequisites`
(module `Langlands.GroupScheme.Absolute.BorelProperQuotientReduction`) to three published
theorems:

- `generalLinearSolvableStabilizer : GeneralLinearSolvableStabilizerStatement.{u}`
  (module `Langlands.GroupScheme.Absolute.GeneralLinearSolvableStabilizerProof`). For every
  algebraically closed `k` and every `N`, `GL_N` acts on a nonempty proper scheme over `Spec k`.
  Every closed subgroup fixing a rational point of that scheme is solvable.
- `closedOrbit : ClosedOrbitStatement.{u}` (module `Langlands.GroupScheme.ClosedOrbitProof`).
  An action of a smooth affine group on a nonempty scheme of finite type has a reduced closed
  orbit, which is a closed subscheme with an equivariant action that is transitive on rational
  points.
- `solvableProperFixedPoint : SolvableProperFixedPointStatement.{u}` (module
  `Langlands.GroupScheme.SolvableProperFixedPointProof`). A smooth, connected, affine, solvable
  group acting on a nonempty proper scheme over an algebraically closed field fixes a rational
  point.

The reduction's Markdown explains how these combine. In short, embed `G` as a closed subgroup
of `GL_N` and restrict the flag action to `G`. Take a closed orbit `O`, which is proper. Let an
arbitrary Borel subgroup `B` fix a rational point `y` of `O`. Maximality of `B` and solvability
of point stabilizers identify `B` with the reduced identity component of the stabilizer of `y`.
The orbit map at `y` is flat. The finite-index quotient transfer then shows that every
homogeneous quotient by `B` is proper.

The proof uses no Borel conjugacy and no dimension theory. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

The target is Milne, *Algebraic Groups* (2017), Theorem 17.9(a), printed p.354 (PDF p.370),
source `milne-2017-algebraic-groups`, restricted to the existence of one Borel subgroup with
proper quotients. Milne proves it for a Borel subgroup of maximal dimension, using Chevalley's
theorem, Lie–Kolchin and the closed-orbit lemma. The route here instead combines a closed orbit,
the Borel fixed point theorem (Milne Corollary 17.3, printed p.353, PDF p.369) and
solvable stabilizers on a flag-type scheme, as described in the reduction's Markdown.
