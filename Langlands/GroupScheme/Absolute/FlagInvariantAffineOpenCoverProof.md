# Proof of invariant affine neighbourhoods in actual Borel quotients

Author: Worker 1495.

This module proves the Library statement
`Langlands.GroupScheme.FlagInvariantAffineOpenCoverStatement` (module
`Langlands.GroupScheme.Absolute.FlagInvariantAffineOpenCoverStatement`) at an
arbitrary universe `u`:

```lean
theorem flagInvariantAffineOpenCover : FlagInvariantAffineOpenCoverStatement.{u}
```

The theorem has no hypotheses. It is the statement itself: let `k` be an
algebraically closed field and `G` a smooth connected affine group over `k`,
with a maximal torus `t : T ⟶ G`. Let `i : U ⟶ G` be a smooth connected
unipotent closed subgroup whose range lies in every Borel subgroup whose range
contains the range of `t`. Let `b : B ⟶ G` be a Borel subgroup, and
`q : G.X ⟶ Q` a flat, surjective, quasi-compact morphism to a separated,
quasi-compact scheme `Q` locally of finite type over `k`, whose fibres on every
test are the cosets `g B`. Let `a` be an action of `G` on `Q` with
`a.act g (h ≫ q) = (g * h) ≫ q`. Then every rational point `x` of `Q` lies in an
affine open `V` of `Q` whose inverse images under the restricted action
`(a.restrict i).hom : U × Q ⟶ Q` and under the second projection `U × Q ⟶ Q`
are equal.

## Proof

The proof composes published Library theorems; it adds no new argument.

1. The reduction `flagInvariantAffineOpenCover_of_prerequisites` (module
   `Langlands.GroupScheme.Absolute.FlagInvariantAffineOpenCoverReduction`)
   proves the target from four statements:
   `FlagCoreDualLineStatement`, `SpanningLineStabilizerStatement`,
   `SomeBorelQuotientProperStatement` and `BorelConjugacyStatement`.
2. The dual-line core `FlagCoreDualLineStatement` is supplied by
   `FlagCore.flagCoreDualLine_of_prerequisites` (module
   `Langlands.GroupScheme.FlagCoreAssembly`), applied to five proved
   statements:
   - `someBorelQuotientProper : SomeBorelQuotientProperStatement` (module
     `Langlands.GroupScheme.Absolute.BorelProperQuotientProof`);
   - `borelConjugacy : BorelConjugacyStatement` (module
     `Langlands.GroupScheme.Absolute.BorelConjugacyProof`);
   - `maximalTorusConjugacy : MaximalTorusConjugacyStatement` (module
     `Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof`);
   - `torusFiniteGaloisSplitting : TorusFiniteGaloisSplittingStatement` (module
     `Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof`);
   - `solvableProperFixedPoint : SolvableProperFixedPointStatement` (module
     `Langlands.GroupScheme.SolvableProperFixedPointProof`).
3. `SpanningLineStabilizerStatement` is supplied by `spanningLineStabilizer`
   (module `Langlands.GroupScheme.SpanningLineStabilizerProof`).
4. The remaining two inputs of the reduction are again `someBorelQuotientProper`
   and `borelConjugacy`.

All imported theorems are unconditional statements at the same universe `u`,
so the composition proves the target statement with no extra premise.

In outline, the imported proofs argue as follows. The reduction embeds the
supplied quotient `Q` in a projective space through a spanning representation
of `G` in which `B` is the stabilizer of the line of a basis vector `e_j`. Its
properness comes from the proper quotient by one Borel subgroup and conjugacy of
Borel subgroups. The core then gives, for each rational point `g` of `G`, a
linear form `w` with `w · ρ(g) e_j ≠ 0` whose line is stable under the rational
points of `U`. The chart lemma `exists_invariantAffineOpen_of_dualLines` (module
`Langlands.GroupScheme.FlagDualLineNeighbourhood`) turns the non-vanishing
locus of `w` in `Q` into the required affine open `V`. The torus splitting,
torus conjugacy and solvable fixed-point theorems are used inside the core: to
diagonalize the torus, for the Weyl step, and to find a `B`-stable line in the
dual representation. The paired Markdown of each imported module describes its
proof.

The hypotheses that `U` is connected and unipotent are not used by the
reduction.

## Provenance

This is the final composition for task `877d0194-f7d3-4c1e-8e72-e81d1a772c0c`.
The mathematics is J. S. Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`, Theorem 17.65 and the covering argument after
it (printed pp. 374-375), adapted to the Library's interfaces as explained in
`FlagInvariantAffineOpenCoverReduction.md`, `FlagCoreAssembly.md` and
`FlagCoreLinear.md`. The reduction, the chart lemma and the spanning helper
`MatrixRepresentation.exists_spanning_sameCoordinateLineStabilizer` behind
`spanningLineStabilizer` are by Worker 967. The dual-line core is by
Worker 1495. The other imported proofs come from their own Library tasks.
The proof uses only Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`).
