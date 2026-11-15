# Proof of the canonical cuspidal eigenvalue

This module proves the published proposition
`Langlands.Aubert.General.RationalPointFamily.CanonicalRationalCuspidalEigenvalueStatement`
(module `CanonicalRationalTheorem17Targets`) at universes `u`, `v`:

`theorem canonicalRationalCuspidalEigenvalue :
  CanonicalRationalCuspidalEigenvalueStatement.{u, v}`.

The target is Aubert (1995), Théorème 1.7 (4). For an irreducible smooth
complex representation `A` of `G(k)` whose actual normalized Jacquet modules
at all proper standard subsets are zero, the canonical actual operator
satisfies `D [A] = (-1)^(number of simple roots) • [A]`. It is stated for every
connected reductive group over every nonarchimedean local field. The statement
module's Markdown describes the statement, its meaning and its provenance.
This file describes only the Lean proof.

The theorem proves the whole proposition. Like every target of that module,
the proposition is itself an implication from its two global dynamic
finite-length binders `hiFl : DynamicInductionFiniteLengthStatement` and
`hrFl : DynamicJacquetFiniteLengthStatement`. The proof keeps them as binders
of the proposition. It does not discharge them and adds no other hypothesis.

Authors: Worker 29, with Worker 3640 (Task 3640, block (vi)). Submitted by
Worker 432 for Task 6835 (`58e99db2-3edb-433a-a8ef-b4668aaa3af2`).

## Proof

The proof is a single term:

```
canonicalRationalCuspidalEigenvalue_of_rational.{u, v}
  rationalCuspidalEigenvalue.{u, v}
```

1. `rationalCuspidalEigenvalue : RationalCuspidalEigenvalueStatement.{u, v}`
   (module `RationalCuspidalEigenvalueProof`) is the published proof of the
   existing rational-point target. That target quantifies all structural
   premises.
2. `canonicalRationalCuspidalEigenvalue_of_rational`
   (module `CanonicalRationalTargetBridgesProof`, the published proof of
   Task 6316, `4320e0f3-a054-4148-bc31-69a2529b0d13`) proves
   `RationalCuspidalEigenvalueStatement.{u, v} →
   CanonicalRationalCuspidalEigenvalueStatement.{u, v}`. For the same field,
   group, maximal split torus and generic cocharacter, it instantiates the
   rational target at the canonical point topology with its published
   locally compact, nonarchimedean and Hausdorff instances, the published
   `standardCocharacter` and the relative root system
   `relativeRootSystem k G hG T i hi`. It supplies the published structural
   facts: closed unipotent radicals and parabolics, continuous Levi
   projections, and unipotent radicals that are limits of compact subgroups.
   It derives the rational target's per-subset finite-length premises from
   the canonical target's own `hiFl` and `hrFl`.

The universe arguments are passed explicitly, so both declarations are used
at exactly the universes of the conclusion.

All modules named are in `Langlands/Representation/Aubert/General/`.

## Dependency status

Every module this proof imports is in the Library (checked at Library commit
`2016a0d994180c702214a75514a08546aa930f07`). The statement module
`CanonicalRationalTheorem17Targets` is imported through
`CanonicalRationalTargetBridgesProof`. Against that Library the module
compiles with zero errors and zero warnings. The theorem has level parameters
`u` and `v` and uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
