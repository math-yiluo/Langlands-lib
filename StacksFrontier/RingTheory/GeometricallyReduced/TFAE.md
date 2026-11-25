# Test fields for geometric reducedness

Module `StacksFrontier.RingTheory.GeometricallyReduced.TFAE`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a commutative algebra over a field, reducedness after every field extension can be detected after adjoining pth roots, after extending to a perfect closure, or after extending to an algebraic closure.

`Algebra.isGeometricallyReduced_tfae`, proved by `Stacks.GeometricallyReduced.TestFields.solution`, gives six equivalent conditions for a commutative k-algebra S over a field k of exponential characteristic p.

1. k′ ⊗ₖ S is reduced for every finite purely inseparable extension k′/k.
2. The base change to `AdjoinPthRoots k` is reduced.
3. The base change to a specified perfect closure of k is reduced.
4. The base change to a specified algebraic closure of k is reduced.
5. L ⊗ₖ S is reduced for every field extension L/k in the universe of k.
6. S satisfies Mathlib’s `Algebra.IsGeometricallyReduced` over k.

`Stacks.GeometricallyReduced.TestFields.isReduced_tensorProduct_fractionRing_mvPolynomial` gives reducedness of the base change of a reduced k-algebra to a rational function field in any set of variables. Independently, `Stacks.LocalHom.isLocalHom_of_isIntegral` proves that an integral algebra map between commutative local rings is local.

The proof for finite purely inseparable tests reduces to finitely generated extensions, passes to a separably generated extension after a finite purely inseparable base change, then descends reducedness along an injection. The pth-root test uses localizations at minimal primes and a separability criterion for their fields.

The first and fifth tests quantify in the universe of k. The two closures are given abstractly via `IsPerfectClosure` and `IsAlgClosure` and have independent universes. `AdjoinPthRoots k` uses the Frobenius algebra structure for the pth-root extension.

The first five conditions are Tag 030V, with the Mathlib predicate added as condition (6). The auxiliary ascent and detection results cite EGA 0 23.1.7, EGA IV 4.3.5, EGA IV 4.3.6, EGA IV 4.6.16 and EGA IV 7.3.16.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [030V](https://stacks.math.columbia.edu/tag/030V) | `isGeometricallyReduced_tfae` | The source's five conditions in its order, with its definition of geometric   reducedness spelled out as item (5), plus item (6), Mathlib's `Algebra.IsGeometricallyReduced`;   `k^{1/p}` is `AdjoinPthRoots k`, and the perfect and algebraic closures are taken abstractly, as   `IsPerfectClosure` and `IsAlgClosure`. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 23.1.7 | `isReduced_tensorProduct_of_isSeparablyGenerated` | partial |
| EGA | IV 4.3.5 | `isReduced_tensorProduct_of_isSeparablyGenerated` | special case |
| EGA | IV 4.3.6 | `isReduced_tensorProduct_of_isSeparablyGenerated` | special case |
| EGA | IV 4.6.16 | `isReduced_tensorProduct_of_forall_finiteDimensional_isPurelyInseparable` | special case |
| EGA | IV 7.3.16 | `isReduced_tensorProduct_of_forall_finiteDimensional_isPurelyInseparable` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/GeometricallyReduced/TFAE.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 5 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
