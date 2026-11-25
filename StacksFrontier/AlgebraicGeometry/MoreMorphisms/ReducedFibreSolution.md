# Solutions at generic points of fibres over a Dedekind base

Module `StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreSolution`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let `A` be a Dedekind domain with fraction field `K` and `f : X ⟶ Spec A` flat and locally of finite type with `X` normal. At a point `x` that is generic in its own fibre, over a nonzero prime of `A`, both `A_x` (the localization at the prime under `x`) and the stalk `O` of `X` at `x` are discrete valuation rings, the second an essentially finite type extension of the first. Elimination of ramification then gives a finite extension of `K` that is a solution for `A_x → O`, and one extension can serve finitely many points.

## Main definitions and results

- Supporting structures: `algebraLocalizationAtPrimeBase` (`K` as an `A_x`-algebra, with `isFractionRing_localizationAtPrimeBase`), `algebraStalkFractionRing` (`Frac O` as a `K`-algebra), and scalar-tower lemmas.
- `isDiscreteValuationRing_localizationAtPrimeBase`: `A_x` is a discrete valuation ring when the prime is nonzero.
- `isDiscreteValuationRing_stalk_of_mem_genericPoints`: `O` is a discrete valuation ring at such an `x`, via coheight one.
- `essFiniteType_stalkAlgebraOfSpecHom`, `injective_algebraMap_stalkFractionRing`: `O` is essentially of finite type over `A_x`, and `A_x → Frac O` is injective for flat `f`.
- `IsSolutionForStalk K f x hs hg K₁`: for finite `K₁/K`, there exists a base-change package `IntegralClosureBaseChange` for `A_x → O` and `K₁` (Tag 09EM) satisfying its `IsSolution` property, the formal smoothness of Tag 09EN(2).
- `exists_finite_extension_isSolution_stalk`: a finite `K₁/K` with `IsSolutionForStalk` exists at each such point.
- `exists_finite_extension_forall_isSolution_stalk`: for a finite family of such points, a single finite `K₁/K` is a solution at each.

## Proofs

Existence at one point is the library's elimination of ramification theorem (`Stacks.EliminateRamification.exists_finite_extension_isSolution`). For finitely many points the individual solutions are embedded into a common finite extension, and a finite extension of a solution is again a solution (`exists_isSolution_of_tower`).

## Watch for

- `IsSolutionForStalk` is the library's own predicate, and it depends on the proofs `hs`, `hg` as arguments.
- The index type of the finite family lies in `Type`, the lowest universe.

## References

Tags 09IL, 09II, 0GLR, 09EM, 09EN.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/MoreMorphisms/ReducedFibreSolution.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
