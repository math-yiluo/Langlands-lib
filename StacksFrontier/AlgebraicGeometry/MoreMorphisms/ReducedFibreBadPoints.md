# One finite extension for the bad points of all nongeneric fibres

Module `StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreBadPoints`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let `A` be a Dedekind domain with fraction field `K`, and `f : X ⟶ Spec A` flat, quasi-compact and locally of finite type with `X` normal. A point is bad if it lies outside the smooth locus of `f`, is a generic point of an irreducible component of its fibre, and lies over a nonzero prime.

- `exists_finite_extension_forall_isSolution_stalk_of_dense_open_smooth`: if a dense open `U` of the generic fibre is smooth over the residue field of the generic point, one finite extension `K₁/K` satisfies `IsSolutionForStalk` for `A_x → 𝒪_(X,x)` at every bad point `x`.
- `isSolutionForStalk_congr`: the predicate transports along equality of points.

The density hypothesis makes the bad locus finite (Tag 054X); it is enumerated by `Fin n` and one extension serves the whole family (Tags 09II, 0GLR).

This is the second and third paragraphs of the proof of Tag 09IL, given an already available dense smooth open; it is not the full theorem. The nonzero-prime condition is a hypothesis of the conclusion.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/MoreMorphisms/ReducedFibreBadPoints.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
