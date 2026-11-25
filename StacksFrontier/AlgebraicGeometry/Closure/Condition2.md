# Flatness and a smooth fibre give smoothness at a point

Module `StacksFrontier.AlgebraicGeometry.Closure.Condition2`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a morphism of schemes `f : X ⟶ S` locally of finite presentation and a point `x` of `X`, the file proves one implication between characterizations of smoothness at `x`: condition (2), flatness of `𝒪_{S,f x} ⟶ 𝒪_{X,x}` plus smoothness at `x` of the fibre over `κ(f x)`, implies condition (1), smoothness of `f` at `x`.

- `formallySmooth_residueField_tensor_stalk`: if the fibre is smooth at `x` (`InfinitesimalLifting.SmoothAt`), then `κ(f x) ⊗_{𝒪_{S,f x}} 𝒪_{X,x}` is formally smooth over `κ(f x)`.
- `condition2_imp_condition1`: `Condition2 f x` implies `Condition1 f x`.

The proof writes the two stalks as localizations at primes of `Γ(S, V)` and of the finitely presented `Γ(S, V)`-algebra `Γ(X, U)`, for affine opens `V` and `U`, and applies a ring-theoretic criterion of another file.

## Watch for

`Condition1`, `Condition2` and `InfinitesimalLifting.SmoothAt` are the library's own definitions from other files. Only this one implication is proved here.

## References

Tag 01V9 and Tag 00TF. The table of references below gives the place in SGA (marked partial).

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 3 XV 1.1 | `condition2_imp_condition1` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Closure/Condition2.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
