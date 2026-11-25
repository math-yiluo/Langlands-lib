# Fibres and base change

Module `StacksFrontier.RingTheory.LocalRing.ResidueField.FiberBaseChange`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Suppose a pushout of commutative rings, expressed by `Algebra.IsPushout`, presents S′ as the base change of S from R to R′. For primes p of R and p′ of R′, the file compares the respective fibres over their residue fields.

`Ideal.Fiber.baseChangeAlgEquiv` identifies the scalar extension of κ(p) ⊗_R S to κ(p′) with the fibre κ(p′) ⊗_R′ S′ as κ(p′)-algebras. `Ideal.Fiber.baseChangeAlgebra` transports the map z ↦ 1 ⊗ z across this equivalence. The map extends S → S′, and `Ideal.Fiber.isPushout_baseChange` proves that the square of fibres is a pushout. The comparison cancels successive scalar extensions and interchanges tensor factors.

The residue field extension is supplied directly as a κ(p)-algebra structure on κ(p′) with its scalar tower over R. The fibre algebra structure and the tower `Ideal.Fiber.isScalarTower_baseChange` must be installed locally to use the pushout theorem.

The applications cited concern smoothness (Tag 02UQ), complete intersections (Tag 00SI), and Cohen–Macaulayness (Tag 00RJ) under field extension.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/LocalRing/ResidueField/FiberBaseChange.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 7 declarations of the source file 6 are kept. The 1 left out are not needed by the results for which the extract is made: `Ideal.Fiber.algebraMap_baseChange_includeRight`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
