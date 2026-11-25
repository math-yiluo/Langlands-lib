# Formal smoothness from flatness and a formally smooth fibre ring

Module `StacksFrontier.AlgebraicGeometry.Closure.FibreRing`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Two statements of commutative algebra used to show that flatness plus a smooth fibre gives smoothness at a point.

- `formallySmooth_of_formallySmooth_residueField_tensor`: let `S'` be a finitely presented `R'`-algebra, `q` a prime of `S'` over a prime `p` of `R'`, and `Rp`, `Sq` local rings that are localizations of `R'` at `p` and of `S'` at `q`, compatibly. If `Sq` is flat over `Rp`, `Rp ⟶ Sq` is local, and `κ(Rp) ⊗_{Rp} Sq` is formally smooth over `κ(Rp)`, then `Sq` is formally smooth over `Rp` (by a Mathlib lemma applied to `S'_p`).
- `formallySmooth_residueField_tensor_of_quotient`: for a local ring `R` and an `R`-algebra `B`, if `B ⧸ 𝔪_R B` is isomorphic, compatibly with the structure maps, to a ring formally smooth over `R ⧸ 𝔪_R`, then `κ(R) ⊗_R B` is formally smooth over `κ(R)`.

## Watch for

`Rp` and `Sq` are arbitrary models of the localizations (`IsLocalization.AtPrime`), so the first result applies directly to stalks.

## References

Tag 01V9 and Tag 00TF.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Closure/FibreRing.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
