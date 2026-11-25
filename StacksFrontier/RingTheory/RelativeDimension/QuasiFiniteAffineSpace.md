# Quasi-finite maps from affine space near a prime

Module `StacksFrontier.RingTheory.RelativeDimension.QuasiFiniteAffineSpace`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a commutative R-algebra S of finite type and a prime 𝔮 of S at which `Algebra.relativeDimensionAt R 𝔮` is a natural number n, `exists_quasiFinite_mvPolynomial_away` gives g ∉ 𝔮 and an R-algebra map ψ from `MvPolynomial (Fin n) R` to `Localization.Away g` with `ψ.toRingHom.QuasiFinite`: Stacks 00QE at a prime of S. It is `quasiFinite_over_polynomial_of_relativeDimension` read at the point of the fibre spectrum attached to 𝔮.

Two lemmas make that translation. `relativeDimensionAt_eq_of_fiber` identifies `Algebra.relativeDimensionAt R 𝔮` with the root-namespace `relativeDimensionAt` at the point of Spec(κ(𝔭) ⊗[R] S), for 𝔭 the contraction of 𝔮, given by `PrimeSpectrum.preimageHomeomorphFiber`, and `comap_fiberMap_preimageHomeomorphFiber` shows that this point contracts to 𝔮 along `fiberMap`.

The conclusion records quasi-finiteness of ψ but not that ψ is of finite type. The module docstring states and sketches the form adapted to the prime, Stacks 0520, with f ∉ 𝔭 and the contraction of 𝔮S_g equal to (𝔭, x_{r+1}, …, x_n), together with a lemma on ideals of variables; neither is in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/RelativeDimension/QuasiFiniteAffineSpace.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 15 declarations of the source file 3 are kept. The 12 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
