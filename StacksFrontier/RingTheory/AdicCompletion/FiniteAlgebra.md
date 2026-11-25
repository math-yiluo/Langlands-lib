# Completions of finite algebras and fibres

Module `StacksFrontier.RingTheory.AdicCompletion.FiniteAlgebra`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file compares adic completions along a local homomorphism and splits the base change of a finite algebra to a completed local ring into its completed local factors. All rings are commutative.

## Local homomorphisms

`AdicCompletion.nonempty_algEquiv_map_and_finite` applies to a local map (R, 𝔪) → (S, 𝔫) with 𝔪 finitely generated and S/𝔪S finite as an R-module. It gives existence of an S-algebra isomorphism between the 𝔫-adic and 𝔪S-adic completions of S. It also gives finiteness over the 𝔪-adic completion of R of the completion of the R-module S along 𝔪.

The finite fibre is Artinian, so a power of 𝔫 is contained in 𝔪S and the two filtrations are cofinal. Finiteness of the completed module follows from the finite-reduction criterion for a separated module over a precomplete ring.

Of the two maximal ideals, only 𝔪 is assumed finitely generated. The two conclusions use the same quotient tower via the extended ideal on the ring S and via the 𝔪-action on the R-module S, respectively.

## Product over primes

`AdicCompletion.nonempty_algEquiv_pi_primesOver` assumes R is Noetherian, S is module-finite over R, and p is a prime of R. It gives an S-algebra isomorphism, under `Nonempty`, from the tensor product over R of S with the maximal-ideal completion of Rₚ to the product of the maximal-ideal completions of S_q over the primes q of S lying over p. The localizations Rₚ and S_q are supplied as rings with the corresponding localization and local-ring instances.

The proof localizes S over Rₚ, identifies completion with the tensor product using the finite-module comparison, and takes the compatible Artinian product decompositions of the quotients by powers of the extended maximal ideal. The local comparison above identifies each resulting factor with the completion at its own maximal ideal. The final statement identifies the outer terms of the product formula, with the completion of the localized algebra used in the proof.

## References

The local comparison is Tag 0394 and the product formula is Tag 07N9. The file also cites Tag 0319, Tag 031D, Tag 05GG, Tag 00MA, Tag 00JB, and Tag 00KJ. The related references are EGA 0 7.2.12, EGA I 6.2.2, EGA 0 7.3.3, EGA 0 7.7.8, SGA 1 I 2.1, and SGA 3 VIIB 0.1.1.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0394](https://stacks.math.columbia.edu/tag/0394) | `AdicCompletion.nonempty_algEquiv_map_and_finite` | Stated without the source's finite generation of `n`, which no step needs; the \ `m`-adic completion of `S` appears as a completion along the ideal `mS` of `S` in the first \ conjunct and along `m` in the second. See the module docstring. |
| [07N9](https://stacks.math.columbia.edu/tag/07N9) | `AdicCompletion.nonempty_algEquiv_pi_primesOver` | The source's middle term `(S_p)^∧` is Mathlib's \ `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian` over `Rₚ`; the two outer terms are \ identified here. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 7.2.12 | `finite_adicCompletion` | special case |
| SGA | 1 I 2.1 | `AdicCompletion.nonempty_algEquiv_map_and_finite` | (i) => (iii) |
| EGA | I 6.2.2 | `bijective_algebraMap_pi_of_isArtinianRing` | affine, special case |
| SGA | 3 VIIB 0.1.1 | `bijective_algebraMap_pi_of_isArtinianRing` | partial |
| EGA | I 6.2.2 | `bijective_algebraMap_pi_quotient` | affine, special case |
| SGA | 3 VIIB 0.1.1 | `bijective_algebraMap_pi_quotient` | partial |
| EGA | 0 7.3.3 | `bijective_ofTensorAlgHom` | special case |
| EGA | 0 7.7.8 | `bijective_ofTensorAlgHom` | B = Â |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/AdicCompletion/FiniteAlgebra.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 8 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
