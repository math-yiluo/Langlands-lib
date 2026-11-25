# Base change and transport of ring structures

Module `StacksFrontier.RingTheory.BaseChangeTransport`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file gives algebra equivalences for composing base changes and for adjoining a root, and two transport results.

- For a tower of commutative rings K → F → E and a commutative K-algebra A, `Algebra.TensorProduct.cancelBaseChangeTower` identifies (A ⊗[K] F) ⊗[F] E with A ⊗[K] E as E-algebras, every action coming from the right factor.
- For a commutative R-algebra T and p in R[X], `AdjoinRoot.baseChangeAlgEquiv` identifies the base change of R[X] ⧸ (p) to T with T[X] modulo the image of p. The auxiliary `AdjoinRoot.ridAlgEquiv` moves the coefficients along T ⊗[R] R ≃ T.
- `IsFractionRing.of_ringEquiv_ringEquiv` transports `IsFractionRing S K` to `IsFractionRing R L` along ring isomorphisms R ≃ S and K ≃ L compatible with the algebra maps, for total rings of fractions.
- `isLocalHom_algebraMap_of_isIntegral` proves that an integral algebra map between commutative local rings is local: the maximal ideal of the target contracts to that of the source.

The module docstring lists as main results the values of `AdjoinRoot.baseChangeAlgEquiv` on the root and on coefficients; the file does not contain them.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | II 6.4.5.1 | `isLocalHom_algebraMap_of_isIntegral` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/BaseChangeTransport.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 9 declarations of the source file 6 are kept. The 3 left out are not needed by the results for which the extract is made: `AdjoinRoot.baseChangeAlgEquiv_tmul_of`, `AdjoinRoot.baseChangeAlgEquiv_tmul_root`, `AdjoinRoot.ridAlgEquiv_apply`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
