# Normality of directed unions, polynomial rings and étale algebras

Module `StacksFrontier.RingTheory.GeometricallyNormal.TFAE`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file proves three properties of the library's normality predicate `IsNormalRing`, which requires every prime localization to be an integrally closed domain: it passes to directed unions and to polynomial rings in any number of variables, and it ascends along étale maps.

- `isNormalRing_of_directedUnion`: a commutative ring R covered by a monotone family of normal subrings, indexed by a nonempty directed preorder, is normal. The proof identifies R with the direct limit of the subrings and applies `directLimit_isNormalRing`.
- `isNormalRing_mvPolynomial`: a polynomial ring in an arbitrary set of variables over a normal ring is normal. Finitely many variables are handled by induction from the one-variable case `polynomial_ring_normal`, and the general case is the directed union of the subrings of polynomials in finitely many of the variables.
- `IsNormalRing.of_etale_of_isDomain`: an étale algebra S over an integrally closed domain D is a normal ring. S embeds into S ⊗_D Frac D, which is étale and finite over the field Frac D, hence reduced and Artinian; so S is reduced, S ⊗_D Frac D is its total ring of fractions and S has finitely many minimal primes. S is integrally closed in it because integral closure commutes with smooth base change, with `TensorProduct.exists_algebraMap_eq_toIntegralClosure` as the step on elements. Lemma 030C turns these facts into normality.
- `IsNormalRing.of_localization_atPrime_tensorProduct`: an R-algebra S is normal if R_𝔭 ⊗_R S is normal for every prime 𝔭 of R.
- `IsNormalRing.of_etale`: an étale algebra over a normal ring is normal, by the two previous results.

Both module docstrings are about the theorem that normality of k′ ⊗ₖ A for every field extension k′/k is detected by the finite purely inseparable extensions, or by a perfect closure of k (Tag 037Z), and describe its proof. That theorem and the lemmas of its proof are not in this file; the sections named after them near the end are empty.

The polynomial and directed-union results are Lemma 00H1 and Lemma 037D in the forms the file uses, and the étale ascent is a case of Tag 033C.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 7.5.3 | `IsNormalRing.of_etale_of_isDomain` | (vi), special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/GeometricallyNormal/TFAE.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 23 declarations of the source file 9 are kept. The 14 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above; the source's 10 others belong to declarations left out.
