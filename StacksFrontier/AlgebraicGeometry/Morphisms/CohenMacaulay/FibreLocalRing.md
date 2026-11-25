# Cohen–Macaulayness of fibre local rings

Module `StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreLocalRing`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file computes the local ring of an affine scheme-theoretic fibre at a point and compares Cohen–Macaulayness at corresponding fibre points under open restriction and isomorphism.

## Affine calculation

- For a commutative algebra T over R and a prime p of R, `affineFiberSchemeIso` identifies the fibre of Spec T ⟶ Spec R over p with the spectrum of κ(p) ⊗ᵣ T. For a prime q of T over p, `affineFiberPoint` gives the corresponding prime of that tensor product, and `affineFiberStalkRingEquiv` identifies the fibre stalk with the localization there.
- `affineFiberRingEquiv` identifies T localized at q and then quotiented by the extended ideal p with T/pT localized at the image of q. It accepts any model of the prime localization. `affineFiberPointRingEquiv` compares this calculation with localization in the tensor product.
- If every fibre of Spec T ⟶ Spec R is locally Noetherian, `affineFiber_cm_iff` equates Cohen–Macaulayness of the fibre stalk with maximal Cohen–Macaulayness of the localized fibre algebra as a module over itself. `affineFiberPoint_cm_iff_ring_locus` gives the equivalent test on the localization of T/pT.

## Transport between fibres

`localFiberCM_iff_sourceOpenImmersion` and `localFiberCM_iff_openTarget` preserve the Cohen–Macaulay condition on fibre stalks under open immersion of the source or target, respectively. `localFiberCM_iff_arrowIso` compares the conditions at corresponding points under an isomorphism of scheme arrows.

On spectra the calculation uses the pullback description of fibres and the compatibility of localization with quotients. The transport arguments use isomorphisms on stalks induced by open immersions and identify residue fields for an open immersion of targets.

The transport lemmas take local Noetherianity of the relevant fibres and local and Noetherian ring instances for the stalks. The arrow isomorphism lemma assumes through `hf` and `hg` that every fibre of `f` and of `g` is locally Noetherian, not only the fibres at the points concerned, and explicitly assumes local Noetherianity for the intermediate composite fibre through `hcomp`.

EGA II 1.5.4 (the affine fibre isomorphism is a special case).

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | II 1.5.4 | `affineFiberSchemeIso` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/CohenMacaulay/FibreLocalRing.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
