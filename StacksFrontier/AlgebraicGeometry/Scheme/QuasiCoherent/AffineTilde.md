# Associated sheaves under affine pullback

Module `StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a homomorphism `φ : R ⟶ S` of commutative rings, pullback along the induced map `Spec S ⟶ Spec R` acts on associated sheaves by extension of scalars, naturally in the module.

`pushforwardΓLinearEquiv` identifies global sections of the pushforward of any module sheaf on `Spec S` with its original global sections with scalars restricted along `φ`. The comparison is the identity on elements and assembles into the natural isomorphism `pushforwardΓIso`, whose naturality holds by definition.

`pullbackTildeIso` identifies the pullback of the sheaf associated to an `R`-module `M` with the sheaf associated to the tensor product `S ⊗[R] M`. It compares two left adjoints using `pushforwardΓIso` to identify their right adjoints. The file states nothing about this isomorphism on sections.

The module docstring also announces the pushforward of associated sheaves as restriction of scalars and normalizations of both isomorphisms on global sections; none of these is in the file.

## References

Stacks Project, Tag 01I9, for the affine pullback formula.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [01I9](https://stacks.math.columbia.edu/tag/01I9) | `pullbackTildeIso` | affine_pullback_tilde |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Scheme/QuasiCoherent/AffineTilde.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 11 declarations of the source file 3 are kept. The 8 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.isIso_pushforwardTildeNatTrans`, `AlgebraicGeometry.isIso_pushforwardTildeNatTrans_app`, `AlgebraicGeometry.pullbackTildeIso_hom_app_unit_toOpen`, `AlgebraicGeometry.pushforwardTildeIso`, `AlgebraicGeometry.pushforwardTildeIso_hom_app_toOpen`, `AlgebraicGeometry.pushforwardTildeNatTrans`, `AlgebraicGeometry.pushforwardTildeNatTrans_app_toOpen`, `AlgebraicGeometry.pushforwardTildeΓIso`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
