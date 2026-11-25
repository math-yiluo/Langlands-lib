# Finite type under pullback of module sheaves

Module `StacksFrontier.Topology.Sheaves.Modules.FiniteType`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Pullback along a morphism f from X to Y of ringed spaces carries locally finitely generated module sheaves to locally finitely generated module sheaves.

In `AlgebraicGeometry.SheafOfModules`, `siteRestrict` restricts a module sheaf to an open subspace, and `siteRestrictAdjunction` makes this restriction left adjoint to pushforward along the open immersion. The comparison `overFunctorIsoSiteRestrict` identifies restriction to the slice site over an open with restriction to the open subspace after transporting along the site equivalence. The isomorphism `overFunctorIsoPullback` then identifies this restriction with pullback along the open immersion by uniqueness of left adjoints.

In `Stacks.SheafOfModules`, `openPreimageFactorization` gives the induced morphism from f⁻¹V to V for any open V of Y, together with its commuting square. The isomorphism `modulePullbackOpenPreimageIso` identifies restriction of the pullback to f⁻¹V with pullback of the restriction to V along that induced morphism. The construction `modulePullbackGeneratingSections` pulls back a family of global generators using that pullback is a left adjoint and carries the unit module to the unit module.

The instance `AlgebraicGeometry.SheafOfModules.pullback_isFiniteType` starts with local generators witnessing Mathlib's `IsFiniteType` on Y. The proof pulls back the cover and transports the generators on each member through the restriction comparisons. The same finite index set of generators works on the corresponding preimage open. Finiteness is required on each local family of generators.

Reference for preservation of finite type is Tag 01B6.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [01B6](https://stacks.math.columbia.edu/tag/01B6) | `pullback_isFiniteType` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Topology/Sheaves/Modules/FiniteType.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
