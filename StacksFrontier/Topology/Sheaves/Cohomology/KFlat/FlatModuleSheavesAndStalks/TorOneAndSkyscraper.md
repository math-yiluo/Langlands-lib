# Skyscraper presheaves of modules realizing a stalk module

Module `StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks.TorOneAndSkyscraper`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a point x of a ringed space X and a module N over the stalk ring O_{X,x}, the file builds a skyscraper presheaf of O_X-modules whose stalk at x is N.

- `OXModule.skyscraperObj x N U` is N, with O_X(U) acting by restriction of scalars along the germ map O_X(U) → O_{X,x}, when the open U contains x, and the zero module otherwise. `OXModule.skyscraperMap` gives the transition maps, built on opens containing x from the factorization of germs through restriction (`OXModule.structure_germ_comp`) and zero elsewhere. `OXModule.skyscraperMap_id` and `OXModule.skyscraperMap_comp` are the functoriality laws, and `OXModule.skyscraperPOM` assembles the presheaf of modules over `OXModule.ringSheaf X`.
- On opens containing x the underlying presheaf of abelian groups has value N and identity transition maps (`OXModule.skyscraperPOM_presheaf_obj_eq`, `OXModule.skyscraperPOM_presheaf_map_eq`), so its stalk at x is N as an abelian group: `OXModule.sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv`, which sends the germ of n to n by `OXModule.sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv_germ`.
- `OXModule.sheafify_skyscraperPOM_stalkIso_skyscraper` makes this an isomorphism of O_{X,x}-modules. Scalars are compared on a common neighbourhood through the germ formula `OXModule.skyscraperPOM_leg_smul` and the cast lemma `OXModule.cast_smul_restrictScalars`.

The lemmas `OXModule.restrictScalarsComp'App_hom_eqToHom` and `OXModule.restrictScalarsId'App_inv_eqToHom` identify Mathlib's change-of-scalars isomorphisms with casts; they serve the functoriality proofs.

Despite the prefix `sheafify_`, the two stalk isomorphisms concern the stalk of the presheaf `OXModule.skyscraperPOM` itself, not of its sheafification. Rings and modules share one universe, which is also the universe of the ringed space. The module docstring and the comments before the construction describe a Tor₁ criterion for flatness over a commutative ring and a horseshoe construction, which the file does not contain.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Topology/Sheaves/Cohomology/KFlat/FlatModuleSheavesAndStalks/TorOneAndSkyscraper.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 29 declarations of the source file 16 are kept. The 13 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
