# Closed subschemes of projective space have finite Čech cohomology of the structure sheaf (proof)

Module
`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj`.
Its declarations live in the namespace
`P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj`.

## Statement

`solution`: let `A` be a noetherian ring, `n : ℕ` and
`ι : W ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)` a closed immersion into `ℙⁿ_A`. Then the
structure sheaf of `W`, as the `A`-module presheaf `OModulePresheaf.unit (ι ≫ ProjSpace.π A n)`, has finitely
generated Čech cohomology in every degree for the pullback `ProjSpace.stdCoverPullback ι` of the standard
affine cover of `ℙⁿ_A` (`CechFinite`, `Def_AlgebraicGeometry_OrderedAffineCoverCech`; the cover is from
`Def_AlgebraicGeometry_ProjSpaceCover`). The theorem module
`Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj` states this as
`AlgebraicGeometry.OModulePresheaf.cechFinite_unit_of_isClosedImmersion_proj` and proves it from `solution`.

## Proof outline

The proof is in the namespace `…AlgebraicGeometry.ProjSpace.ClosedImmCech`. It identifies the Čech complex of
`O_W` with the graded Čech complex of the homogeneous coordinate ring `S/J` of `W`, where `S = A[X₀, …, Xₙ]`,
and applies the finiteness theorem for finitely generated graded modules.

1. **Module structures** (section `File8`). `canonicalAlg`, `moduleΓ` and `resLinearMap` make the sections of
   `W` into `A`-modules through `ι ≫ π` and the restriction maps into `A`-linear maps.
2. **Opens of the cover.** `idxEquiv` identifies the indices of the pulled-back cover with
   `ProjSpaceCech.Idx n i`. The intersection over an index `s` is the preimage of `D₊(∏_{j ∈ img s} Xⱼ)`
   (`finsetInf_basicOpen`, `altOpen_eq`).
3. **The ideal of `W`.** `testAt d j m` is the image on `ι⁻¹ D₊(Xⱼ)` of the degree-0 fraction `m / Xⱼᵈ`, for
   `m` homogeneous of degree `d`. `J` is the submodule spanned by the homogeneous `m` with `testAt d j m = 0`
   for all `j`. It is stable under multiplication by each `Xₖ` (`J_xMul_stable`, `J_monMul_stable`), so
   `Dι = S/J` is a graded module (`ProjSpaceCech.GradedModule.quot`), with quotient map `mkQHom`. A
   homogeneous element lies in `J` exactly when all its tests vanish (`mem_J_homogeneous`). `Dι` is a quotient
   of `S`, hence finitely generated (`GradedModule.IsFG`, `Dι_isFG`).
4. **Sections over chart intersections.** For a nonempty `I`, `secAux` sends a fraction `m / X^a` of the free
   module, with support of `a` in `I`, to the section of `W` over `ι⁻¹ D₊(∏_{j ∈ I} Xⱼ)` given by the degree-0
   fraction obtained after padding the denominator to a power of `∏_{j ∈ I} Xⱼ` (`pad`, `testAtI`,
   `secAuxNum_mem`). It respects the fraction relation, addition and the `A`-action (`secAux_wellDef`,
   `secAux_add`, `secAux_smul`; `canonicalAlg_eq` matches the two `A`-algebra structures), giving the linear
   map `freeSec`. `freeSec` is surjective because `ι` is a closed immersion and the chart is affine
   (`freeSec_surjective`). Its kernel is the kernel of the map to the sections of `Dι`: `freeSec_ker_le` uses
   that a section vanishing on `ι⁻¹ D₊(∏ Xᵢ)` is killed on each `ι⁻¹ D₊(Xⱼ)` by a power of `∏ Xᵢ`
   (`proj_basicOpen_awayMk` computes the relevant basic open), and `freeSec_ker_ge` uses
   `testAtI_eq_zero_of_mem_J`. Hence `quotSecEquiv`: the sections of `Dι` over `I` are isomorphic to the
   sections of `W` over `ι⁻¹ D₊(∏_{j ∈ I} Xⱼ)`, compatibly with restrictions (`secAux_face`,
   `quotSecEquiv_face`).
5. **Cochains and cohomology.** `chainEquiv` (built from `chainFwd` and `chainBwd`) is an `A`-linear
   equivalence between the graded Čech cochains of `Dι` and the Čech cochains of `O_W`. It commutes with the
   differentials (`chainEquiv_comm`), so it restricts to cocycles (`chainEquivKer`) and induces isomorphisms
   on cohomology. `ProjSpaceCech.GradedModule.finite_cohomology_of_isFG`
   (`Theorems.Thm_ProjSpaceCech_GradedModule_finite_cohomology_of_isFG`) applied to `Dι` gives finiteness in
   positive degrees (`gradH_altHF_finite`) and in degree `0` (`closedImm_allFinite`). `solution` is
   `closedImm_allFinite ι`.

## Provenance and licence

This file is a port of
`P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic,
PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and
`ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_ProjSpaceCover`,
  `Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule` and
  `Theorems.Thm_ProjSpaceCech_GradedModule_finite_cohomology_of_isFG` are renamed to the corresponding
  `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false` (the file then
  raises the heartbeat limits further itself, as in FLT);
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. Each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names.
  Each `p2m_open` becomes an `open` of the same namespaces, written with `_root_.` where needed and omitting a
  `P2MW`-prefixed namespace that does not exist yet at that point. No declaration, statement or proof step
  changed.
