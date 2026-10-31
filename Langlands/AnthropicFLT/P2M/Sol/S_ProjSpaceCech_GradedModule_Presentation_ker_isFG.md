# The kernel of a presentation of a graded module is finitely generated (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_ProjSpaceCech_GradedModule_Presentation_ker_isFG`. Its declarations
live in the namespace `P2MW.S_ProjSpaceCech_GradedModule_Presentation_ker_isFG`.

## Statement

`solution`: let `R` be a noetherian ring, `D : ProjSpaceCech.GradedModule R n`, and `σ` a presentation of
`D` (`Def_AlgebraicGeometry_ProjSpaceCechGradedModule`). Then the kernel `σ.ker`, as a graded module, has a
presentation itself (`GradedModule.IsFG σ.ker`). This is Hilbert's basis theorem for graded modules over
`S = R[X₀, …, Xₙ]`. The theorem module `Theorems.Thm_ProjSpaceCech_GradedModule_Presentation_ker_isFG`
states this as `ProjSpaceCech.GradedModule.Presentation.ker_isFG` and proves it from `solution`.

## Proof outline

The proof is in the namespace `…ProjSpaceCech`. Write `F = σ.F`, a finite sum of shifted copies of `S`, and
`K = σ.K` for the kernel of the presentation map.

1. **`S`-module structures.** The scoped instances `GradedModule.F_module`, `GradedModule.F_scalarTower`,
   `GradedModule.FD_module` and `GradedModule.ker_module` make `F` an `S`-module, on which `xMul j` is
   multiplication by `Xⱼ` (`GradedModule.F_xMul_eq_smul`). `K` is stable under `S`
   (`GradedModule.K_smul_stable`).
2. **The graded part of the kernel.** `GradedModule.Kgr` is the sum over `d` of `grade d ∩ K`, the elements
   of `K` that are sums of homogeneous elements of `K`. It is stable under each `xMul j`
   (`GradedModule.Kgr_xMul_stable`), hence an `S`-submodule (`GradedModule.KgrS`).
3. **Homogeneous components.** `GradedModule.mem_F_grade` describes the grades of `F` componentwise, and
   `GradedModule.freeGrade_smul_mem_grade` says multiplication by a homogeneous polynomial of degree `a`
   raises degrees by `a`. `GradedModule.FProj d` is the projection of `F` to its degree-`d` part
   (`GradedModule.FProj_apply`). On an element of degree `e` it is the identity if `d = e` and zero
   otherwise (`GradedModule.FProj_apply_of_mem_grade`).
4. **Finite generation** (`GradedModule.Presentation.ker_isFG'`). `S` is noetherian (Hilbert's basis
   theorem), so `F` is a noetherian `S`-module and `KgrS` has finitely many generators. Decompose each
   generator into its homogeneous pieces in `K`. These finitely many homogeneous elements `pv t`, of degrees
   `de t`, define a graded map from `⨁ₜ S(−de t)` to `F` that lands in `σ.ker` and commutes with each
   `xMul j`. It is surjective in each degree: an element `m` of degree `d` in `K` is an `S`-combination
   `∑ cₜ pv t`, and projecting to degree `d` (`FProj`) replaces each `cₜ` by its homogeneous component of
   degree `d − de t`.

## Provenance and licence

This file is a port of `P2M/Sol/S_ProjSpaceCech_GradedModule_Presentation_ker_isFG.lean` from the Anthropic
Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026
Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE`
and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist` and
  `Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule` are renamed to
  `Langlands.AnthropicFLT.Definitions.*`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false` (the file
  then raises the heartbeat limits further itself, as in FLT);
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect: each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same
  names, each `p2m_open "N"` becomes `open _root_.N`, and each `p2m_open_scoped "N" in` becomes
  `open scoped _root_.N in`. Each `p2m_reactivate` becomes an `open scoped` of
  `P2MW.S_ProjSpaceCech_GradedModule_Presentation_ker_isFG.ProjSpaceCech.GradedModule` (and, at the end,
  also of `P2MW.S_ProjSpaceCech_GradedModule_Presentation_ker_isFG.ProjSpaceCech`). It re-activates the
  scoped instances of step 1, which belong to that namespace. No declaration, statement or proof step
  changed.
