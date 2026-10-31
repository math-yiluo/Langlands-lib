# Čech cohomology of graded modules commutes with finite products (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_ProjSpaceCech_GradedModule_nonempty_HEquiv_pi`. Its declarations live
in the namespace `P2MW.S_ProjSpaceCech_GradedModule_nonempty_HEquiv_pi`.

## Statement

`solution`: let `R` be a commutative ring, `ι` a finite type and `D : ι → ProjSpaceCech.GradedModule R n` a
family of graded modules over `R[X₀, …, Xₙ]`, with product `GradedModule.pi D`
(`Def_AlgebraicGeometry_ProjSpaceCechGradedModule`). Then for every `i` there is an `R`-linear equivalence
`GradedModule.H (GradedModule.pi D) i ≃ₗ[R] (∀ k, GradedModule.H (D k) i)` between the `i`-th Čech
cohomology of the product and the product of the `i`-th Čech cohomologies. The theorem module
`Theorems.Thm_ProjSpaceCech_GradedModule_nonempty_HEquiv_pi` states this as
`ProjSpaceCech.GradedModule.nonempty_HEquiv_pi` and proves it from `solution`.

## Proof outline

The proof is in the namespace `…ProjSpaceCech`.

1. **Linear-algebra helpers.** `GradedModule.piComm` swaps the two arguments of a double product, and
   `GradedModule.piSubmodEquiv` identifies `Submodule.pi Set.univ p` with `∀ k, p k`. Both are `rfl`
   equivalences.
2. **Sections.** The monomial action on the product is computed componentwise
   (`GradedModule.pi_monMul_apply`). `GradedModule.secPiProj D I k` maps the localized sections of the
   product over a chart intersection `I` to those of `D k`, and `GradedModule.secPiFwd` collects these maps.
   It commutes with the restriction maps (`GradedModule.secPiFwd_incl`). It is injective because a fraction
   killed by a monomial in each of the finitely many components is killed by the product of these monomials
   (`GradedModule.secPiFwd_injective`). It is surjective by putting finitely many fractions over a common
   denominator (`GradedModule.secPiFwd_surjective`). This gives `GradedModule.secPiEquiv`.
3. **Cochains.** `GradedModule.cochainPiEquiv` identifies the `i`-cochains of the product with the product of
   the `i`-cochains and intertwines the differential of the product with the componentwise differential
   `GradedModule.piAltd` (`GradedModule.cochainPiEquiv_comm`). Hence it maps cocycles onto the kernel and
   coboundaries onto the range of `piAltd` (`GradedModule.cochainPiEquiv_ker`, `GradedModule.cochainPiEquiv_range`),
   and these are the products of the componentwise kernels and ranges (`GradedModule.ker_piAltd`,
   `GradedModule.range_piAltd`).
4. **Cohomology.** `GradedModule.kerPiEquiv` is the induced equivalence on cocycles, and
   `GradedModule.kerPiEquiv_comap_range` shows that it carries coboundaries to the product of coboundaries.
   `GradedModule.HPiEquiv` is `kerPiEquiv` in degree `0`. In degree `j + 1` it is the induced equivalence of
   quotients followed by `Submodule.quotientPi`. `solution` is `⟨GradedModule.HPiEquiv D i⟩`.

## Provenance and licence

This file is a port of `P2M/Sol/S_ProjSpaceCech_GradedModule_nonempty_HEquiv_pi.lean` from the Anthropic Lean
formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (registered
literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in
`licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies.
Declaration names and namespaces are FLT's. The port makes only these changes:

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
  `open scoped _root_.N in`. No declaration, statement or proof step changed.
