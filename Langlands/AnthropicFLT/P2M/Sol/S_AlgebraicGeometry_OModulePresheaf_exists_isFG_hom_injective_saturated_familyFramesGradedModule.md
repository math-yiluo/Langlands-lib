# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Each FLT command `p2m_export "N" "a b …"` (from `P2M.Util`; it adds the aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) is replaced by the Lean command `export _root_.N (a b …)`, which adds the same aliases.
- `p2m_export` also exports from namespaces that contain only private declarations of this module (`P2mFamFG`), which Lean does not register as namespaces; Lean's `export` rejects them, so each of them is registered by an empty block `namespace N end N` right after the options.
- Compatibility edit for the project's Mathlib: in the definition of `xAlg`, the proof `by rintro _ ⟨l, rfl⟩ _ ⟨l', rfl⟩; exact (Mf ι hθ).xMul_comm l l'` of the hypothesis of `Algebra.isMulCommutative_adjoin` becomes `by rintro _ ⟨l, rfl⟩ _ ⟨l', rfl⟩ _; exact (Mf ι hθ).xMul_comm l l'`. In this Mathlib that hypothesis is `s.Pairwise Commute`, which has an extra premise `x ≠ y`; the added `_` introduces and ignores it. The definition is otherwise unchanged.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule`.

Proof (namespace `P2mFamFG`), with `Mf ι hθ` the graded module `familyFramesGradedModule ι G θ hθ` over
`B = A[Y_1, …, Y_s]`.

- Constants: over the chart `ι⁻¹ D₊(X_l)` (`pullbackChart ι l`) the scalars from `A` come through
  `Proj.awayToSection` (`algebraMap_eq_app_awayToSection`); for `ι` a closed immersion every section of the chart
  is an `A`-combination of monomials in the frame units `u_{l i}` (`exists_eq_sum`, via `awayMkHom`); the basic open
  of `u_{ji}` in the chart is the overlap (`basicOpen_frameUnit`, `proj_basicOpen_awayToSection_ratio`).
- Algebra: `uprod ι j c = ∏_l u_{jl}^{c_l}` is multiplicative and satisfies the twisted cocycle rule
  (`uprod_add`, `uprod_single`, `uprod_cocycle`), so it shifts the `FramesCompat` degree by `∑ c`
  (`framesCompat_uprod_smul`); `FramesCompat` is closed under subtraction and affine homomorphisms
  (`framesCompat_sub`, `framesCompat_app`). Lemmas on `FamilyFrames.single` (`single_add'`, `single_C_smul`,
  `sum_apply'`, `single_zero'`, `single_congr`, `monMul_single`, `xMul_pow_single`, `yEnd_single`,
  `single_mem_grade_iff`). `xAlg` is the `B`-algebra map `B[X_0, …, X_r] → End_B(Mf)` sending `X_l` to `xMul l`
  (`xAlg_X`, `xAlg_C`, `xMul_pow_eq_xAlg`, `xAlg_prod`, `xAlg_monomial`, `xAlg_comm_xMul_pow`), mapping the
  free degree-`n'` part and degree-`e` elements into degree `e + n'` (`xAlg_mem_grade`, with `sum_eq_degree`,
  `freeGrade_mul_mem`).
- Presentation: `Gens` records degree-`d₁` compatible chart families `sg a` (`a < m`) of `G 0` generating every
  chart. `F` is the free graded module `⊕_a B[X](-d₁)` (Library `GradedModule.pi`, `GradedModule.FD`;
  `mem_F_grade_iff`, `F_xMul_apply`), `gen a` the element `single d₁ 0 (sg a)` of `Mf` (`gen_mem`), and
  `Φlin p = ∑_a xAlg (p a) (gen a)` a graded homomorphism `ΦHom` (`Φlin_apply`, `Φlin_mem_grade`, `Φlin_xMul`,
  `Φlin_xMul_pow`, `Φlin_xAlg`). Its kernel `K` is `xMul`-stable (`K_stable`), `D = F / K` has the finite
  presentation `pres`, and the induced `hHom : D → Mf` is injective (`hHom_injective`, `hHom_mkQ`).
- Saturation: `Sat l e f` says that `X_l^N f` is in the image of `F` in degree `e + N` for some `N`
  (equivalently all large `N`, `sat_iff_le`). It is closed under `0`, `+`, `B`-scalars, finite sums, `xAlg`,
  monomials, `xMul` powers and `yEnd` (`sat_zero`, `Sat.add`, `Sat.smul`, `Sat.sum`, `Sat.xAlg`, `Sat.monMul`,
  `Sat.xMul_pow`, `Sat.yEnd`), and can be checked after multiplying by `X_l^n` (`Sat.of_xMul_pow`). For `G k`
  quasi-coherent, a compatible family vanishing on chart `l` is saturated (a power of `u_{jl}` kills it,
  `sat_single_of_apply_eq_zero`), so saturation of `single n k g` depends only on `g l` (`sat_single_congr`).
- Generation: `GoodAt l k z` says that `z ∈ G k(chart l)` is the `l`-component of a saturated compatible family.
  It holds for `0` and is closed under sums, multiplication by `A`-multiples of `uprod`, hence (closed
  immersion) by arbitrary chart sections, and under every `θ m k` (`goodAt_zero`, `framesCompat_pow_smul`,
  `GoodAt.bump`, `GoodAt.add`, `GoodAt.sum`, `GoodAt.smul_const_uprod`, `GoodAt.smul_fun`, `GoodAt.app`). The
  generators are good (`goodAt_gen`); since the `θ m` generate each level from the previous one, every element of
  every `G k(chart l)` is good (`goodAt_all`, induction on `k`). Hence every compatible `single` and, decomposing
  homogeneous elements into finitely many levels (`eq_sum_single`), every homogeneous element of `Mf` is
  saturated (`sat_single`, `sat_of_mem_grade`).
- `main`: the ported theorem `exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top` (Serre's
  theorem A for `G 0`) gives generators `𝔤`; then `D hθ 𝔤`, `pres`, `hHom` and `sat_of_mem_grade` give the claim.
  `solution` is `P2mFamFG.main`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.algebraMap_eq_app_awayToSection`
- def `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.awayMkHom`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.exists_eq_sum`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.proj_basicOpen_awayToSection_ratio`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.basicOpen_frameUnit`
- abbrev `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.Mf`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.res_smul'`
- def `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.uprod`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.uprod_add`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.uprod_single`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.uprod_cocycle`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.framesCompat_uprod_smul`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.framesCompat_sub`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.framesCompat_app`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.single_add'`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.single_C_smul`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.sum_apply'`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.single_zero'`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.single_congr`
- private theorem `P2mFamFG.monMul_single`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.xMul_pow_single`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.yEnd_single`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.single_mem_grade_iff`
- private def `P2mFamFG.xAlg`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.xAlg_X`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.xAlg_C`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.xMul_pow_eq_xAlg`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.xAlg_prod`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.xAlg_monomial`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.xAlg_comm_xMul_pow`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.sum_eq_degree`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.xAlg_mem_grade`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.freeGrade_mul_mem`
- structure `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.Gens`
- abbrev `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.F`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.mem_F_grade_iff`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.F_xMul_apply`
- def `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.gen`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.gen_mem`
- def `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.Φlin`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.Φlin_apply`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.Φlin_mem_grade`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.Φlin_xMul`
- def `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.ΦHom`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.Φlin_xMul_pow`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.Φlin_xAlg`
- abbrev `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.K`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.K_stable`
- def `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.D`
- def `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.pres`
- def `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.hHom`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.hHom_injective`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.hHom_mkQ`
- def `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.Sat`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.sat_iff_le`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.sat_zero`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.Sat.add`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.Sat.smul`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.Sat.sum`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.Sat.xAlg`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.Sat.monMul`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.Sat.xMul_pow`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.Sat.yEnd`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.Sat.of_xMul_pow`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.sat_single_of_apply_eq_zero`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.sat_single_congr`
- def `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.GoodAt`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.goodAt_zero`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.framesCompat_pow_smul`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.GoodAt.bump`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.GoodAt.add`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.GoodAt.sum`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.GoodAt.smul_const_uprod`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.GoodAt.smul_fun`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.GoodAt.app`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.goodAt_gen`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.goodAt_all`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.sat_single`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.eq_sum_single`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.sat_of_mem_grade`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.P2mFamFG.main`
- theorem `P2mFamFG.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafFamilyFramesGradedModule` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top` (same contribution).
Other imports: `Mathlib`.
