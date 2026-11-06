# `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafFamilyFramesGradedModule`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_AlgebraicGeometry_OModulePresheafFamilyFramesGradedModule.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- Compatibility edit for the project's Mathlib: in the definition of `polyEnd`, the proof `by rintro _ ⟨m, rfl⟩ _ ⟨m', rfl⟩; exact yEnd_mul_comm hθ m m'` of the hypothesis of `Algebra.isMulCommutative_adjoin` becomes `by rintro _ ⟨m, rfl⟩ _ ⟨m', rfl⟩ _; exact yEnd_mul_comm hθ m m'`. In this Mathlib that hypothesis is `s.Pairwise Commute`, which has an extra premise `x ≠ y`; the added `_` introduces and ignores it. The definition is otherwise unchanged.

## Content

Let `A` be a commutative ring, `ι : P ⟶ ℙ^r_A = Proj A[X_0, …, X_r]` a morphism and `q : P ⟶ Spec A`. This
module builds, from a sequence `G : ℕ → OModulePresheaf q` of FLT presheaves of modules, a graded module over a
polynomial ring in the sense of the Library structure `ProjSpaceCech.GradedModule`:

- `FramesCompat ι F d t` (for a family `t j ∈ F(ι⁻¹ D₊(X_j))` of chart sections) is the degree-`d` twisted gluing
  condition `t j = u_{jl}^d · t l` on the overlaps, with `u_{jl} = ProjSpace.frameUnit ι j l` (`framesCompat_iff`);
  it is closed under `0`, `+`, `A`-scalars, and multiplying by `u_{j l₀}` raises `d` by one
  (`FramesCompat.zero`, `.add`, `.smul`, `.frameUnit_smul`).
- `FamilyFrames ι G` is the `A`-module of all families `f e k j ∈ G k (ι⁻¹ D₊(X_j))` indexed by a degree `e : ℤ`,
  a level `k : ℕ` and a chart `j` (pointwise operations; `zero_apply`, `add_apply`, `neg_apply`, `sub_apply`,
  `smul_apply`, `ext`). `xEnd l` shifts the degree by one and multiplies chart `j` by `u_{jl}` (`xEnd_apply`);
  these commute (`xEnd_comm`).
- `IsHomogeneousElem ι G e f` says that `f` is concentrated in degree `e`, vanishes if `e < 0`, satisfies
  `FramesCompat` in degree `e` at every level, and has only finitely many nonzero levels
  (`isHomogeneousElem_iff`); it is preserved by `0`, `+`, scalars and `xEnd` (raising the degree), and
  `FamilyFrames.single e k t` (the family `t` placed in degree `e` and level `k`; `single_apply_self`,
  `single_apply_of_ne_degree`, `single_apply_of_ne_level`) is homogeneous iff `t` satisfies the condition
  (`isHomogeneousElem_single_iff`).
- Given affine-indexed maps `θ m k : AffHom (G k) (G (k+1))` for `m : Fin s`, `yEnd m` raises the level by one by
  applying `θ m` on charts (`yEnd_apply_zero`, `yEnd_apply_succ`, via `ySucc`); it commutes with every `xEnd`
  (`xEnd_comp_yEnd`). `YComm G θ` says the `θ m` commute pairwise on affine opens (`yComm_iff`); then the `yEnd m`
  commute (`yEnd_comm`, `yEnd_mul_comm`) and `polyEnd` is the `A`-algebra map `A[Y_m : m < s] → End_A(FamilyFrames)`
  sending `Y_m` to `yEnd m` (`polyEnd_X`, `polyEnd_C`), with associated module structure `polyModule`
  (`polyModule_smul_def`); `xEnd` commutes with it (`xEnd_polyEnd`) and it preserves homogeneity
  (`IsHomogeneousElem.yEnd`, `IsHomogeneousElem.polyEnd`).
- `familyFramesGradedModule ι G θ hθ` is the graded module over `A[Y_m]` with underlying module `FamilyFrames ι G`,
  degree-`e` part the homogeneous elements of degree `e` (`mem_grade_iff`) and multiplication by `X_l` given by
  `xEnd l` (`xMul_apply`, `xMul_apply_apply`, `xMul_pow_apply`, `monMul_apply`); `moduleBase` is its `A`-module
  structure, and `smul_def`, `X_smul`, `C_smul`, `base_smul_apply` unfold the polynomial action.

The chart opens are recorded as affine opens by `framesChart` and `framesOverlap` (`ι` affine), and
`sections_smul_comm` is the commutation of the `A`- and `Γ(P, U)`-actions on sections. (Used to view the Rees-type
module `⊕_{e,k} H⁰(G_k(e))` of a family of coherent sheaves as a graded module over `A[Y]`, as in the proof of the
Grothendieck existence theorem for projective morphisms.)

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.OModulePresheaf.sections_smul_comm`
- def `AlgebraicGeometry.OModulePresheaf.FramesCompat`
- theorem `AlgebraicGeometry.OModulePresheaf.framesCompat_iff`
- theorem `AlgebraicGeometry.OModulePresheaf.FramesCompat.zero`
- theorem `AlgebraicGeometry.OModulePresheaf.FramesCompat.add`
- theorem `AlgebraicGeometry.OModulePresheaf.FramesCompat.smul`
- theorem `AlgebraicGeometry.OModulePresheaf.FramesCompat.frameUnit_smul`
- def `AlgebraicGeometry.OModulePresheaf.FamilyFrames`
- instance `AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup`
- instance `AlgebraicGeometry.OModulePresheaf.FamilyFrames.module`
- theorem `AlgebraicGeometry.OModulePresheaf.FamilyFrames.zero_apply`
- theorem `AlgebraicGeometry.OModulePresheaf.FamilyFrames.add_apply`
- theorem `AlgebraicGeometry.OModulePresheaf.FamilyFrames.neg_apply`
- theorem `AlgebraicGeometry.OModulePresheaf.FamilyFrames.sub_apply`
- theorem `AlgebraicGeometry.OModulePresheaf.FamilyFrames.smul_apply`
- theorem `AlgebraicGeometry.OModulePresheaf.FamilyFrames.ext`
- def `AlgebraicGeometry.OModulePresheaf.xEnd`
- theorem `AlgebraicGeometry.OModulePresheaf.xEnd_apply`
- theorem `AlgebraicGeometry.OModulePresheaf.xEnd_comm`
- def `AlgebraicGeometry.OModulePresheaf.IsHomogeneousElem`
- theorem `AlgebraicGeometry.OModulePresheaf.isHomogeneousElem_iff`
- theorem `AlgebraicGeometry.OModulePresheaf.IsHomogeneousElem.zero`
- theorem `AlgebraicGeometry.OModulePresheaf.IsHomogeneousElem.add`
- theorem `AlgebraicGeometry.OModulePresheaf.IsHomogeneousElem.smul`
- theorem `AlgebraicGeometry.OModulePresheaf.IsHomogeneousElem.xEnd`
- def `AlgebraicGeometry.OModulePresheaf.FamilyFrames.single`
- theorem `AlgebraicGeometry.OModulePresheaf.FamilyFrames.single_apply_self`
- theorem `AlgebraicGeometry.OModulePresheaf.FamilyFrames.single_apply_of_ne_degree`
- theorem `AlgebraicGeometry.OModulePresheaf.FamilyFrames.single_apply_of_ne_level`
- theorem `AlgebraicGeometry.OModulePresheaf.isHomogeneousElem_single_iff`
- abbrev `AlgebraicGeometry.OModulePresheaf.framesChart`
- abbrev `AlgebraicGeometry.OModulePresheaf.framesOverlap`
- def `AlgebraicGeometry.OModulePresheaf.ySucc`
- theorem `AlgebraicGeometry.OModulePresheaf.ySucc_zero`
- theorem `AlgebraicGeometry.OModulePresheaf.ySucc_succ`
- def `AlgebraicGeometry.OModulePresheaf.yEnd`
- theorem `AlgebraicGeometry.OModulePresheaf.yEnd_apply_zero`
- theorem `AlgebraicGeometry.OModulePresheaf.yEnd_apply_succ`
- theorem `AlgebraicGeometry.OModulePresheaf.xEnd_comp_yEnd`
- def `AlgebraicGeometry.OModulePresheaf.YComm`
- theorem `AlgebraicGeometry.OModulePresheaf.yComm_iff`
- theorem `AlgebraicGeometry.OModulePresheaf.yEnd_comm`
- theorem `AlgebraicGeometry.OModulePresheaf.yEnd_mul_comm`
- def `AlgebraicGeometry.OModulePresheaf.polyEnd`
- theorem `AlgebraicGeometry.OModulePresheaf.polyEnd_X`
- theorem `AlgebraicGeometry.OModulePresheaf.polyEnd_C`
- def `AlgebraicGeometry.OModulePresheaf.polyModule`
- theorem `AlgebraicGeometry.OModulePresheaf.polyModule_smul_def`
- theorem `AlgebraicGeometry.OModulePresheaf.xEnd_polyEnd`
- theorem `AlgebraicGeometry.OModulePresheaf.IsHomogeneousElem.yEnd`
- theorem `AlgebraicGeometry.OModulePresheaf.IsHomogeneousElem.polyEnd`
- def `AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule`
- theorem `AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule_M`
- instance `AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase`
- theorem `AlgebraicGeometry.OModulePresheaf.mem_grade_iff`
- theorem `AlgebraicGeometry.OModulePresheaf.xMul_apply`
- theorem `AlgebraicGeometry.OModulePresheaf.xMul_apply_apply`
- theorem `AlgebraicGeometry.OModulePresheaf.smul_def`
- theorem `AlgebraicGeometry.OModulePresheaf.X_smul`
- theorem `AlgebraicGeometry.OModulePresheaf.C_smul`
- theorem `AlgebraicGeometry.OModulePresheaf.base_smul_apply`
- theorem `AlgebraicGeometry.OModulePresheaf.xMul_pow_apply`
- theorem `AlgebraicGeometry.OModulePresheaf.monMul_apply`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (Library).
Other imports: `Mathlib`.
