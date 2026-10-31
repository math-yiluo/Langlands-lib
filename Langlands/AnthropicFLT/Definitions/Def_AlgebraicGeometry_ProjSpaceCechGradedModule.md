# Graded modules over a polynomial ring and their combinatorial Čech complex on projective space

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule`, in namespace
`ProjSpaceCech`. Modules live in a fixed universe `u`; `R` is a commutative ring and `n ∈ ℕ`. The index
tuples `Idx n i`, their images `Idx.img` and faces `Idx.face` are those of
`Def_AlgebraicGeometry_ProjSpaceCechTwist`.

## Definitions and results

**Graded modules.** A `GradedModule R n` is an `R`-module `M` with a family of submodules `grade d`,
`d ∈ ℤ`, and pairwise commuting `R`-linear maps `xMul j : M → M` (multiplication by `Xⱼ`) that send
`grade d` into `grade (d+1)`. This models a graded module over `R[X₀, …, Xₙ]`. The `grade d` need not
form a direct sum decomposition.

- `monMul D a` is multiplication by the monomial `Xᵃ = ∏ⱼ Xⱼ^{aⱼ}` (a commuting product of powers of the
  `xMul j`). The lemmas `xMul_pow_commute`, `monMul_congr`, `noncommProd_one`, `monMul_zero`,
  `monMul_add`, `monMul_add_apply`, `monMul_single`, `monMul_commute` and `monMul_commute_apply` give its
  algebra, and `xMul_pow_mem_grade` and `monMul_mem_grade` say that `Xᵃ` raises degrees by `∑ aⱼ`.

**Degree-zero localizations.** For `I ⊆ {0, …, n}`:

- a `GradedModule.Frac D I` is a formal fraction `m / Xᵃ` with `aⱼ = 0` for `j ∉ I` and
  `m ∈ grade (∑ aⱼ)`;
- `Frac.Rel D I` identifies `m / Xᵃ` and `m' / Xᵃ'` when `Xᶜ Xᵃ' m = Xᶜ Xᵃ m'` for some `c` supported in
  `I`. It is an equivalence relation (`Rel.refl`, `Rel.symm`, `Rel.trans`, `Frac.setoid`; `supp_add` is a
  helper);
- `GradedModule.sec D I` is the quotient, the degree-zero part of the localization of `M` at
  `∏_{j∈I} Xⱼ`: the sections over `D₊(∏_{j∈I} Xⱼ)` of the sheaf attached to `D`. It is an `R`-module
  (instances `instZero`, `instAdd`, `instNeg`, `instSMul`, `instAddCommGroup`, `instModule`) with
  constructor `sec.mk` and lemmas `sec_mk_eq`, `sec_mk_smul`, `sec_mk_neg`, `sec_mk_zero_num`,
  `sec_mk_congr`, `sec_mk_add`;
- `secMkAt D I a ha : grade (∑ aⱼ) → sec D I` is `m ↦ m / Xᵃ`, and `secIncl D hIJ` for `I ⊆ J` is the
  restriction `sec D I → sec D J` (`secIncl_mk`, `secIncl_trans`, `secIncl_irrel`).

**Čech complex.** `GradedModule.cochain D i` is the product of `sec D (img s)` over `s : Idx n i`,
`GradedModule.faceRes` the restriction along a face, `GradedModule.d D i` the alternating Čech
differential (`d_apply`), and `GradedModule.H D i` the Čech cohomology (with its group and module
instances). `subsingleton_cohomology_of_lt` (theorem): `H D i` is trivial for `i > n`.

**Constructions.**

- `GradedModule.free R n` is `R[X₀, …, Xₙ]` with `grade d` the homogeneous polynomials of degree `d`
  (`freeGrade`, zero for `d < 0`; `freeGrade_of_nonneg`) and `xMul j` multiplication by `Xⱼ`
  (`freeXMul`). `free_monMul_apply` says `monMul` is multiplication by `∏ Xⱼ^{aⱼ}`, which is injective
  (`free_monMul_injective`).
- `D.shift d₀` has `grade d = D.grade (d + d₀)`, and `GradedModule.FD R n d₀ = (free R n).shift d₀`, the
  module `R[X₀, …, Xₙ](d₀)`. `isHomogeneous_prod_X_pow` and `prod_X_pow_mem_freeGrade` say that `Xᵉ`
  is homogeneous of degree `∑ eⱼ`.
- `GradedModule.pi D` is a finite product, `D.quot K hstab` the quotient by an `xMul`-stable submodule
  `K`, and `D.sub K hstab` the submodule `K` with grades `grade d ⊓ K`.

**Morphisms.** A `GradedModule.Hom D₁ D₂` is an `R`-linear map preserving grades and commuting with
every `xMul j`. It commutes with `monMul` (`Hom.map_monMul`), induces maps `secMap` on degree-zero
localizations (compatible with `secIncl`, `secMap_incl`), `cochainMap` on cochains (commuting with `d`,
`cochainMap_comm`), `cochainMapKer` on cocycles and `HMap` on Čech cohomology. `Hom.shift` is the
shifted morphism (`shift_toLinearMap`).

**Finitely generated graded modules.** A `GradedModule.Presentation D` is a finite family of shifts
`d₀ k` and a morphism `hom : ⨁ₖ R[X₀, …, Xₙ](d₀ k) → D` that is surjective in every degree. `D.IsFG`
means a presentation exists. For a presentation `σ`, `σ.F` is the free source, `σ.K` the kernel of
`hom` (stable under every `xMul j`, `K_xMul_stable`), `σ.ker` the kernel as a graded module, and
`σ.kerIncl` its inclusion into `σ.F`.

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_ProjSpaceCechGradedModule.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist` is renamed to
  `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- one proof step is adapted to the pinned Mathlib (FLT pins Lean 4.33.1 and Mathlib `db584cd6`; this
  project pins Lean 4.34.0 and Mathlib `5ed29652`, where `MonoidAlgebra` is a structure and
  `MvPolynomial.coeff m` is written `r.coeff m`). The diff against the FLT file (after the import rename
  and option insertion) is:

```diff
--- FLT/Definitions/Def_AlgebraicGeometry_ProjSpaceCechGradedModule.lean (imports rewritten, options inserted)
+++ port
@@ -552,3 +552,3 @@
     ext e
-    have := congrArg (MvPolynomial.coeff (e + ∑ j, Finsupp.single j (a j))) h'
+    have := congrArg (fun r : MvPolynomial (Fin (n+1)) R => r.coeff (e + ∑ j, Finsupp.single j (a j))) h'
     simpa [MvPolynomial.coeff_monomial_mul'] using this
```

The line numbers refer to the file without the attribution header.
