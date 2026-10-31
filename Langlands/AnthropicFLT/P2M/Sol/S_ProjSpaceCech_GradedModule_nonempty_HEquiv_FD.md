# The monomial Čech complex of `O(d)` and the graded Čech complex of `S(d)` (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_ProjSpaceCech_GradedModule_nonempty_HEquiv_FD`. Its declarations live
in the namespace `P2MW.S_ProjSpaceCech_GradedModule_nonempty_HEquiv_FD`.

## Statement

`solution`: for a commutative ring `R`, `n : ℕ`, `d₀ : ℤ` and `i : ℕ` there is an `R`-linear equivalence
`ProjSpaceCech.Twist.H R n d₀ i ≃ₗ[R] ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.FD R n d₀) i`.
The left side is the `i`-th cohomology of the Čech complex of `O(d₀)` on `ℙⁿ_R` written with Laurent
monomials (`Def_AlgebraicGeometry_ProjSpaceCechTwist`). The right side is the `i`-th Čech cohomology of the
free graded module `S(d₀)` over `S = R[X₀, …, Xₙ]`, built from homogeneous fractions
(`Def_AlgebraicGeometry_ProjSpaceCechGradedModule`). The theorem module
`Theorems.Thm_ProjSpaceCech_GradedModule_nonempty_HEquiv_FD` states this as
`ProjSpaceCech.GradedModule.nonempty_HEquiv_FD` and proves it from `solution`.

## Proof outline

The proof is in the namespace `…ProjSpaceCech`, section `Bridge`.

1. **Monomials as fractions.** `GradedModule.Xprod e` is the monomial `∏ⱼ Xⱼ ^ eⱼ`, which lies in the grade
   `∑ⱼ eⱼ` (`GradedModule.Xprod_mem_freeGrade`). `GradedModule.twistFrac b` writes a Laurent monomial `b` of
   degree `d₀`, with negative exponents only at indices in `I`, as the fraction with numerator
   `Xprod (b⁺)` and denominator exponents `b⁻`. `GradedModule.twistToGradSec I` extends this linearly from
   the free module `Twist.Sec R n d₀ I` on such monomials to the localized sections over `I`. It commutes
   with the restriction maps (`GradedModule.twistToGradSec_incl`).
2. **Auxiliary identities.** `GradedModule.sec_mk_enlarge` multiplies numerator and denominator by a
   monomial. `GradedModule.FD_monMul_apply` and `GradedModule.Xprod_mul` compute the monomial action on
   `S(d₀)`. `GradedModule.coeff_Xprod` gives the coefficients of `Xprod e`.
   `GradedModule.sec_mk_Xprod_eq_twistFrac` identifies a fraction `Xprod e / X^a` with `twistFrac b` when
   `b = e − a`. `GradedModule.secMkAt_FD_injective` says that fractions with a fixed denominator are
   injective in the numerator, because multiplication by a monomial is injective on polynomials.
3. **Bijectivity on sections.** For injectivity (`GradedModule.twistToGradSec_injective`), put a finite
   combination of the `twistFrac b` over the common denominator `a₀`, the maximum of the negative parts.
   The numerators `Xprod (a₀ + b)` are distinct monomials, so comparing coefficients
   (`GradedModule.coeff_Xprod`) shows all coefficients vanish. For surjectivity
   (`GradedModule.twistToGradSec_surjective`), a fraction `m / X^a` with `m` homogeneous of degree
   `∑ aⱼ + d₀` is the sum of its monomial terms, each of which is the image of the Laurent monomial `e − a`.
   If that degree is negative, the grade is zero. This gives `GradedModule.secTwistEquiv`.
4. **Cochains and cohomology.** `GradedModule.cochainTwistEquiv` applies `secTwistEquiv` on each component
   and commutes with the differentials (`GradedModule.cochainTwistEquiv_comm`, the signs `(-1)ʲ` as integers
   versus elements of `R`). Hence it maps cocycles onto cocycles and coboundaries onto coboundaries
   (`GradedModule.cochainTwistEquiv_ker`, `GradedModule.cochainTwistEquiv_range`).
   `GradedModule.HTwistEquiv` is the induced equivalence on cocycles in degree `0` and on the quotient in
   degree `j + 1`. The latter uses `Twist.d_sq` (`Theorems.Thm_ProjSpaceCech_Twist_d_sq`) to see that
   coboundaries are cocycles. `solution` is `⟨GradedModule.HTwistEquiv d₀ i⟩`.

## Provenance and licence

This file is a port of `P2M/Sol/S_ProjSpaceCech_GradedModule_nonempty_HEquiv_FD.lean` from the Anthropic Lean
formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (registered
literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in
`licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies.
Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist`,
  `Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule` and
  `Theorems.Thm_ProjSpaceCech_Twist_d_sq` are renamed to the corresponding `Langlands.AnthropicFLT.*`
  modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false` (the file
  then raises the heartbeat limits further itself, as in FLT);
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect: each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names,
  each `p2m_open "N"` becomes `open _root_.N`, and each `p2m_open_scoped "N" in` becomes
  `open scoped _root_.N in`;
- two proof steps are adapted to the newer Mathlib of this environment. FLT pins Lean 4.33.1 and Mathlib
  `db584cd6`, and this environment has Lean 4.34.0 and Mathlib `5ed29652`, where the constant
  `MvPolynomial.coeff` no longer exists. The coefficient is written with dot notation instead, and
  `MvPolynomial.coeff_zero` is replaced by `AddMonoidAlgebra.coeff_zero`. The statements are unchanged.
  The unified diff against the FLT file after the other changes above is:

```diff
--- FLT/P2M/Sol/S_ProjSpaceCech_GradedModule_nonempty_HEquiv_FD.lean (after the other changes)
+++ port
@@ -133,3 +133,3 @@
 theorem GradedModule.coeff_Xprod (e : Fin (n + 1) → ℕ) (s : Fin (n + 1) →₀ ℕ) :
-    MvPolynomial.coeff s (GradedModule.Xprod (R := R) e)
+    (GradedModule.Xprod (R := R) e).coeff s
       = if s = ∑ j, Finsupp.single j (e j) then 1 else 0 := by
@@ -238,4 +238,4 @@
     intro s
-    have hc := congrArg (MvPolynomial.coeff s) hpz
-    rw [MvPolynomial.coeff_zero, MvPolynomial.coeff_sum] at hc
+    have hc := congrArg (fun r : MvPolynomial (Fin (n + 1)) R => r.coeff s) hpz
+    rw [MvPolynomial.coeff_sum, AddMonoidAlgebra.coeff_zero] at hc
     refine Eq.trans (Finset.sum_congr rfl fun e _ => ?_) hc
```

The line numbers refer to the file without the attribution header.
