# Projective space is compatible with base change (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_isPullback_map`. Its declarations live in
the namespace `P2MW.S_AlgebraicGeometry_ProjSpace_isPullback_map`.

## Statement

`solution`: for commutative rings `R` and `A` with an `R`-algebra structure on `A` and `n : ℕ`, the square

```
ℙⁿ_A ──ProjSpace.map R A n──▶ ℙⁿ_R
  │                            │
ProjSpace.π A n          ProjSpace.π R n
  ▼                            ▼
Spec A ───Spec (algebraMap)──▶ Spec R
```

is a pullback square (`IsPullback`; `ProjSpace.map`, `ProjSpace.π` from `Def_AlgebraicGeometry_ProjSpace`), so
`ℙⁿ_A ≅ ℙⁿ_R ×_{Spec R} Spec A`. The theorem module `Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map`
states this as `AlgebraicGeometry.ProjSpace.isPullback_map` and proves it from `solution`.

## Proof outline

The proof is in the namespace `…AlgebraicGeometry.ProjSpace`, section `ProjBaseChange`. Write `𝒜R`, `𝒜A` for
the gradings of `R[X₀, …, Xₙ]` and `A[X₀, …, Xₙ]`.

1. **The charts.** `awayMapX j` is the map of degree-zero localizations `(𝒜R)_{(Xⱼ)} → (𝒜A)_{(Xⱼ)}` induced by
   `mvMapGraded` (`awayMapX_mk`, `awayMapX_algebraMap`, `awayMapX_ratio`; `C_mem_zero` and
   `algebraMap_eq_mk_zero` describe constants). In section `AwayChart`, `awayChartEquiv` identifies
   `(𝒜S)_{(Xⱼ)}` with the polynomial ring `S[Xₖ/Xⱼ : k ≠ j]`: the evaluation at the ratios (`ProjSpace.ratio`)
   is injective by comparing coefficients of monomials (`val_aeval_ratio_monomial`, `exponent_inj`,
   `aeval_ratio_injective`) and surjective because the ratios generate (`adjoin_range_ratio`).
2. **Base change of a chart** (section `AwayBC`). With `awayMapXₐ`, `incAₐ` and the identification
   `R[x] ⊗_R A ≅ A[x]` (`scalarRTensorAlgEquiv'`, `scalarRTensor_tmul_one`, `scalarRTensor_one_tmul`),
   `awayMvPolyBaseChangeEquiv` is a ring isomorphism `(𝒜R)_{(Xⱼ)} ⊗_R A ≅ (𝒜A)_{(Xⱼ)}`
   (`awayMapX_chart_compat`, `awayMvPolyBaseChangeEquiv_tmul_one`, `awayMvPolyBaseChangeEquiv_one_tmul`).
3. **The square commutes** (`w`). On each standard chart `D₊(s)` of `ℙⁿ_A`, both composites are `Spec` of the
   same ring map (`w_chart`, `awayMap_fromZero_compat`), and these charts cover `ℙⁿ_A`.
4. **The comparison map is an isomorphism** (`isPullback_map'`). Let `c : ℙⁿ_A → ℙⁿ_R ×_{Spec R} Spec A` be
   the induced map. The pullback of the chart `D₊(Xⱼ)` of `ℙⁿ_R` is `Spec ((𝒜R)_{(Xⱼ)} ⊗_R A)`, which
   `chartIso` identifies with `Spec (𝒜A)_{(Xⱼ)}`, and `c` restricted to `D₊(Xⱼ)` of `ℙⁿ_A`
   (`projMap_preimage_basicOpen_X`, `map_preimage_basicOpen_X'`) is this isomorphism (`hkey`). Being an
   isomorphism is local on the target (`IsZariskiLocalAtTarget.of_openCover`), so `c` is an isomorphism and
   the square is a pullback (`IsPullback.of_iso_pullback`).

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_isPullback_map.lean` from the Anthropic Lean
formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (registered
literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in
`licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies.
Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_ProjSpace` is renamed to
  `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false` (the file then
  raises the heartbeat limits further itself, as in FLT);
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. Each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names.
  Each `p2m_open` becomes an `open` of the same namespaces, written with `_root_.` where needed. These
  replacements change no declaration, statement or proof step;
- several proof steps are adapted to the newer Mathlib of this environment. FLT pins Lean 4.33.1 and Mathlib
  `db584cd6`, and this environment has Lean 4.34.0 and Mathlib `5ed29652`. There the lemma for
  `Finsupp.mapDomain` along an injective map is named `Finsupp.mapDomain_apply_of_injective`, the constant
  `MvPolynomial.coeff` no longer exists (coefficients are written `p.coeff d`), and `MvPolynomial.coeff_zero`
  is replaced by `AddMonoidAlgebra.coeff_zero` or closed by `simp`. The statements are unchanged. The unified
  diff against the FLT file after the other changes above is:

```diff
--- FLT/P2M/Sol/S_AlgebraicGeometry_ProjSpace_isPullback_map.lean (after the other changes)
+++ port
@@ -130,3 +130,3 @@
   simp only [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm k.2), add_zero,
-    Finsupp.mapDomain_apply Subtype.val_injective] at this
+    Finsupp.mapDomain_apply_of_injective Subtype.val_injective] at this
   exact this
@@ -162,3 +162,3 @@
   have hterm : ∀ d ∈ p.support,
-      Localization.mk (coeff d p • ∏ k ∈ d.support, (X k.1 : MvPolynomial _ S) ^ d k)
+      Localization.mk (p.coeff d • ∏ k ∈ d.support, (X k.1 : MvPolynomial _ S) ^ d k)
           (⟨(X j)^(∑ k ∈ d.support, d k), _, rfl⟩
@@ -166,3 +166,3 @@
         * ι ((X j)^N)
-      = ι ((coeff d p • ∏ k ∈ d.support, (X k.1 : MvPolynomial _ S) ^ d k)
+      = ι ((p.coeff d • ∏ k ∈ d.support, (X k.1 : MvPolynomial _ S) ^ d k)
           * (X j)^(N - ∑ k ∈ d.support, d k)) := by
@@ -184,3 +184,3 @@
   have hform : ∀ d ∈ p.support,
-      (coeff d p • ∏ k ∈ d.support, (X k.1 : MvPolynomial (Fin (n+1)) S) ^ d k)
+      (p.coeff d • ∏ k ∈ d.support, (X k.1 : MvPolynomial (Fin (n+1)) S) ^ d k)
         * (X j)^(N - ∑ k ∈ d.support, d k)
@@ -188,3 +188,3 @@
           (d.mapDomain Subtype.val + Finsupp.single j (N - ∑ k ∈ d.support, d k)))
-          (coeff d p) := by
+          (p.coeff d) := by
     intro d _
@@ -202,11 +202,11 @@
   by_cases hd₀ : d₀ ∈ p.support
-  · have hcoef := congrArg (coeff (d₀.mapDomain Subtype.val
+  · have hcoef := congrArg (fun q : MvPolynomial (Fin (n + 1)) S => q.coeff (d₀.mapDomain Subtype.val
       + Finsupp.single j (N - ∑ k ∈ d₀.support, d₀ k))) hp'
     simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
-      MvPolynomial.coeff_zero] at hcoef
+      AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at hcoef
     rw [Finset.sum_congr rfl (fun d _ => if_congr
       ⟨fun h => exponent_inj n j N h, fun h => h ▸ rfl⟩ rfl rfl),
-      Finset.sum_ite_eq' p.support d₀ (fun d => coeff d p), if_pos hd₀] at hcoef
-    exact hcoef.trans (MvPolynomial.coeff_zero _).symm
-  · exact (MvPolynomial.notMem_support_iff.mp hd₀).trans (MvPolynomial.coeff_zero _).symm
+      Finset.sum_ite_eq' p.support d₀ (fun d => p.coeff d), if_pos hd₀] at hcoef
+    exact hcoef.trans (by simp)
+  · exact (MvPolynomial.notMem_support_iff.mp hd₀).trans (by simp)
 
```

The line numbers refer to the file without the attribution header.
