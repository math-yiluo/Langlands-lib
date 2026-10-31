# The monomial Čech cohomology of `O(d)` on `ℙⁿ` is finitely generated (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_ProjSpaceCech_Twist_finite_cohomology`. Its declarations live in the
namespace `P2MW.S_ProjSpaceCech_Twist_finite_cohomology`.

## Statement

`solution`: for a commutative ring `R`, `n : ℕ`, `d : ℤ` and `i : ℕ`, the `R`-module
`ProjSpaceCech.Twist.H R n d i` is finitely generated. Here `Twist.H R n d i` is the `i`-th cohomology of the
Čech complex of `O(d)` on `ℙⁿ_R` for the standard cover, written with Laurent monomials
(`Def_AlgebraicGeometry_ProjSpaceCechTwist`): an `i`-cochain assigns to each strictly increasing index
`s : Idx n i` a finitely supported `R`-combination of exponent vectors `a : Fin (n + 1) → ℤ` of total degree
`d` whose negative support `Twist.negSupp n a` lies in the image of `s`. The theorem module
`Theorems.Thm_ProjSpaceCech_Twist_finite_cohomology` states this as `ProjSpaceCech.Twist.finite_cohomology`
and proves it from `solution`.

## Proof outline

The proof is in the namespace `…ProjSpaceCech`. It computes enough of the cohomology to see finiteness in
every degree.

1. **Degrees above `n`** (`Twist.subsingleton_cohomology_of_lt`). There are no strictly increasing indices
   of length `i + 1 > n + 1`, so the cochains and the cohomology are trivial.
2. **Index combinatorics** (section `Homotopy`). An index is determined by its image (`Twist.idx_canonical`,
   `Twist.idx_eq_of_img`). Faces erase one element of the image (`Twist.img_face`). `Twist.altOfFinset`,
   `Twist.altPos`, `Twist.altInsert` and `Twist.insPos` build the index with a given image, find the position
   of an element, and insert a new element `j` at its position. Lemmas such as `Twist.face_altInsert_insPos`
   and `Twist.img_face_altInsert_ne` relate faces and insertion. `Twist.altPos_eq_card` and
   `Twist.insPos_eq_card` (section `Rank`) compute positions as numbers of smaller elements, which fixes the
   signs below.
3. **Coefficients.** `Twist.coeff f s a` is the coefficient of the monomial `a` in `f s`, or `0` if `a` is not
   allowed at `s`. It is additive and linear (`Twist.coeff_add`, `Twist.coeff_smul`, `Twist.coeffL`),
   determines `f` (`Twist.ext_coeff`), and the differential is the alternating sum of the coefficients on
   the faces (`Twist.coeff_d`). `Twist.coeff_piSingle` computes it on basis cochains.
4. **The contracting homotopy.** For `j₁ : Fin (n + 1)`, `Twist.hj j₁` sends an `(i + 1)`-cochain `f` to the
   `i`-cochain whose value at `s` with `j₁ ∉ img s` is `±f(s ∪ {j₁})`, the sign being `(-1)` to the position
   of `j₁`, and `0` otherwise (`Twist.coeff_hj`, `Twist.coeff_hj_of_mem`). The key identity
   `Twist.dh_hd_coeff` says `d(hj f) + hj(d f)` and `f` have the same coefficient at `(s, a)` whenever the
   negative support of `a` lies in `img s` and avoids `j₁`. `Twist.posMin a` is the least index outside the
   negative support of `a`, and `Twist.homot` applies `hj (posMin a)` to the `a`-part of each component, so
   on coefficients it agrees with `hj (posMin a)` (`Twist.homot_basis`, `Twist.coeff_homot`).
5. **Middle degrees** (`Twist.subsingleton_cohomology_succ_of_le`). If `i + 2 ≤ n`, the negative support of
   an allowed monomial at an `(i + 1)`-index has at most `i + 2 < n + 1` elements, so `posMin` exists, and a
   cocycle `f` equals `d (homot f)`. Hence `H^{i+1} = 0`.
6. **Degree `0` for `n ≥ 1`** (section `HZero`). `Twist.constSec` sends a combination of monomials with no
   negative exponents to the constant `0`-cochain, which is a cocycle (`Twist.constSec_mem_ker`). A cocycle
   has the same coefficients at every vertex (`Twist.ker_edge`), and a monomial with a negative exponent at
   one vertex is not allowed at another vertex, so every cocycle is a constant section
   (`Twist.H_zero_finite`). There are finitely many monomials of degree `d` with no negative exponents (the
   scoped instance `Twist.mon_empty_finite`).
7. **Top degree `n = m + 1`** (section `HN`). The only `n`-index is `Twist.sfull`, every `n`-cochain is a
   cocycle, and a basis cochain at a monomial with some nonnegative exponent is a coboundary
   (`Twist.basis_mem_range`, again via `hj` and `Twist.dh_hd_coeff`). So `H^n` is spanned by the monomials
   all of whose exponents are negative, of which there are finitely many (the scoped instance
   `Twist.mon_allNeg_finite`). This is `Twist.H_top_finite`.
8. **Conclusion** (`Twist.finite_cohomology`). For `n = 0`, `H^0` is the whole cochain module, which is
   finite because there is only one monomial of each degree (`Twist.mon_zero_finite`), and higher
   cohomology vanishes. For `n = m + 1`, combine steps 1, 5, 6 and 7, using
   `Twist.finite_of_subsingleton` for the vanishing degrees. `solution` is `Twist.finite_cohomology`.

## Provenance and licence

This file is a port of `P2M/Sol/S_ProjSpaceCech_Twist_finite_cohomology.lean` from the Anthropic Lean
formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (registered
literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in
`licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies.
Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist` is renamed to
  `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false` (the file
  then raises the heartbeat limits further itself, as in FLT);
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect: each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names,
  each `p2m_open "N"` becomes `open _root_.N`, and each `p2m_open_scoped "N" in` becomes
  `open scoped _root_.N in`. Each `p2m_reactivate` becomes an `open scoped` of
  `P2MW.S_ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist` (and, at the end, also of
  `P2MW.S_ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech`). It re-activates the scoped instances
  `Twist.mon_empty_finite`, `Twist.mon_allNeg_finite` and `Twist.mon_zero_finite`, which belong to that
  namespace;
- three proof steps are adapted to the newer Mathlib of this environment. FLT pins Lean 4.33.1 and Mathlib
  `db584cd6`, and this environment has Lean 4.34.0 and Mathlib `5ed29652`, where the lemma for
  `Finsupp.mapDomain` along an injective map is named `Finsupp.mapDomain_apply_of_injective` rather than
  `Finsupp.mapDomain_apply`. The statements are unchanged. The unified diff against the FLT file after the
  other changes above is:

```diff
--- FLT/P2M/Sol/S_ProjSpaceCech_Twist_finite_cohomology.lean (after the other changes)
+++ port
@@ -234,3 +234,3 @@
               ⟨a, hok.1, hface⟩ := rfl
-      rw [key, Finsupp.mapDomain_apply (Twist.Mon.incl_injective n d _)]
+      rw [key, Finsupp.mapDomain_apply_of_injective (Twist.Mon.incl_injective n d _)]
     · rw [Twist.coeff_of_not _ _ _ _ _ hface, smul_zero,
@@ -723,3 +723,3 @@
         = Twist.Mon.incl n d (Finset.empty_subset _) ⟨a, h2.1, h2.2.le⟩ := rfl
-    rw [key, Finsupp.mapDomain_apply (Twist.Mon.incl_injective n d _)]
+    rw [key, Finsupp.mapDomain_apply_of_injective (Twist.Mon.incl_injective n d _)]
   · rw [Finsupp.mapDomain_notin_range]
@@ -950,3 +950,3 @@
       have hkey : b = (Subtype.val : S → _) ⟨b, hb⟩ := rfl
-      rw [hkey, Finsupp.mapDomain_apply Subtype.val_injective, hg_def,
+      rw [hkey, Finsupp.mapDomain_apply_of_injective Subtype.val_injective, hg_def,
         Finsupp.comapDomain_apply]
```

The line numbers refer to the file without the attribution header.
