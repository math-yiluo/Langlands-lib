# Projective space over a ring, products of projective spaces, and Chow data

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace`, in namespace
`AlgebraicGeometry`. All objects live in a fixed universe `u`; `R` is a commutative ring.

## Definitions and results

**Projective space.** Let `𝒜` be the grading of `R[X₀, …, Xₙ]` by total degree
(`MvPolynomial.homogeneousSubmodule`), so that `Proj 𝒜` is projective `n`-space `ℙⁿ_R`.

- `ProjSpace.grad0Equiv R n` is the ring isomorphism `R ≅ 𝒜₀` (constants), and `ProjSpace.π R n` is the
  structure morphism `ℙⁿ_R ⟶ Spec R`: `Proj 𝒜 ⟶ Spec 𝒜₀` followed by this isomorphism.
- Instances: `R[X₀, …, Xₙ]` is of finite type over `𝒜₀` (`finiteType_mvPolynomial`), so `π R n` is
  proper (`isProper_π`).
- `irrelevant_le_span_X` (theorem): the irrelevant ideal is contained in the ideal `(X₀, …, Xₙ)`.
- `X_mem_one`: each `Xⱼ` has degree `1`. `algebraAway` is the `R`-algebra structure on the degree-zero
  localization `𝒜_(Xᵢ)`, and `awayι_comp_π` (theorem) says that the chart `Spec 𝒜_(Xᵢ) ⟶ ℙⁿ_R`
  followed by `π` is `Spec` of this algebra map.
- `ProjSpace.ratio R n i k` is the element `Xₖ / Xᵢ` of `𝒜_(Xᵢ)`. `ratio_self` says `Xᵢ / Xᵢ = 1`, and
  `val_algebraMap` describes the image of `r ∈ R` in the localization.
- `ProjSpace.affineOpenCover R n` is the standard affine open cover of `ℙⁿ_R` by the charts
  `Spec 𝒜_(Xⱼ)` (`affineOpenCover_f`).
- `awayMk_monomial` (theorem) writes the fraction `r·Xᵉ / Xᵢᵈ` (with `deg e = d`) as
  `r · ∏ⱼ (Xⱼ / Xᵢ)^{eⱼ}`; consequently `adjoin_range_ratio` (theorem): `𝒜_(Xᵢ)` is generated as an
  `R`-algebra by the ratios `Xⱼ / Xᵢ`.

**Products of projective spaces.** For `e : Fin m → ℕ`:

- `prodOver R e` is the fibre product `ℙ^{e 0}_R ×_R ⋯ ×_R ℙ^{e (m−1)}_R` (with `Spec R` for `m = 0`),
  built by iterated pullbacks (`prodOverAux`), and `prodOverπ R e` its structure morphism to `Spec R`. It
  is proper (`isProper_prodOverπ`, instance `instIsProperProdOverπ`).
- `prodPr R e k` is the projection to the `k`-th factor, with `prodPr_comp_π`: it commutes with the
  structure morphisms.
- `prodLift R s e g hg`, for `s : X ⟶ Spec R` and morphisms `g k : X ⟶ ℙ^{e k}_R` over `Spec R`, is the
  induced morphism `X ⟶ prodOver R e` (built by `prodLiftAux`). `prodLift_comp_prodOverπ` and
  `prodLift_comp_prodPr` give its compatibilities.

**Base change of projective space.** For an `R`-algebra `A`:

- `mvMapGraded R A n` is the graded ring map `R[X₀, …, Xₙ] → A[X₀, …, Xₙ]` induced by `R → A`
  (`mvMapGraded_X`: it fixes the variables). `irrelevant_le_map_mvMapGraded` (theorem): the irrelevant
  ideal over `A` is contained in the image of the irrelevant ideal over `R`.
- `ProjSpace.map R A n : ℙⁿ_A ⟶ ℙⁿ_R` is the induced morphism of `Proj`s (`map_eq` unfolds it).

**Chow data.** Let `π : V ⟶ Spec R`.

- A `ChowDatum π` consists of `m` and `e : Fin m → ℕ`, a scheme `V'` with a proper morphism `p : V' ⟶ V`
  and a closed immersion `ι : V' ⟶ prodOver R e` over `Spec R` (`ι ≫ prodOverπ = p ≫ π`), and a dense
  open `U` of `V` over which `p` is an isomorphism (the projection `p⁻¹(U) ⟶ U` is an isomorphism). This
  is the data of Chow's lemma.
- A `ChowDatumProj π` is the same with a single projective space `ℙ^{Nd}_R` instead of a product.

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_ProjSpace.lean` from the Anthropic Lean
formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026
Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE`
and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these
changes:

- an attribution header is added above the imports;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- two proof steps are adapted to the pinned Mathlib (FLT pins Lean 4.33.1 and Mathlib `db584cd6`; this
  project pins Lean 4.34.0 and Mathlib `5ed29652`). There `MonoidAlgebra` is a structure, so
  `MvPolynomial.coeff d a` is written `a.coeff d` and `coeff_zero` is replaced by `simp`. The diff
  against the FLT file (after the option insertion) is:

```diff
--- FLT/Definitions/Def_AlgebraicGeometry_ProjSpace.lean (options inserted)
+++ port
@@ -367,3 +367,3 @@
     rcases eq_or_ne i 0 with rfl | hi0
-    · rw [ha, coeff_zero]
+    · rw [ha]; simp
     · exact ((mem_homogeneousSubmodule i _).mp
@@ -372,3 +372,3 @@
   obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr (Finsupp.support_eq_empty.not.mpr hd0)
-  obtain ⟨q, hq⟩ : (X j : MvPolynomial (Fin (n + 1)) A) ∣ monomial d (coeff d a) :=
+  obtain ⟨q, hq⟩ : (X j : MvPolynomial (Fin (n + 1)) A) ∣ monomial d (a.coeff d) :=
     X_dvd_monomial.mpr (Or.inr (Finsupp.mem_support_iff.mp hj))
```

The line numbers refer to the file without the attribution header. The file imports only Mathlib, so its
imports are unchanged.
