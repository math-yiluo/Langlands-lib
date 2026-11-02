# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- Manual edit for Mathlib drift (FLT line 58, line 70 here): `have hmono : (monomial s (coeff s g) : MvPolynomial (Fin (n + 1)) B) =` is replaced by `have hmono : (monomial s (g.coeff s) : MvPolynomial (Fin (n + 1)) B) =`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 59, line 71 here): `coeff s g • MvPolynomial.map (algebraMap A B) (monomial s (1 : A)) := by` is replaced by `g.coeff s • MvPolynomial.map (algebraMap A B) (monomial s (1 : A)) := by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 177, line 189 here): `have hw : ∀ s : Fin (n + 1) →₀ ℕ, (monomial s (coeff s p) : MvPolynomial (Fin (n + 1)) A).IsHomogeneous d := by` is replaced by `have hw : ∀ s : Fin (n + 1) →₀ ℕ, (monomial s (p.coeff s) : MvPolynomial (Fin (n + 1)) A).IsHomogeneous d := by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 179, line 191 here): `by_cases hs : coeff s p = 0` is replaced by `by_cases hs : p.coeff s = 0`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 183, line 195 here): `let w : (Fin (n + 1) →₀ ℕ) → SA (n := n) (A := A) d := fun s => ⟨monomial s (coeff s p), hw s⟩` is replaced by `let w : (Fin (n + 1) →₀ ℕ) → SA (n := n) (A := A) d := fun s => ⟨monomial s (p.coeff s), hw s⟩`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 189, line 201 here): `∑ s ∈ p.support, monomial s (algebraMap A B (coeff s p)) := by` is replaced by `∑ s ∈ p.support, monomial s (algebraMap A B (p.coeff s)) := by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 192, line 204 here): `have hterm : ∀ s ∈ p.support, Psi' (B := B) I d (monomial s (algebraMap A B (coeff s p))) =` is replaced by `have hterm : ∀ s ∈ p.support, Psi' (B := B) I d (monomial s (algebraMap A B (p.coeff s))) =`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 199, line 211 here): `show algebraMap A B (coeff s p) = coeff s p • (1 : B) by rw [Algebra.smul_def, mul_one],` is replaced by `show algebraMap A B (p.coeff s) = p.coeff s • (1 : B) by rw [Algebra.smul_def, mul_one],`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 253, line 265 here): `(monomial s (coeff s (q : MvPolynomial (Fin (n + 1)) B)) : MvPolynomial (Fin (n + 1)) B).IsHomogeneous d := by` is replaced by `(monomial s ((q : MvPolynomial (Fin (n + 1)) B).coeff s) : MvPolynomial (Fin (n + 1)) B).IsHomogeneous d := by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 255, line 267 here): `by_cases hs : coeff s (q : MvPolynomial (Fin (n + 1)) B) = 0` is replaced by `by_cases hs : (q : MvPolynomial (Fin (n + 1)) B).coeff s = 0`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 260, line 272 here): `fun s => ⟨monomial s (coeff s (q : MvPolynomial (Fin (n + 1)) B)), hw s⟩` is replaced by `fun s => ⟨monomial s ((q : MvPolynomial (Fin (n + 1)) B).coeff s), hw s⟩`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 266, line 278 here): `E (B := B) I d (Psi' (B := B) I d (monomial s (coeff s (q : MvPolynomial (Fin (n + 1)) B)))) =` is replaced by `E (B := B) I d (Psi' (B := B) I d (monomial s ((q : MvPolynomial (Fin (n + 1)) B).coeff s))) =`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 15 here); in 3 lines the replacements `Type` (universe 0) → `Type uz` (3 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map`. Statement. `AlgebraicGeometry.HilbertFunctor.exists_linearEquiv_baseChange_piece_map`: let `B` be an
`A`-algebra and `I` a homogeneous ideal of `A[X₀, …, Xₙ]`. Then the extended ideal of `B[X₀, …, Xₙ]` is
homogeneous, and for every `d` there is a `B`-linear isomorphism `B ⊗[A] piece I d ≅ piece (I B) d`
sending `1 ⊗ [p]` to `[p_B]` (the pieces commute with base change).

Proof (namespace `HilbPieceBC`). Homogeneous components commute with `MvPolynomial.map`
(`homogeneousComponent_map`). `T I j`: the `B`-span of the images of the forms of degree `j` in `I`;
it is stable under multiplication by forms (`mul_mem_T`), contains the degree-`d` components of all
elements of the extended ideal (`homogeneousComponent_mem_T`), and lies in it (`T_le`); in particular
the extended ideal is homogeneous (`map_homogeneous`). The map `E : B ⊗ piece I d → piece (I B) d` is
the base change of `gbar` (induced by `gd = MvPolynomial.map` on degree-`d` forms). Its inverse
`Psi` is defined on monomials (`Psi'` via the monomial basis, `v`), kills `T I d` (`T_le_ker`) and
hence descends to `piece (I B) d`; `Psi_E` and `E_Psi` show that they are inverse (`equiv`,
`equiv_tmul_mk`).

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.homogeneousComponent_map`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.degree_eq_of_mem_support`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.decompose_eq`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.T`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.map_mem_T`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.mul_mem_T`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.homogeneousComponent_mem_T`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.T_le`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.map_homogeneous`
- abbrev `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.SA`
- abbrev `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.SB`
- abbrev `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.I'`
- abbrev `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.KA`
- abbrev `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.KB`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.gd`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.gd_apply_coe`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.gbar`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.gbar_mk`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.E`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.E_tmul`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.v`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.Psi'`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.Psi'_monomial`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.Psi'_map`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.Psi'_map_eq_zero`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.T_le_ker`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.Psi`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.Psi_mk`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.Psi_E`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.E_Psi`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.equiv`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.HilbPieceBC.equiv_tmul_mk`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution).
Other imports: `Mathlib`.
