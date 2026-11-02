# `Langlands.AnthropicFLT.P2M.Sol.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- Manual edit for Mathlib drift (FLT line 127, line 139 here): `a - C (coeff 0 a) ∈ Ideal.span (Set.range (X : τ → MvPolynomial τ K)) := by` is replaced by `a - C (a.coeff 0) ∈ Ideal.span (Set.range (X : τ → MvPolynomial τ K)) := by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 177, line 189 here): `have hGsum : G = ∑ i, C (coeff 0 (p i)) * F i := by` is replaced by `have hGsum : G = ∑ i, C ((p i).coeff 0) * F i := by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 181, line 193 here): `have hhom : ∀ i, (ψ (r' i) - C (coeff 0 (p i)) * ℓ).IsHomogeneous 1 := fun i =>` is replaced by `have hhom : ∀ i, (ψ (r' i) - C ((p i).coeff 0) * ℓ).IsHomogeneous 1 := fun i =>`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 182, line 194 here): `(hψh 1 _ (hr'1 i)).sub (by simpa using (isHomogeneous_C σ (coeff 0 (p i))).mul hℓ)` is replaced by `(hψh 1 _ (hr'1 i)).sub (by simpa using (isHomogeneous_C σ ((p i).coeff 0)).mul hℓ)`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 183, line 195 here): `refine ⟨fun i => ψ (r' i) - C (coeff 0 (p i)) * ℓ, ⟨⟨1, le_rfl, hhom⟩, ?_⟩, hhom, fun i => ?_⟩` is replaced by `refine ⟨fun i => ψ (r' i) - C ((p i).coeff 0) * ℓ, ⟨⟨1, le_rfl, hhom⟩, ?_⟩, hhom, fun i => ?_⟩`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 184, line 196 here): `· calc ∑ i, (ψ (r' i) - C (coeff 0 (p i)) * ℓ) * F i` is replaced by `· calc ∑ i, (ψ (r' i) - C ((p i).coeff 0) * ℓ) * F i`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 185, line 197 here): `= ∑ i, ψ (r' i) * F i - ℓ * ∑ i, C (coeff 0 (p i)) * F i := by` is replaced by `= ∑ i, ψ (r' i) * F i - ℓ * ∑ i, C ((p i).coeff 0) * F i := by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 202, line 214 here): `have hyC : ∀ i, y i = C (coeff 0 (y i)) := fun i => by` is replaced by `have hyC : ∀ i, y i = C ((y i).coeff 0) := fun i => by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 204, line 216 here): `refine ⟨0, zero_mem _, fun i => coeff 0 (y i), ?_, fun i => ?_⟩` is replaced by `refine ⟨0, zero_mem _, fun i => (y i).coeff 0, ?_, fun i => ?_⟩`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 222, line 234 here): `have key : ∃ v₁ ∈ V F, ∀ i, (a - C (coeff 0 a)) * C (w₀ i) = φ (v₁ i) := by` is replaced by `have key : ∃ v₁ ∈ V F, ∀ i, (a - C (a.coeff 0)) * C (w₀ i) = φ (v₁ i) := by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 243, line 255 here): `refine ⟨ψ a • v₀ + v₁, add_mem (Submodule.smul_mem _ _ hv₀) hv₁, fun i => coeff 0 a * w₀ i, ?_, fun i => ?_⟩` is replaced by `refine ⟨ψ a • v₀ + v₁, add_mem (Submodule.smul_mem _ _ hv₀) hv₁, fun i => a.coeff 0 * w₀ i, ?_, fun i => ?_⟩`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 735, line 747 here): `have hFC : F i₀ = C (coeff 0 (F i₀)) := by` is replaced by `have hFC : F i₀ = C ((F i₀).coeff 0) := by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 737, line 749 here): `have hx : coeff 0 (F i₀) ≠ 0 := fun hx => hi₀ (by rw [hFC, hx, C_0])` is replaced by `have hx : (F i₀).coeff 0 ≠ 0 := fun hx => hi₀ (by rw [hFC, hx, C_0])`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 776, line 788 here): `∑ u ∈ q.support, monomial u (f (coeff u q))` is replaced by `∑ u ∈ q.support, monomial u (f (q.coeff u))`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 778, line 790 here): `theorem coeff_Λ (f : L →ₗ[K] K) (q : MvPolynomial σ L) (u : σ →₀ ℕ) : coeff u (Λ L f q) = f (coeff u q) := by` is replaced by `theorem coeff_Λ (f : L →ₗ[K] K) (q : MvPolynomial σ L) (u : σ →₀ ℕ) : (Λ L f q).coeff u = f (q.coeff u) := by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 876, line 888 here): `∑ u ∈ b.support, monomial u (1 : K) * Λ L (f ∘ₗ LinearMap.mulLeft K (coeff u b)) (y i) := by` is replaced by `∑ u ∈ b.support, monomial u (1 : K) * Λ L (f ∘ₗ LinearMap.mulLeft K (b.coeff u)) (y i) := by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 882, line 894 here): `have : (monomial u (coeff u b) : MvPolynomial (Fin (n + 1)) L) =` is replaced by `have : (monomial u (b.coeff u) : MvPolynomial (Fin (n + 1)) L) =`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 883, line 895 here): `map (algebraMap K L) (monomial u 1) * C (coeff u b) := by` is replaced by `map (algebraMap K L) (monomial u 1) * C (b.coeff u) := by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 887, line 899 here): `(monomial u (1 : K)) • fun i => Λ L (f ∘ₗ LinearMap.mulLeft K (coeff u b)) (y i) := by` is replaced by `(monomial u (1 : K)) • fun i => Λ L (f ∘ₗ LinearMap.mulLeft K (b.coeff u)) (y i) := by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 644, line 656 here): `rw [Pi.zero_apply, coeff_zero]` is replaced by `rw [Pi.zero_apply, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]`. In the project's Mathlib the lemma `MvPolynomial.coeff_zero` (FLT: `coeff m 0 = 0`) is replaced by `AddMonoidAlgebra.coeff_zero : (0 : R[M]).coeff = 0`, an equality of finitely supported functions; it is followed by `Finsupp.coe_zero` and `Pi.zero_apply` to evaluate at `m`, which gives the FLT rewrite.
- Manual edit for Mathlib drift (FLT line 792, line 804 here): `ext u; simp only [coeff_Λ, coeff_add, map_add]` is replaced by `ext u; simp only [coeff_Λ, AddMonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply, map_add]`. In the project's Mathlib the lemma `MvPolynomial.coeff_add` (FLT: `coeff m (p + q) = coeff m p + coeff m q`) is replaced by `AddMonoidAlgebra.coeff_add : (p + q).coeff = p.coeff + q.coeff`, an equality of finitely supported functions, followed by `Finsupp.coe_add` and `Pi.add_apply`.
- Manual edit for Mathlib drift (FLT line 789, line 801 here): `ext u; rw [coeff_Λ, coeff_zero, coeff_zero, map_zero]` is replaced by `ext u; rw [coeff_Λ, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply, map_zero]`. In the project's Mathlib the lemma `MvPolynomial.coeff_zero` (FLT: `coeff m 0 = 0`) is replaced by `AddMonoidAlgebra.coeff_zero : (0 : R[M]).coeff = 0`, an equality of finitely supported functions; it is followed by `Finsupp.coe_zero` and `Pi.zero_apply` to evaluate at `m`, which gives the FLT rewrite.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 21 here); in 5 lines the replacements `Type` (universe 0) → `Type uz` (5 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le`. Statement. `MvPolynomial.relation_mem_span_of_forall_finrank_piece_succ_le`: let `F₁, …, F_g` be forms of degree `m` generating an
ideal whose growth from degree `m` to `m + 1` is maximal among ideals generated in degree `m` with the same `h(m)`. Then
every homogeneous relation `Σ cᵢ Fᵢ = 0` is generated by relations of degree `≤ 1` (linear syzygies).

Proof. Sections `Core`, `Pieces`: reductions (`claimA`, `core`, `Ik`). Section `Transport` and `Descent`: dimensions and
relations are compatible with field extension (ported `HilbertFunctor.exists_linearEquiv_baseChange_piece_map`,
`Λ`, `descend`), so `K` may be assumed infinite (section `InfiniteField`). Section `Hyperplane`: for a generic linear
form `ℓ` (ported `MvPolynomial.exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le`, Macaulay's bound,
lex-segment comparison), `ℓ` is a nonzerodivisor (ported
`MvPolynomial.exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow`) and restricting to the
hyperplane `ℓ = 0` (`phi`, `psi`, `ker_phi`) gives the same situation in one variable fewer. Induction on the number of
variables (section `Assembly`), with the degree-zero case separately (section `DegreeZero`): a relation is reduced
modulo `ℓ`, lifted from the hyperplane by the induction hypothesis (`lift_linear_relation`), and the remainder is
divisible by `ℓ` and of lower degree.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.decompose_eq`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.hc_mul_left_of_le`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.hc_mul_left_of_not_le`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.hc_mul_right_of_le`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.hc_of_isHomogeneous_self`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.hc_of_isHomogeneous_ne`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.map_homogeneousComponent`
- def `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.hcv`
- def `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.genSet`
- def `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.V`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.rel_of_mem_V`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.hcv_mem`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.sub_C_coeff_zero_mem`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.lift_linear_relation`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.claimA`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.core`
- def `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.Ik`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.mem_Ik`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.Ik_mono`
- scoped instance `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.finite_homogeneousSubmodule`
- scoped instance `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.finite_piece`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.finrank_piece_add`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.finrank_piece_eq_zero_of_forall`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.span_homogeneous`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.homogeneous_of_gen`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.homogeneous_sup`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.finrank_piece_succ_eq_add`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.finrank_homogeneousSubmodule`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.finrank_homogeneousSubmodule_le`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.finrank_piece_le`
- def `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.ell`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.ell_def`
- def `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.gsub`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.gsub_castSucc`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.gsub_last`
- def `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.phi`
- def `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.psi`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.phi_X`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.phi_psi`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.phi_surjective`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.gsub_isHomogeneous`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.phi_isHomogeneous`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.psi_isHomogeneous`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.ell_isHomogeneous`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.eval_ell`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.ell_ne_zero`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.phi_ell`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.ker_phi`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.finrank_piece_transport`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.rel_mem_V_fin_zero`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.exists_eval_ne_zero`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.span_range_generated`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.infinite_main`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.hcol_of_degree_zero`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.zero_degree_main`
- def `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.Λ`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.coeff_Λ`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.Λ_zero`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.Λ_add`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.Λ_sum`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.Λ_map_mul`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.Λ_C_mul`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.Λ_map`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.Λ_isHomogeneous`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.exists_functional_one`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.descend`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.finrank_piece_map`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore.main`
- theorem `P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_finrank_piece_succ_le_macaulayPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map` (same contribution).
Other imports: `Mathlib`.
