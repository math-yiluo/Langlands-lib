# `Langlands.AnthropicFLT.P2M.Sol.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- Manual edit for Mathlib drift (FLT line 107, line 118 here): `rw [coeff_map, coeff_zero]` is replaced by `rw [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]`. In the project's Mathlib the lemma `MvPolynomial.coeff_zero` (FLT: `coeff m 0 = 0`) is replaced by `AddMonoidAlgebra.coeff_zero : (0 : R[M]).coeff = 0`, an equality of finitely supported functions; it is followed by `Finsupp.coe_zero` and `Pi.zero_apply` to evaluate at `m`, which gives the FLT rewrite.
- Manual edit for Mathlib drift (FLT line 161, line 172 here): `sub_self, coeff_zero]` is replaced by `sub_self, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]`. In the project's Mathlib the lemma `MvPolynomial.coeff_zero` (FLT: `coeff m 0 = 0`) is replaced by `AddMonoidAlgebra.coeff_zero : (0 : R[M]).coeff = 0`, an equality of finitely supported functions; it is followed by `Finsupp.coe_zero` and `Pi.zero_apply` to evaluate at `m`, which gives the FLT rewrite.
- Manual edit for Mathlib drift (FLT line 258, line 269 here): `· rw [hm, h0, coeff_zero]` is replaced by `· rw [hm, h0, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]`. In the project's Mathlib the lemma `MvPolynomial.coeff_zero` (FLT: `coeff m 0 = 0`) is replaced by `AddMonoidAlgebra.coeff_zero : (0 : R[M]).coeff = 0`, an equality of finitely supported functions; it is followed by `Finsupp.coe_zero` and `Pi.zero_apply` to evaluate at `m`, which gives the FLT rewrite.
- Manual edit for Mathlib drift (FLT line 259, line 270 here): `· rw [hcon m hm, coeff_zero]` is replaced by `· rw [hcon m hm, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]`. In the project's Mathlib the lemma `MvPolynomial.coeff_zero` (FLT: `coeff m 0 = 0`) is replaced by `AddMonoidAlgebra.coeff_zero : (0 : R[M]).coeff = 0`, an equality of finitely supported functions; it is followed by `Finsupp.coe_zero` and `Pi.zero_apply` to evaluate at `m`, which gives the FLT rewrite.
- Manual edit for Mathlib drift (FLT line 354, line 365 here): `have hφF0 : map φ F ≠ 0 := fun h => hφ₁ (by rw [← coeff_map, h, coeff_zero])` is replaced by `have hφF0 : map φ F ≠ 0 := fun h => hφ₁ (by rw [← coeff_map, h, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply])`. In the project's Mathlib the lemma `MvPolynomial.coeff_zero` (FLT: `coeff m 0 = 0`) is replaced by `AddMonoidAlgebra.coeff_zero : (0 : R[M]).coeff = 0`, an equality of finitely supported functions; it is followed by `Finsupp.coe_zero` and `Pi.zero_apply` to evaluate at `m`, which gives the FLT rewrite.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure`. Statement. `MvPolynomial.exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure` (Bertini–Noether): let `R`
be a domain and `F` a polynomial over `R` in finitely many variables that is irreducible over an algebraic closure of
`Frac R`. There is `c ≠ 0` in `R` such that `φ(F)` is irreducible for every ring map `φ : R → E` to a field with
`φ(c) ≠ 0`.

Proof. Section `System`: factorizations `F = G H` with `G`, `H` of bounded degree are the solutions of a polynomial
system in the coefficients of `G` and `H` (`BddExp`, `genG`, `genH`, `genRel`, `sysIdeal`, `readG`, `readH`;
`bdd_of_dvd`, `totalDegree_map_le` bound the degrees of factors), together with conditions excluding units
(`exists_coeff_ne_zero_of_not_isUnit`, `not_isUnit_of_coeff_ne_zero`). Section `Main`: by irreducibility over the
algebraic closure the system has no solution there, so by the Nullstellensatz the ideal contains a nonzero
constant `c` of `R` (`exists_C_mem_of_forall_exists_aeval_ne_zero`). Section `Final` (`bertiniNoether`): a factorization of
`φ(F)` over `E` would give a solution of the system over `E` (`exists_hom_of_factor`), impossible when `φ(c) ≠ 0`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether.BddExp`
- scoped instance `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether.instFiniteBddExp`
- scoped instance `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether.instFintypeBddExp`
- abbrev `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether.Vars`
- scoped instance `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether.instFiniteVars`
- def `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether.genG`
- def `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether.genH`
- def `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether.genRel`
- def `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether.sysIdeal`
- def `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether.readG`
- def `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether.readH`
- lemma `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether.map_genG`
- lemma `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether.map_genH`
- lemma `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether.map_genRel`
- lemma `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether.coeff_sum_monomial`
- lemma `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether.coeff_readG`
- lemma `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether.coeff_readH`
- lemma `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether.factor_of_forall_mem_sysIdeal`
- lemma `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether.eq_sum_monomial_of_bdd`
- lemma `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether.exists_hom_of_factor`
- theorem `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether.exists_C_mem_of_forall_exists_aeval_ne_zero`
- lemma `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether.exists_coeff_ne_zero_of_not_isUnit`
- lemma `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether.not_isUnit_of_coeff_ne_zero`
- lemma `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether.totalDegree_map_le`
- lemma `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether.bdd_of_dvd`
- theorem `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether.bertiniNoether`
- theorem `P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
