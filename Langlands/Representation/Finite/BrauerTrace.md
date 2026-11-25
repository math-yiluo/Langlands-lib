# Brauer's induction theorem, trace form

`Langlands.Representation.Finite.BrauerTrace`. The trace of a complex matrix representation of a
finite group is an integral combination of class functions induced from linear characters of
subgroups. This is the function-level form of Brauer's theorem. `BrauerLatticeProof` carries it to the
Library's representation classes as
`Langlands.FiniteRep.BrauerLattice.characterLattice : IntegralBrauerCharacterLatticeStatement G`.

## Statement

In namespace `Langlands.FiniteRep.BrauerTrace`, with `open scoped Classical MatrixGroups`:

```lean
theorem exists_trace_eq_sum_zsmul_induced_linearCharacter
    {G : Type u} [Group G] [Fintype G] {n : ℕ} (ρ : G →* GL (Fin n) ℂ) :
    ∃ (k : ℕ) (H : Fin k → Subgroup G) (ψ : (i : Fin k) → (H i →* ℂˣ)) (a : Fin k → ℤ),
      ∀ g : G, ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
        ∑ i : Fin k, (a i : ℂ) * ((Nat.card (H i) : ℂ)⁻¹ *
          ∑ x : G, if hx : x⁻¹ * g * x ∈ H i then (((ψ i) ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ) else 0)
```

In words: there are subgroups `H i`, linear characters `ψ i : H i →* ℂˣ` and integers `a i` with
`trace ρ(g) = ∑ᵢ a i · Ind_{H i}^G (ψ i) (g)`, the induced class function written out as the
normalized sum over `G` (the same formula as `inducedClassFunction`, `inducedClassFunction_ext_apply`).
The coefficients may be negative; the rank `n` may be zero.

## Proof

- `matrixCharacter ρ` is `g ↦ trace (ρ g)`; it is conjugation invariant (`matrixCharacter_conj`).
- `exists_matrixCharacter_eq_sum_zsmul`: by Solomon's theorem over `ℂ`
  (`Solomon.exists_one_eq_sum_zsmul_inducedClassFunction_one_complex`),
  `1 = ∑ a i · inducedClassFunction (H i) 1` with `H i` hyperelementary. Multiplying by the class
  function `matrixCharacter ρ` and using `inducedClassFunction_mul_of_conj_invariant` gives
  `matrixCharacter ρ = ∑ a i · inducedClassFunction (H i) (matrixCharacter ρ)`.
- `exists_inducedClassFunction_matrixCharacter_eq_sum`: for a hyperelementary `H` with cyclic normal
  `C`, the subgroup `C.subgroupOf H` of `H` is normal and commutative, and every element of `H` has a
  `q`-power in it; `MonomialTrace.exists_trace_eq_sum_inducedClassFunction_linearCharacter` applied to
  `ρ` restricted to `H` writes its trace as a sum of inductions of linear characters `ψ j` of subgroups
  `L j` of `H`. Induction in stages (`inducedClassFunction_inducedClassFunction`) turns
  `inducedClassFunction H (matrixCharacter ρ)` into the sum of the inductions from the images of `L j`
  in `G` of the transported characters.
- The double sum over `Σ i, Fin (kf i)` is renumbered by `Fin` (`Fintype.equivFin`,
  `Fintype.sum_sigma`), and `inducedClassFunction_ext_apply` writes each term as in the statement.

## Declarations

In order, all in `Langlands.FiniteRep.BrauerTrace` (section `Proof`, then the theorem): def
`matrixCharacter`; theorem `matrixCharacter_conj`; private def `ext` (extension of a character by
zero); theorems `inducedClassFunction_ext_apply`, `exists_inducedClassFunction_matrixCharacter_eq_sum`,
`exists_matrixCharacter_eq_sum_zsmul`, `exists_trace_eq_sum_zsmul_induced_linearCharacter`.

## Source and licence

Adapted from two files of the Anthropic Lean formalisation of Fermat's Last Theorem (commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`; registered literature
`anthropic-flt-complete-lean-source-6e837e75`); `BrauerProof.solomon_complex` of the second file is in
`SolomonInduction`:

| FLT file | SHA-256 |
| --- | --- |
| `Theorems/Thm_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter.lean` | `e95c9ec70037c816a43048d4d94006ae45547f23ab90b31f78ff02204f37df91` |
| `P2M/Sol/S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter.lean` | `5babda630f44302983a1103552efde23e363517bfd56c9c8cd55ddf797c6f0c2` |

The SHA-256 values are those recorded for the FLT files in the evidence appendix of the Library's
audit `notes/reuse/anthropic-brauer-audit.md`.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`,
`NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. The FLT `ATTRIBUTION.md` does not list
these files as containing third-party material.

### Changes against the FLT files

- Statement and proof are one file. The FLT end theorem
  `BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter` becomes
  `Langlands.FiniteRep.BrauerTrace.exists_trace_eq_sum_zsmul_induced_linearCharacter`, into which the
  FLT `solution` (the same statement) is merged. In the FLT name space `P2MW.S_….BrauerProof`:
  `chi` → `matrixCharacter`, `chi_conj` → `matrixCharacter_conj`, `induced_ext_apply` →
  `inducedClassFunction_ext_apply`, `induced_chi_hyper` → `exists_inducedClassFunction_matrixCharacter_eq_sum`,
  `main` → `exists_matrixCharacter_eq_sum_zsmul`; the private `ext` keeps its name (the FLT
  `p2m_export` alias of it is not needed).
- Universe: `G : Type u` (FLT: `Type`). The proof is unchanged; it uses the universe-polymorphic
  `SolomonInduction` and `MonomialTrace` (the monomial case is applied to the subgroup `H`, a type in
  the same universe as `G`).
- Imports: `SolomonInduction` and `MonomialTrace` (FLT: `Mathlib` and the FLT modules). No option is
  set (FLT: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`, `autoImplicit false`, three linters off).
- In `exists_inducedClassFunction_matrixCharacter_eq_sum` the extract's `change` that states the
  dependent conditional is kept (the audit's compatibility edit 4). With the linters on:
  `matrixCharacter_conj` does not take the unused `[Fintype G]`; a `haveI` for a proposition is `have`;
  a `beta_reduce` that did nothing is removed; deprecated names are replaced (`dif_pos` →
  `dite_eq_left`, …).
- Docstrings and this page are added.

## Literature

Jean-Pierre Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977) (literature
`serre-1977-linear-representations`), read in the library copy:

- §10.5, Theorems 19 and 20, printed p.78 (Theorem 20's proof and the definition of monomial
  characters on p.79): each character of `G` is an integral combination of characters induced from
  characters of elementary subgroups (Theorem 19), and of monomial characters, those induced from
  characters of degree 1 (Theorem 20). The statement here is Theorem 20 for the trace of a matrix
  representation, with the induced characters written by the formula of §7.2 (p.55).
- Serre proves Theorem 19 through `p`-elementary subgroups: §10.1 (p.74), §10.2 Theorems 18 and 18'
  (p.75), §10.3 Lemmas 6–9 (pp.76–77), §10.4 (p.78); elementary groups are nilpotent, hence monomial by
  §8.5 Theorem 16 (pp.66–67). The proof here instead uses hyperelementary subgroups: Solomon's theorem
  (`SolomonInduction`; compare Serre's Theorems 27 and 28 for `Γ_K`-elementary subgroups, §12.6,
  pp.97–98) and the monomial case for groups with a normal commutative subgroup with `p`-group
  quotient (`MonomialTrace`).
- §7.2, Remark (3), p.57: `Ind(ψ · Res φ) = (Ind ψ) · φ`, used to multiply Solomon's identity by the
  character.
