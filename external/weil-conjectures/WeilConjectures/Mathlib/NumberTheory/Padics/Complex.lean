/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Complex.Cardinality
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Classification
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.Topology.Algebra.Module.Cardinality
public import WeilConjectures.Mathlib.FieldTheory.IsAlgClosed.Classification

/-!
# `ℚ̄_p` is abstractly isomorphic to `ℂ`

The field `ℚ_[p]` has the cardinality of the continuum: it is a complete nontrivially normed
field, so it has at least continuum many elements, and it is a quotient of the Cauchy sequences
of rationals, so it has at most that many. Its algebraic closure `PadicAlgCl p` is then an
algebraically closed field of characteristic zero and of cardinality `𝔠`, hence isomorphic to `ℂ`
by the classification of uncountable algebraically closed fields.

In particular field embeddings `ι : ℚ̄_ℓ →+* ℂ`, used to compare `ℓ`-adic eigenvalues with
complex absolute values, exist.

## Main statements

- `Padic.mk_eq_continuum`: `#ℚ_[p] = 𝔠`.
- `PadicAlgCl.mk_eq_continuum`: `#ℚ̄_p = 𝔠`.
- `PadicAlgCl.nonempty_ringEquiv_complex`: `ℚ̄_p ≃+* ℂ`.
- `PadicAlgCl.exists_ringEquiv_complex_extend`: every embedding of a number field `L ⊆ ℚ̄_p`
  into `ℂ` extends to an isomorphism `ℚ̄_p ≃+* ℂ` (blueprint `lemma-reciprocal-roots-zeta--6`).
- `PadicAlgCl.exists_ringEquiv_complex_apply_eq`: an algebraic `β ∈ ℚ̄_p` can be sent to any
  conjugate by an isomorphism `ℚ̄_p ≃+* ℂ`.
-/

@[expose] public section

open Cardinal

variable (p : ℕ) [Fact p.Prime]

/-- The field `ℚ_[p]` has at most continuum many elements: it is a quotient of the Cauchy
sequences of rationals. -/
theorem Padic.mk_le_continuum : #ℚ_[p] ≤ 𝔠 := by
  have h₁ : #ℚ_[p] ≤ #(CauSeq ℚ (padicNorm p)) :=
    Cardinal.mk_le_of_surjective (f := fun f : CauSeq ℚ (padicNorm p) ↦ (Padic.mk f : ℚ_[p]))
      fun x ↦ (Quotient.exists_rep x).imp fun _ hf ↦ hf
  have h₂ : #(CauSeq ℚ (padicNorm p)) ≤ #(ℕ → ℚ) :=
    Cardinal.mk_le_of_injective (f := fun f : CauSeq ℚ (padicNorm p) ↦ (f : ℕ → ℚ))
      fun _ _ h ↦ Subtype.ext h
  have h₃ : #(ℕ → ℚ) = 𝔠 := by
    rw [← Cardinal.power_def, Cardinal.mkRat, Cardinal.mk_nat, Cardinal.aleph0_power_aleph0]
  exact h₁.trans (h₂.trans h₃.le)

/-- The field `ℚ_[p]` has the cardinality of the continuum. -/
theorem Padic.mk_eq_continuum : #ℚ_[p] = 𝔠 :=
  le_antisymm (Padic.mk_le_continuum p) (continuum_le_cardinal_of_nontriviallyNormedField ℚ_[p])

/-- The algebraic closure `ℚ̄_p` of `ℚ_[p]` has the cardinality of the continuum. -/
theorem PadicAlgCl.mk_eq_continuum : #(PadicAlgCl p) = 𝔠 := by
  refine le_antisymm ?_ ?_
  · refine (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)).trans ?_
    exact max_le (Padic.mk_le_continuum p) Cardinal.aleph0_le_continuum
  · rw [← Padic.mk_eq_continuum p]
    exact Cardinal.mk_le_of_injective (algebraMap ℚ_[p] (PadicAlgCl p)).injective

/-- The algebraic closure `ℚ̄_p` of `ℚ_[p]` is isomorphic to `ℂ` as a field: both are
algebraically closed of characteristic zero and of cardinality `𝔠`. -/
theorem PadicAlgCl.nonempty_ringEquiv_complex : Nonempty (PadicAlgCl p ≃+* ℂ) := by
  refine IsAlgClosed.ringEquiv_of_equiv_of_charZero ?_ ?_
  · rw [PadicAlgCl.mk_eq_continuum]
    exact Cardinal.aleph0_lt_continuum
  · rw [← Cardinal.eq, PadicAlgCl.mk_eq_continuum, Cardinal.mk_complex]

/-- There is a field embedding `ℚ̄_p →+* ℂ`. -/
theorem PadicAlgCl.nonempty_ringHom_complex : Nonempty (PadicAlgCl p →+* ℂ) :=
  (PadicAlgCl.nonempty_ringEquiv_complex p).map RingEquiv.toRingHom

/-- Blueprint `lemma-reciprocal-roots-zeta--6` (extension of embeddings): every field embedding
`σ : L → ℂ` of a number field `L ⊆ ℚ̄_p` extends to an abstract field isomorphism
`ι : ℚ̄_p ≃ ℂ`. Both fields are algebraically closed of cardinality `𝔠`, so their transcendence
bases over the countable field `L` (acting on `ℂ` through `σ`) are equipotent
(`IsAlgClosed.exists_ringEquiv_extend`). -/
theorem PadicAlgCl.exists_ringEquiv_complex_extend (L : IntermediateField ℚ (PadicAlgCl p))
    [FiniteDimensional ℚ L] (σ : L →ₐ[ℚ] ℂ) :
    ∃ ι : PadicAlgCl p ≃+* ℂ, ∀ x : L, ι x = σ x := by
  have hL : #L ≤ ℵ₀ := (Algebra.IsAlgebraic.cardinalMk_le_max ℚ L).trans <| by
    rw [Cardinal.mkRat, max_self]
  have hK : ℵ₀ < #(PadicAlgCl p) := by
    rw [PadicAlgCl.mk_eq_continuum]
    exact Cardinal.aleph0_lt_continuum
  have hKL : Nonempty (PadicAlgCl p ≃ ℂ) :=
    Cardinal.eq.1 (by rw [PadicAlgCl.mk_eq_continuum, Cardinal.mk_complex])
  obtain ⟨ι, hι⟩ := IsAlgClosed.exists_ringEquiv_extend hL hK hKL σ.toRingHom
  exact ⟨ι, hι⟩

open IntermediateField in
/-- An element `β ∈ ℚ̄_p` algebraic over `ℚ` can be sent by a field isomorphism `ℚ̄_p ≃+* ℂ` to
any complex root of its minimal polynomial over `ℚ`: embed `ℚ(β)` by `β ↦ z` and extend
(`PadicAlgCl.exists_ringEquiv_complex_extend`, blueprint `lemma-reciprocal-roots-zeta--6`). -/
theorem PadicAlgCl.exists_ringEquiv_complex_apply_eq {β : PadicAlgCl p} (hβ : IsIntegral ℚ β)
    {z : ℂ} (hz : Polynomial.aeval z (minpoly ℚ β) = 0) :
    ∃ ι : PadicAlgCl p ≃+* ℂ, ι β = z := by
  have : FiniteDimensional ℚ ℚ⟮β⟯ := adjoin.finiteDimensional hβ
  let τ : ℚ⟮β⟯ →ₐ[ℚ] ℂ := (adjoin.powerBasis hβ).lift z (by
    rwa [adjoin.powerBasis_gen, minpoly_gen])
  obtain ⟨ι, hι⟩ := PadicAlgCl.exists_ringEquiv_complex_extend p ℚ⟮β⟯ τ
  refine ⟨ι, ?_⟩
  have h := hι (AdjoinSimple.gen ℚ β)
  rw [AdjoinSimple.coe_gen] at h
  rw [h]
  exact (adjoin.powerBasis hβ).lift_gen z _

/-- An element `β ∈ ℚ̄_p` algebraic over `ℚ` can be sent by a field embedding `ℚ̄_p →+* ℂ` to any
complex root of its minimal polynomial over `ℚ`: embed `ℚ(β)` by `β ↦ z` and extend
(`PadicAlgCl.exists_ringEquiv_complex_extend`, blueprint `lemma-reciprocal-roots-zeta--6`). -/
theorem PadicAlgCl.exists_ringHom_complex_apply_eq {β : PadicAlgCl p} (hβ : IsIntegral ℚ β)
    {z : ℂ} (hz : Polynomial.aeval z (minpoly ℚ β) = 0) :
    ∃ ι : PadicAlgCl p →+* ℂ, ι β = z :=
  let ⟨ι, hι⟩ := PadicAlgCl.exists_ringEquiv_complex_apply_eq p hβ hz
  ⟨ι, hι⟩
