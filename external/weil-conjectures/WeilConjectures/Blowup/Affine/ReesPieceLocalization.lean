/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.BaseChange
public import WeilConjectures.Blowup.Affine.ReesGrading

/-!

# Localization of the pieces of the Rees algebra

For a localization `B = A[1/s]` and an ideal `I` of `A`, the degree-`n` piece of the Rees
algebra commutes with base change to `B`:
`B ⊗[A] (reesGrading I n) ≃ₗ[B] reesGrading (I.map (algebraMap A B)) n`.

## Main definitions

- `AlgebraicGeometry.reesGradingEquivPow` — the degree-`n` piece of the Rees algebra is
  isomorphic to `I ^ n`.
- `AlgebraicGeometry.reesGradingLocalizationEquiv` — the base change isomorphism
  (blueprint: `definition-admissible-blow-up--1`).

-/

@[expose] public section

universe u

open TensorProduct

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The degree-`n` piece of the Rees algebra is isomorphic to `I ^ n`, via `x·Xⁿ ↦ x`. -/
noncomputable def reesGradingEquivPow (n : ℕ) : reesGrading I n ≃ₗ[A] ↥(I ^ n) where
  toFun F := ⟨((F : reesAlgebra I) : Polynomial A).coeff n,
    (mem_reesAlgebra_iff I _).mp (F : reesAlgebra I).2 n⟩
  invFun x := ⟨reesMonomial I (x : A) x.2, reesMonomial_mem I _ _⟩
  map_add' F G := by ext; simp
  map_smul' c F := by ext; simp
  left_inv F := by
    obtain ⟨x, hx, hF⟩ := (mem_reesGrading_iff_exists I).mp F.2
    refine Subtype.ext ?_
    simp only [hF, coe_reesMonomial, Polynomial.coeff_monomial_same]
  right_inv x := by ext; simp

@[simp]
lemma coe_reesGradingEquivPow_symm_apply (n : ℕ) (x : ↥(I ^ n)) :
    ((reesGradingEquivPow I n).symm x : reesAlgebra I) = reesMonomial I (x : A) x.2 :=
  rfl

variable {B : Type u} [CommRing B] [Algebra A B] (s : A) [IsLocalization.Away s B]

/-- **Localization of each Rees piece**: for `B = A[1/s]`, base change of the degree-`n` piece
of the Rees algebra of `I` is the degree-`n` piece of the Rees algebra of `I·B`:
`B ⊗[A] R_A(I)_n ≃ₗ[B] R_B(I·B)_n`. Both sides are identified with `B ⊗[A] Iⁿ` and
`(I·B)ⁿ = Iⁿ·B`, and `Iⁿ·B` is the localization of `Iⁿ`.
(blueprint: `definition-admissible-blow-up--1`) -/
noncomputable def reesGradingLocalizationEquiv (n : ℕ) :
    B ⊗[A] reesGrading I n ≃ₗ[B] reesGrading (I.map (algebraMap A B)) n :=
  ((reesGradingEquivPow I n).baseChange A B _ _).trans <|
    ((IsLocalizedModule.isBaseChange (Submonoid.powers s) B
      (Algebra.idealMap B (I ^ n))).equiv.trans
      (LinearEquiv.ofEq _ _ (by rw [Ideal.map_pow]))).trans
    (reesGradingEquivPow (I.map (algebraMap A B)) n).symm

lemma reesGradingLocalizationEquiv_tmul (n : ℕ) (b : B) (x : A) (hx : x ∈ I ^ n) :
    ((reesGradingLocalizationEquiv I s n
      (b ⊗ₜ ⟨reesMonomial I x hx, reesMonomial_mem I x hx⟩) :
        reesAlgebra (I.map (algebraMap A B))) :
        Polynomial B) = Polynomial.monomial n (b * algebraMap A B x) := by
  simp [reesGradingLocalizationEquiv, reesGradingEquivPow, IsBaseChange.equiv_tmul,
    Algebra.idealMap, Algebra.smul_def]
  rfl

end AlgebraicGeometry
