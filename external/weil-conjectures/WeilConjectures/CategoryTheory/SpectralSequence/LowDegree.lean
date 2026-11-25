/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.Exact
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# The exact sequence of low degree terms of a spectral sequence

Let `E` be a first quadrant cohomological spectral sequence starting at the `E₂`-page which
abuts to an `ℕ`-graded object `H`. Then there is an exact sequence of low degree terms
`0 ⟶ E₂^{1,0} ⟶ H¹ ⟶ E₂^{0,1} ⟶ E₂^{2,0}`, the last map being the differential `d₂`.

Indeed, the abutment filtration `H¹ = F⁰ ⊇ F¹ ⊇ F² = 0` has graded pieces
`F¹ ≅ E∞^{1,0} = E₂^{1,0}` and `H¹ / F¹ ≅ E∞^{0,1} = ker (d₂ : E₂^{0,1} ⟶ E₂^{2,0})`, since in the
first quadrant no other differential enters or leaves these spots.

## Main statements

- `CategoryTheory.SpectralSequence.Abutment.exists_lowDegree_exact`: the exact sequence of low
  degree terms.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace SpectralSequence

variable {E : E₂CohomologicalSpectralSequenceNat C} {H : ℕ → C}

/-- On the `E₂`-page, `E₂^{1,0}` is its own homology: no differential enters or leaves it. -/
noncomputable def pageTwoHomologyIsoXOneZero (E : E₂CohomologicalSpectralSequenceNat C) :
    (E.page 2).homology (1, 0) ≅ (E.page 2).X (1, 0) :=
  ((E.page 2).isoHomologyπ _ (1, 0) rfl ((E.page 2).shape _ _ (by
    simp only [ComplexShape.spectralSequenceNat_rel_iff]; lia))).symm ≪≫
    (E.page 2).iCyclesIso (1, 0) _ rfl ((E.page 2).shape _ _ (by
      simp only [ComplexShape.spectralSequenceNat_rel_iff]; lia))

/-- On the `E₂`-page, the homology at `E₂^{0,1}` is the kernel of `d₂ : E₂^{0,1} ⟶ E₂^{2,0}`:
no differential enters this spot. -/
noncomputable def pageTwoHomologyIsoCyclesZeroOne (E : E₂CohomologicalSpectralSequenceNat C) :
    (E.page 2).homology (0, 1) ≅ (E.page 2).cycles (0, 1) :=
  ((E.page 2).isoHomologyπ _ (0, 1) rfl ((E.page 2).shape _ _ (by
    simp only [ComplexShape.spectralSequenceNat_rel_iff]; lia))).symm

/-- `E∞^{1,0} ≅ E₂^{1,0}`. -/
noncomputable def pageInfinityOneZeroIso (E : E₂CohomologicalSpectralSequenceNat C) :
    E.pageInfinity (1, 0) ≅ (E.page 2).X (1, 0) :=
  E.pageXIsoOfEq (1, 0) _ 3 ≪≫ (E.iso 2 3 (1, 0)).symm ≪≫ pageTwoHomologyIsoXOneZero E

/-- `E∞^{0,1} ≅ ker (d₂ : E₂^{0,1} ⟶ E₂^{2,0})`. -/
noncomputable def pageInfinityZeroOneIso (E : E₂CohomologicalSpectralSequenceNat C) :
    E.pageInfinity (0, 1) ≅ (E.page 2).cycles (0, 1) :=
  E.pageXIsoOfEq (0, 1) _ 3 ≪≫ (E.iso 2 3 (0, 1)).symm ≪≫ pageTwoHomologyIsoCyclesZeroOne E

/-- **The exact sequence of low degree terms.** If the first quadrant spectral sequence `E`
abuts to `H`, then there is an exact sequence
`0 ⟶ E₂^{1,0} ⟶ H¹ ⟶ E₂^{0,1} ⟶ E₂^{2,0}`, where the last map is the differential `d₂`. -/
theorem Abutment.exists_lowDegree_exact (A : E.Abutment H) :
    ∃ (a : (E.page 2).X (1, 0) ⟶ H 1) (b : H 1 ⟶ (E.page 2).X (0, 1))
      (hab : a ≫ b = 0) (hbc : b ≫ (E.page 2).d (0, 1) (2, 0) = 0),
      Mono a ∧ (ShortComplex.mk a b hab).Exact ∧
        (ShortComplex.mk b ((E.page 2).d (0, 1) (2, 0)) hbc).Exact := by
  let F₀ := A.filtration 1 0
  let F₁ := A.filtration 1 1
  let F₂ := A.filtration 1 (1 + 1)
  have h₀₁ : F₁ ≤ F₀ := A.filtration_succ_le 1 0
  have h₁₂ : F₂ ≤ F₁ := A.filtration_succ_le 1 1
  have : IsIso F₀.arrow := by
    rw [Subobject.isIso_arrow_iff_eq_top]
    exact A.filtration_zero 1
  have hF₂ : IsZero (F₂ : C) := by
    have : F₂ = ⊥ := A.filtration_succ_self 1
    rw [this]
    exact Subobject.botCoeIsoZero.isZero_iff.mpr (isZero_zero C)
  have : IsIso (cokernel.π (Subobject.ofLE _ _ h₁₂)) := by
    rw [hF₂.eq_of_src (Subobject.ofLE _ _ h₁₂) 0]
    infer_instance
  obtain ⟨e₁⟩ := A.nonempty_gradedIso 1 1 0 rfl
  obtain ⟨e₀⟩ := A.nonempty_gradedIso 1 0 1 rfl
  -- `F¹ ≅ E₂^{1,0}`
  let i₁ : (F₁ : C) ≅ (E.page 2).X (1, 0) :=
    asIso (cokernel.π (Subobject.ofLE _ _ h₁₂)) ≪≫ e₁ ≪≫ pageInfinityOneZeroIso E
  -- `H¹ ↠ H¹ / F¹ ≅ ker d₂`
  let π : H 1 ⟶ (E.page 2).cycles (0, 1) :=
    inv F₀.arrow ≫ cokernel.π (Subobject.ofLE _ _ h₀₁) ≫ e₀.hom ≫ (pageInfinityZeroOneIso E).hom
  have hπ : Epi π := by dsimp only [π]; infer_instance
  have hrel : (ComplexShape.spectralSequenceNat ⟨2, 1 - 2⟩).next (0, 1) = (2, 0) :=
    (ComplexShape.spectralSequenceNat ⟨2, 1 - 2⟩).next_eq' (by
      simp only [ComplexShape.spectralSequenceNat_rel_iff]; lia)
  refine ⟨i₁.inv ≫ F₁.arrow, π ≫ (E.page 2).iCycles (0, 1), ?_, by simp, inferInstance, ?_, ?_⟩
  · have : F₁.arrow ≫ inv F₀.arrow = Subobject.ofLE _ _ h₀₁ := by
      rw [IsIso.comp_inv_eq, Subobject.ofLE_arrow]
    simp only [π, Category.assoc, reassoc_of% this, cokernel.condition_assoc, zero_comp,
      comp_zero]
  · have hS : (ShortComplex.mk _ _ (cokernel.condition (Subobject.ofLE _ _ h₀₁))).Exact :=
      ShortComplex.exact_cokernel _
    refine (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      { τ₁ := i₁.hom, τ₂ := F₀.arrow, τ₃ := e₀.hom ≫ (pageInfinityZeroOneIso E).hom ≫
          (E.page 2).iCycles (0, 1)
        comm₁₂ := by simp
        comm₂₃ := by simp [π] }).1 hS
  · have hS : (ShortComplex.mk _ _ ((E.page 2).iCycles_d (0, 1) (2, 0))).Exact :=
      ShortComplex.exact_of_f_is_kernel _ ((E.page 2).cyclesIsKernel (0, 1) (2, 0) hrel)
    let φ : ShortComplex.mk (π ≫ (E.page 2).iCycles (0, 1)) ((E.page 2).d (0, 1) (2, 0))
        (by simp) ⟶ ShortComplex.mk _ _ ((E.page 2).iCycles_d (0, 1) (2, 0)) :=
      { τ₁ := π, τ₂ := 𝟙 _, τ₃ := 𝟙 _ }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hS

end SpectralSequence

end CategoryTheory
