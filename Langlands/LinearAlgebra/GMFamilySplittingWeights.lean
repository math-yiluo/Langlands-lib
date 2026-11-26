import Langlands.LinearAlgebra.GMFamilySplittingReference
import Mathlib.Analysis.Complex.Basic

/-! # Coefficients of the two families of root normals -/

noncomputable section

open Classical Finset
open scoped RealInnerProductSpace

namespace Langlands.GMFamily

open AffineBases

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {R : Finset E} {a : Submodule ℝ E}

/-- The imaginary parameter restricted to the effective space. -/
def effectiveParam (R : Finset E) (a : Submodule ℝ E) (Λ : StrongDual ℝ a) :
    effectiveSpace R a →ₗ[ℝ] ℂ :=
  Complex.I • (Complex.ofRealCLM.toLinearMap.comp (Λ.toLinearMap.comp (Submodule.inclusion inf_le_left)))

@[simp] theorem effectiveParam_simpleNormal (hR : IsRootSet R) (ha : IsLeviSpace R a) {P : Finset E}
    (hP : P ∈ parabolics R a) (Λ : StrongDual ℝ a) (i : simpleRoots a P) :
    effectiveParam R a Λ (simpleNormal hR ha hP i) = Complex.I * (Λ (i : a) : ℂ) := rfl

/-- The undivided root volume over the product of evaluations at the imaginary parameter. -/
def rootWeight {P : Finset E} (I : Finset (simpleRoots a P)) (Λ : StrongDual ℝ a) : ℂ :=
  (gramVolume (fun i : I => ((i : simpleRoots a P) : E)) : ℂ) /
    ∏ i : I, Complex.I * (Λ ((i : simpleRoots a P) : a) : ℂ)

private def disjSumEquiv {ι κ : Type*} (I : Finset ι) (J : Finset κ) :
    ((I : Type _) ⊕ (J : Type _)) ≃ (I.disjSum J : Type _) :=
  (Equiv.sumCongr (Equiv.subtypeEquivRight fun i => (inl_mem_disjSum (s := I) (t := J) (a := i)).symm)
      (Equiv.subtypeEquivRight fun j => (inr_mem_disjSum (s := I) (t := J) (b := j)).symm)).trans
    Equiv.subtypeSum.symm

variable (hR : IsRootSet R) (ha : IsLeviSpace R a) {P₁ P₂ : Finset E}
  (h₁ : P₁ ∈ parabolics R a) (h₂ : P₂ ∈ parabolics R a)

include hR ha in
private theorem normal_subset_linearIndependent {P : Finset E} (hP : P ∈ parabolics R a)
    (I : Finset (simpleRoots a P)) : LinearIndependent ℝ (fun i : I => ((i : simpleRoots a P) : E)) :=
  ((linearIndependent_simpleRoots hR ha hP).map' a.subtype (LinearMap.ker_eq_bot.mpr a.injective_subtype)).comp
    (fun i : I => i.val) Subtype.val_injective

private theorem disjSum_of_normals (I : Finset (simpleRoots a P₁)) (J : Finset (simpleRoots a P₂)) :
    (fun i : I.disjSum J => pairedNormals hR ha h₁ h₂ i) ∘ disjSumEquiv I J =
      Sum.elim (fun i : I => simpleNormal hR ha h₁ i) (fun j : J => simpleNormal hR ha h₂ j) := by
  funext i
  cases i <;> rfl

/-- Complementary normal spaces are exactly the subsets which give a basis of the
paired system of inequalities. -/
theorem disjSum_is_basis_iff (I : Finset (simpleRoots a P₁)) (J : Finset (simpleRoots a P₂)) :
    (LinearIndependent ℝ (fun i : I.disjSum J => pairedNormals hR ha h₁ h₂ i) ∧
      Submodule.span ℝ (Set.range fun i : I.disjSum J => pairedNormals hR ha h₁ h₂ i) = ⊤) ↔
        dCoeff R a (normalFlat P₁ I) (normalFlat P₂ J) ≠ 0 := by
  let V := effectiveSpace R a
  let w := Sum.elim (fun i : I => simpleNormal hR ha h₁ i) (fun j : J => simpleNormal hR ha h₂ j)
  let w' := Sum.elim (fun i : I => ((i : simpleRoots a P₁) : E)) (fun j : J => ((j : simpleRoots a P₂) : E))
  have he : V.subtype ∘ w = w' := by funext i; cases i <;> rfl
  have hspan : Submodule.span ℝ (Set.range w') = normalSpan P₁ I ⊔ normalSpan P₂ J := by
    rw [show Set.range w' = _ from Set.Sum.elim_range _ _, Submodule.span_union]
    rfl
  have hnorm : LinearIndependent ℝ w ↔ Disjoint (normalSpan P₁ I) (normalSpan P₂ J) := by
    constructor
    · intro h
      have h' := h.map' V.subtype (LinearMap.ker_eq_bot.mpr V.injective_subtype)
      rw [he] at h'
      exact (linearIndependent_sum.mp h').2.2
    · intro h
      apply LinearIndependent.of_comp V.subtype
      rw [he]
      exact (normal_subset_linearIndependent hR ha h₁ I).sum_type
        (normal_subset_linearIndependent hR ha h₂ J) h
  have hwhole : Submodule.span ℝ (Set.range w) = ⊤ ↔ normalSpan P₁ I ⊔ normalSpan P₂ J = V := by
    rw [← hspan, ← he, Set.range_comp, Submodule.span_image]
    constructor
    · intro h
      rw [h, Submodule.map_top, Submodule.range_subtype]
    · intro h
      apply Submodule.map_injective_of_injective V.injective_subtype
      simpa only [Submodule.map_top, Submodule.range_subtype] using h
  have hw : (fun i : I.disjSum J => pairedNormals hR ha h₁ h₂ i) ∘ disjSumEquiv I J = w :=
    disjSum_of_normals hR ha h₁ h₂ I J
  have hlin : LinearIndependent ℝ (fun i : I.disjSum J => pairedNormals hR ha h₁ h₂ i) ↔
      LinearIndependent ℝ w := by rw [← hw]; exact (linearIndependent_equiv _).symm
  have hs : Set.range w = Set.range (fun i : I.disjSum J => pairedNormals hR ha h₁ h₂ i) := by
    rw [← hw, (disjSumEquiv I J).surjective.range_comp]
  rw [hlin, ← hs, hnorm, hwhole, dCoeff, inf_orthogonal_normalFlat, inf_orthogonal_normalFlat]
  exact (measureFactor_ne_zero_iff (normalSpan_le hR ha h₁ I) (normalSpan_le hR ha h₂ J)).symm

/-- The determinant of the combined basis gives the product of the local weights times `dCoeff`. -/
theorem normalizedWeight_disjSum (I : Finset (simpleRoots a P₁)) (J : Finset (simpleRoots a P₂))
    (Λ : StrongDual ℝ a) (B : BasisIndex (pairedNormals hR ha h₁ h₂)) (hB : B.val = I.disjSum J) :
    normalizedWeight (pairedNormals hR ha h₁ h₂) (effectiveParam R a Λ) B =
      (dCoeff R a (normalFlat P₁ I) (normalFlat P₂ J) : ℂ) * rootWeight I Λ * rootWeight J Λ := by
  let v := pairedNormals hR ha h₁ h₂
  let e := disjSumEquiv I J
  let w₁ : I → E := fun i => ((i : simpleRoots a P₁) : E)
  let w₂ : J → E := fun j => ((j : simpleRoots a P₂) : E)
  let b : Module.Basis I ℝ (normalSpan P₁ I) := Module.Basis.span (normal_subset_linearIndependent hR ha h₁ I)
  let c : Module.Basis J ℝ (normalSpan P₂ J) := Module.Basis.span (normal_subset_linearIndependent hR ha h₂ J)
  have hb' : (fun i : I => ((b i : normalSpan P₁ I) : E)) = w₁ :=
    funext (Module.Basis.coe_span_apply _)
  have hc' : (fun j : J => ((c j : normalSpan P₂ J) : E)) = w₂ :=
    funext (Module.Basis.coe_span_apply _)
  have hdim : Module.finrank ℝ (normalSpan P₁ I) + Module.finrank ℝ (normalSpan P₂ J) =
      Module.finrank ℝ (effectiveSpace R a) := by
    rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis c, ← card_basisIndex v B, hB,
      card_disjSum, Fintype.card_coe, Fintype.card_coe]
  have hg : gramVolume (fun i : I.disjSum J => (v i : E)) =
      dCoeff R a (normalFlat P₁ I) (normalFlat P₂ J) * gramVolume w₁ * gramVolume w₂ := by
    rw [← gramVolume_reindex e _]
    have he : (fun i : I.disjSum J => (v i : E)) ∘ e = Sum.elim w₁ w₂ := by funext i; cases i <;> rfl
    rw [he, dCoeff, inf_orthogonal_normalFlat, inf_orthogonal_normalFlat]
    simpa only [hb', hc'] using (show gramVolume (Sum.elim (fun i : I => ((b i : normalSpan P₁ I) : E))
        (fun j : J => ((c j : normalSpan P₂ J) : E))) =
          measureFactor (normalSpan P₁ I) (normalSpan P₂ J) (effectiveSpace R a) *
            gramVolume (fun i : I => ((b i : normalSpan P₁ I) : E)) *
              gramVolume (fun j : J => ((c j : normalSpan P₂ J) : E)) from
        gramVolume_sum_eq_measureFactor b c hdim)
  unfold normalizedWeight
  have he : (∏ i : I.disjSum J, effectiveParam R a Λ (v i)) =
      (∏ i : I, Complex.I * (Λ ((i : simpleRoots a P₁) : a) : ℂ)) *
        (∏ j : J, Complex.I * (Λ ((j : simpleRoots a P₂) : a) : ℂ)) := by
    rw [← e.prod_comp (fun i : I.disjSum J => effectiveParam R a Λ (v i)), Fintype.prod_sum_type]
    rfl
  rw [hB]
  change ((gramVolume (fun i : I.disjSum J => (v i : E)) : ℝ) : ℂ) /
      (∏ i : I.disjSum J, effectiveParam R a Λ (v i)) = _
  rw [hg, he, Complex.ofReal_mul, Complex.ofReal_mul, rootWeight, rootWeight, div_eq_mul_inv,
    div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

end Langlands.GMFamily
