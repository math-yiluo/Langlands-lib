import Langlands.GroupScheme.Cartier.AlgClosedCharacterSeparation

/-! # Closed immersions detected on points of an étale scheme -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.FiniteEtale

open Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable {K : Type u} [Field K]

/-- Sections of an étale scheme over a separably closed field are determined by
their values at rational points. -/
lemma section_ext_of_pointValue_of_isSepClosed [IsSepClosed K]
    {X : Over (Spec (CommRingCat.of K))} [Etale X.hom]
    {s t : Γ(X.left, ⊤)}
    (h : ∀ a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X,
      Cartier.pointValue a s = Cartier.pointValue a t) : s = t := by
  have : IsReduced X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      K X.left X.hom
  rw [← sub_eq_zero]
  apply eq_zero_of_basicOpen_eq_bot
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨l, hl, rfl⟩ := Scheme.exists_fac_of_etale_of_isSepClosed X.hom (𝟙 _) x
    (Subsingleton.elim _ _)
  let a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X := Over.homMk l hl
  have h0 : l.appTop (s - t) = 0 := by
    apply (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom).1
    have := h a
    rw [← sub_eq_zero, ← map_sub] at this
    simpa [Cartier.pointValue, a] using this
  have hmem : (default : Spec (CommRingCat.of K)) ∈
      l ⁻¹ᵁ X.left.basicOpen (s - t) := hx
  rw [Scheme.preimage_basicOpen] at hmem
  change (default : Spec (CommRingCat.of K)) ∈
    (Spec (CommRingCat.of K)).basicOpen (l.appTop (s - t)) at hmem
  rw [h0, Scheme.basicOpen_zero] at hmem
  exact absurd hmem (by simp)

lemma pointValue_comp {X Y : Over (Spec (CommRingCat.of K))}
    (a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X) (f : X ⟶ Y)
    (s : Γ(Y.left, ⊤)) :
    Cartier.pointValue a (f.left.appTop s) = Cartier.pointValue (a ≫ f) s := by
  simp [Cartier.pointValue]

/-- If a map to an affine scheme is injective on a finite set of rational
points, functions on the target realize any prescribed values at those points. -/
lemma exists_section_target_pointValue {X Y : Over (Spec (CommRingCat.of K))}
    [IsAffine Y.left] [Finite (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X)]
    (f : X ⟶ Y)
    (hf : Function.Injective fun a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X => a ≫ f)
    (c : (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X) → K) :
    ∃ s : Γ(Y.left, ⊤), ∀ a, Cartier.pointValue (a ≫ f) s = c a := by
  classical
  have := Fintype.ofFinite (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X)
  have hsep : ∀ a b : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X, a ≠ b →
      ∃ r : Γ(Y.left, ⊤), Cartier.pointValue (a ≫ f) r = 1 ∧
        Cartier.pointValue (b ≫ f) r = 0 := by
    intro a b hab
    obtain ⟨r, hr⟩ := Cartier.exists_pointValue_ne (fun h => hab (hf h))
    have hd : Cartier.pointValue (a ≫ f) r - Cartier.pointValue (b ≫ f) r ≠ 0 :=
      sub_ne_zero.mpr hr
    refine ⟨(r - Cartier.constants Y (Cartier.pointValue (b ≫ f) r)) *
      Cartier.constants Y
        (Cartier.pointValue (a ≫ f) r - Cartier.pointValue (b ≫ f) r)⁻¹, ?_, ?_⟩
    · rw [map_mul, map_sub, Cartier.pointValue_constants, Cartier.pointValue_constants,
        mul_inv_cancel₀ hd]
    · rw [map_mul, map_sub, Cartier.pointValue_constants, sub_self, zero_mul]
  choose! e he using hsep
  have hδ : ∀ a b : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X,
      Cartier.pointValue (b ≫ f) (∏ b' ∈ Finset.univ.erase a, e a b') =
        if b = a then 1 else 0 := by
    intro a b
    rw [map_prod]
    split_ifs with hba
    · subst hba
      exact Finset.prod_eq_one fun b' hb' => (he b b' (Finset.ne_of_mem_erase hb').symm).1
    · exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hba, Finset.mem_univ b⟩)
        (he a b (Ne.symm hba)).2
  refine ⟨∑ a, Cartier.constants Y (c a) *
    ∏ b' ∈ Finset.univ.erase a, e a b', fun b => ?_⟩
  simp only [map_sum, map_mul, Cartier.pointValue_constants, hδ, mul_ite, mul_one, mul_zero]
  simp

/-- A morphism from an affine étale scheme with finitely many rational points
over a separably closed field to an affine scheme is a closed immersion if it is
injective on rational points. -/
theorem isClosedImmersion_of_injective_points [IsSepClosed K]
    {X Y : Over (Spec (CommRingCat.of K))}
    [IsAffine X.left] [IsAffine Y.left] [Etale X.hom]
    [Finite (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X)]
    (f : X ⟶ Y)
    (hf : Function.Injective fun a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X => a ≫ f) :
    IsClosedImmersion f.left := by
  apply IsClosedImmersion.of_surjective_of_isAffine
  intro s
  obtain ⟨t, ht⟩ := exists_section_target_pointValue f hf (fun a => Cartier.pointValue a s)
  refine ⟨t, ?_⟩
  apply section_ext_of_pointValue_of_isSepClosed
  intro a
  rw [pointValue_comp, ht a]

end Langlands.AlgebraicGeometry.FiniteEtale
