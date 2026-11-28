import Langlands.LinearAlgebra.GMFamiliesStatement
import Langlands.LinearAlgebra.GMFamilySliceCoarse

/-! # Same-field Levi descent for `(G, M)`-families -/

noncomputable section

open scoped RealInnerProductSpace
open Classical Submodule
open Langlands.LinearAlgebra.AffineVertexWeights

universe u

namespace Langlands.GMFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {R : Finset E} {a a₁ : Submodule ℝ E} {ξ : E}

def sliceSum (R : Finset E) (a a₁ : Submodule ℝ E) (ξ : E)
    (c₁ : Finset E → StrongDual ℝ a₁ → ℂ) (Λ : StrongDual ℝ a) : ℂ :=
  ∑ P ∈ parabolics R a₁, c₁ P (extendParam a a₁ Λ) *
    vertexSum (sliceNormal R a a₁ (P := P)) (sliceParameter R Λ) (sliceOffset ξ)

private theorem cM_induced_eq_sliceSum (D : DescentPosition R a a₁ ξ)
    (c₁ : Finset E → StrongDual ℝ a₁ → ℂ) (hc₁ : IsFamily R a₁ c₁)
    (Λ : StrongDual ℝ a) (hΛ : ∀ r ∈ R, restrictedRoot a r ≠ 0 → Λ (restrictedRoot a r) ≠ 0) :
    cM R a (inducedFamily R a a₁ c₁) Λ = sliceSum R a a₁ ξ c₁ Λ := by
  let C := parabolics R a
  let F := parabolics R a₁
  let selected := F.filter (fun P => ∃ S ∈ C, isSliceLift R a a₁ ξ S P)
  let term (P : Finset E) : ℂ := c₁ P (extendParam a a₁ Λ) *
    vertexSum (sliceNormal R a a₁ (P := P)) (sliceParameter R Λ) (sliceOffset ξ)
  have hfilter : (∑ P ∈ selected, term P) = ∑ P ∈ F, term P := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro P hP hn
    by_cases h : ∃ S ∈ C, S ⊆ P
    · obtain ⟨S, hS, hSP⟩ := h
      have hz : ¬ isSliceLift R a a₁ ξ S P := fun hh =>
        hn (Finset.mem_filter.mpr ⟨hP, S, hS, hh⟩)
      simp only [term, vertexSum_eq_of_coarse_extension D hS hP hSP Λ, ite_eq_right hz, mul_zero]
    · simp only [term, vertexSum_eq_zero_of_no_coarse D hP Λ hΛ h, mul_zero]
  change _ = ∑ P ∈ F, term P
  rw [← hfilter, cM]
  let lift (S : Finset E) (hS : S ∈ C) : Finset E :=
    (existsUnique_sliceLift D hS).exists.choose
  have hlift (S : Finset E) (hS : S ∈ C) : lift S hS ∈ F ∧ isSliceLift R a a₁ ξ S (lift S hS) :=
    (existsUnique_sliceLift D hS).exists.choose_spec
  apply Finset.sum_bij lift
  · intro S hS
    exact Finset.mem_filter.mpr ⟨(hlift S hS).1, S, hS, (hlift S hS).2⟩
  · intro S hS T hT h
    exact coarse_chamber_unique D hS hT (hlift S hS).1 (hlift S hS).2.1
      (h.symm ▸ (hlift T hT).2.1)
  · intro P hP
    obtain ⟨hP, S, hS, hSP⟩ := Finset.mem_filter.mp hP
    obtain ⟨Q, _, hu⟩ := existsUnique_sliceLift D hS
    exact ⟨S, hS, (hu _ (hlift S hS)).trans (hu _ ⟨hP, hSP⟩).symm⟩
  · intro S hS
    obtain ⟨hP, hSP⟩ := hlift S hS
    unfold term
    rw [inducedFamily_eq_of_extension D.roots D.le_fine hc₁ hS hP hSP.1,
      vertexSum_eq_of_coarse_extension D hS hP hSP.1, ite_eq_left hSP]

private def relativeChambers (D : DescentPosition R a a₁ ξ) (L : transverseLevis R a a₁) :
    Finset (Finset E) := parabolics (leviRoots R (posSet R (transversePoint D L))) a₁

private abbrev DescentIndex (D : DescentPosition R a a₁ ξ) :=
  Σ L : transverseLevis R a a₁, relativeChambers D L

private def fineChamber (D : DescentPosition R a a₁ ξ) (u : DescentIndex D) : Finset E :=
  posSet R (transversePoint D u.1) ∪ (u.2 : Finset E)

private def relativeWeight (D : DescentPosition R a a₁ ξ) (Λ : StrongDual ℝ a)
    (u : DescentIndex D) : ℂ :=
  (dDescent a (centralSpace R) a₁ u.1 : ℂ) *
    (theta a₁ u.2 (extendParam a a₁ Λ))⁻¹

private theorem fineChamber_spec (D : DescentPosition R a a₁ ξ) (u : DescentIndex D) :
    fineChamber D u ∈ parabolics R a₁ ∧ ∀ r ∈ fineChamber D u, 0 ≤ ⟪r, transversePoint D u.1⟫ :=
  chamber_union_relative D.roots (transverseLevi_le_fine D u.1 (transversePoint_spec D u.1).1.1)
    u.2.prop

private theorem relative_eq_inter (D : DescentPosition R a a₁ ξ) (u : DescentIndex D) :
    (u.2 : Finset E) = fineChamber D u ∩ leviRoots R (posSet R (transversePoint D u.1)) := by
  have hS : (u.2 : Finset E) ⊆ leviRoots R (posSet R (transversePoint D u.1)) :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp u.2.prop).1
  ext r
  constructor
  · intro hr
    exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hr, hS hr⟩
  · intro hr
    obtain ⟨h₁, h₂⟩ := Finset.mem_inter.mp hr
    rcases Finset.mem_union.mp h₁ with hr | hr
    · exact (((Finset.mem_filter.mp h₂).2).1 hr).elim
    · exact hr

set_option maxHeartbeats 800000 in
private theorem sum_relativeWeight_fiber_eq_vertexSum (D : DescentPosition R a a₁ ξ)
    {P : Finset E} (hP : P ∈ parabolics R a₁) (Λ : StrongDual ℝ a) :
    ∑ u ∈ (Finset.univ : Finset (DescentIndex D)).filter (fun u => fineChamber D u = P),
      relativeWeight D Λ u =
      vertexSum (sliceNormal R a a₁ (P := P)) (sliceParameter R Λ) (sliceOffset ξ) := by
  let T := (Finset.univ : Finset (DescentIndex D)).filter (fun u => fineChamber D u = P)
  let v := sliceNormal R a a₁ (P := P)
  have hc (u : DescentIndex D) (hu : u ∈ T) : ∀ r ∈ P, 0 ≤ ⟪r, transversePoint D u.1⟫ :=
    (Finset.mem_filter.mp hu).2 ▸ (fineChamber_spec D u).2
  let b (u : DescentIndex D) (hu : u ∈ T) : BasisIndex v := activeSliceBasis D hP u.1 (hc u hu)
  have hL (u : DescentIndex D) (hu : u ∈ T) : basisTransverseLevi D hP (b u hu) = u.1 :=
    basisTransverseLevi_activeSliceBasis D hP u.1 (hc u hu)
  let eligible := (Finset.univ : Finset (BasisIndex v)).filter
    (fun J => ∀ i ∉ J.val, 0 < J.slack i (sliceOffset ξ))
  have helig : ∑ J ∈ eligible, weight v (sliceParameter R Λ) J =
      vertexSum v (sliceParameter R Λ) (sliceOffset ξ) := by
    simp only [eligible, Finset.sum_filter, vertexSum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> rfl
  change ∑ u ∈ T, relativeWeight D Λ u = vertexSum v (sliceParameter R Λ) (sliceOffset ξ)
  rw [← helig]
  apply Finset.sum_bij b
  · intro u hu
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (basisFeasible_iff D hP _).mpr ?_⟩
    rw [hL u hu]
    exact hc u hu
  · intro u hu t ht he
    have hLt : u.1 = t.1 := (hL u hu).symm.trans ((congrArg (basisTransverseLevi D hP) he).trans (hL t ht))
    have hPt : fineChamber D u = fineChamber D t :=
      (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp ht).2.symm
    cases u with
    | mk L S =>
      cases t with
      | mk L' S' =>
        cases hLt
        apply congrArg (Sigma.mk L)
        apply Subtype.ext
        rw [relative_eq_inter D (⟨L, S⟩ : DescentIndex D),
          relative_eq_inter D (⟨L, S'⟩ : DescentIndex D), hPt]
  · intro J hJ
    let L := basisTransverseLevi D hP J
    let p := transversePoint D L
    have hp : p ∈ a₁ := transverseLevi_le_fine D L (transversePoint_spec D L).1.1
    have hpc : ∀ r ∈ P, 0 ≤ ⟪r, p⟫ := (basisFeasible_iff D hP J).mp (Finset.mem_filter.mp hJ).2
    obtain ⟨hS, hPS⟩ := relative_chamber_of_closed D.roots hP hp hpc
    let u : DescentIndex D := ⟨L, P ∩ leviRoots R (posSet R p), hS⟩
    have hu : u ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPS⟩
    exact ⟨u, hu, activeSliceBasis_basisTransverseLevi D hP J (hc u hu)⟩
  · intro u hu
    have hP' := (Finset.mem_filter.mp hu).2
    unfold b
    rw [weight_activeSliceBasis D hP u.1 (hc u hu) Λ]
    unfold relativeWeight
    congr 1
    rw [relative_eq_inter D u, hP']

set_option maxHeartbeats 800000 in
private theorem sum_levi_eq_sliceSum (D : DescentPosition R a a₁ ξ)
    (c₁ : Finset E → StrongDual ℝ a₁ → ℂ) (Λ : StrongDual ℝ a) :
    ∑ L ∈ leviSpaces R a₁, (dDescent a (centralSpace R) a₁ L : ℂ) *
        cQM R a₁ c₁ (descentSection R a (centralSpace R) ξ L) (extendParam a a₁ Λ) =
      sliceSum R a a₁ ξ c₁ Λ := by
  let H (L : Submodule ℝ E) : ℂ := (dDescent a (centralSpace R) a₁ L : ℂ) *
    cQM R a₁ c₁ (descentSection R a (centralSpace R) ξ L) (extendParam a a₁ Λ)
  let W (u : DescentIndex D) : ℂ :=
    c₁ (fineChamber D u) (extendParam a a₁ Λ) * relativeWeight D Λ u
  calc
    _ = ∑ L : transverseLevis R a a₁, H L := by
      rw [Finset.sum_coe_sort]
      change ∑ L ∈ leviSpaces R a₁, H L = ∑ L ∈ transverseLevis R a a₁, H L
      unfold transverseLevis
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro L _
      by_cases h : dDescent a (centralSpace R) a₁ L = 0 <;> simp [H, h]
    _ = ∑ u : DescentIndex D, W u := by
      rw [Fintype.sum_sigma W]
      apply Finset.sum_congr rfl
      intro L _
      unfold H
      rw [transversePoint_section D L, cQM, Finset.mul_sum]
      let G (S : Finset E) := (dDescent a (centralSpace R) a₁ L : ℂ) *
        (c₁ (posSet R (transversePoint D L) ∪ S) (extendParam a a₁ Λ) *
          (theta a₁ S (extendParam a a₁ Λ))⁻¹)
      change (∑ S ∈ relativeChambers D L, G S) = ∑ S : relativeChambers D L, W ⟨L, S⟩
      rw [← Finset.sum_coe_sort (relativeChambers D L) G]
      apply Finset.sum_congr rfl
      intro S _
      simp only [W, G, fineChamber, relativeWeight]
      ring
    _ = ∑ P ∈ parabolics R a₁, ∑ u ∈ Finset.univ.filter (fun u => fineChamber D u = P), W u :=
      (Finset.sum_fiberwise_of_maps_to (fun u _ => (fineChamber_spec D u).1) W).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro P hP
      rw [← sum_relativeWeight_fiber_eq_vertexSum D hP Λ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      simp only [W, (Finset.mem_filter.mp hu).2]

/-- Arthur's same-field Levi descent formula at the generic parameters of the published target. -/
theorem descentFormula : DescentFormulaStatement.{u} := by
  intro E _ _ _ R a a₁ hR ha₁ ha haa₁ c₁ hc₁ ξ hξ hgen
  let D : DescentPosition R a a₁ ξ := ⟨hR, ha, ha₁, haa₁, hξ, hgen⟩
  refine ⟨(R.image (restrictedRoot a)).erase 0, Finset.notMem_erase _ _, fun Λ hΛ => ?_⟩
  have hp : ∀ r ∈ R, restrictedRoot a r ≠ 0 → Λ (restrictedRoot a r) ≠ 0 := fun r hr hn =>
    hΛ (restrictedRoot a r) (Finset.mem_erase.mpr ⟨hn, Finset.mem_image.mpr ⟨r, hr, rfl⟩⟩)
  exact (cM_induced_eq_sliceSum D c₁ hc₁ Λ hp).trans (sum_levi_eq_sliceSum D c₁ Λ).symm

end Langlands.GMFamily
