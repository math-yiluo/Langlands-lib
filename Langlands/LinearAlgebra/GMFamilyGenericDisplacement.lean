import Langlands.LinearAlgebra.GMFamilyFaceRestriction
import Langlands.LinearAlgebra.GMFamilySchwartzExtension
import Langlands.LinearAlgebra.GMFamilyAlternateSplittingProof
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Points of `i(𝔞_M^G)^*` off the walls

`OffWalls R a Λ` says that `Λ` does not vanish on the restriction to `a` of any root that is
nonzero on `a`. Off the walls the denominators `θ_S` of the chambers of every Levi root subset
are nonzero, and almost every point of `𝔞_M^G` is off the walls. -/

noncomputable section

open scoped RealInnerProductSpace Topology
open Finset Classical Filter MeasureTheory

namespace Langlands.GMFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {R : Finset E} {a : Submodule ℝ E}

omit [FiniteDimensional ℝ E] in
theorem dualParam_apply (x : relativeSpace R a) (v : a) :
    dualParam R a x v = ⟪(x : E), (v : E)⟫ := rfl

omit [FiniteDimensional ℝ E] in
theorem continuous_dualParam : Continuous (dualParam R a) :=
  (innerSL ℝ).continuous.comp (continuous_subtype_val.subtype_mk _)

omit [FiniteDimensional ℝ E] in
theorem dualParam_zero : dualParam R a 0 = 0 := by
  ext v
  simp [dualParam_apply]

omit [FiniteDimensional ℝ E] in
theorem root_mem_orthogonal_centralSpace {α : E} (hα : α ∈ R) : α ∈ (centralSpace R)ᗮ := by
  intro z hz
  rw [real_inner_comm]
  exact (mem_centralSpace_iff.mp hz) α hα

/-- The restriction to a Levi space of a root lies in the orthogonal complement of `𝔞_G`. -/
theorem restrictedRoot_mem_orthogonal_centralSpace {L : Submodule ℝ E} (hL : centralSpace R ≤ L)
    {α : E} (hα : α ∈ R) : (restrictedRoot L α : E) ∈ (centralSpace R)ᗮ := by
  intro z hz
  have h : ⟪(restrictedRoot L α : E), z⟫ = ⟪α, z⟫ := inner_restrictedRoot_subtype L α ⟨z, hL hz⟩
  rw [real_inner_comm, h]
  exact (mem_centralSpace_iff.mp hz) α hα

/-- `Λ` avoids every wall: `Λ(α|_a) ≠ 0` for every root `α` whose restriction `α|_a`
(`restrictedRoot a α`) is nonzero. -/
def OffWalls (R : Finset E) (a : Submodule ℝ E) (Λ : StrongDual ℝ a) : Prop :=
  ∀ α ∈ R, restrictedRoot a α ≠ 0 → Λ (restrictedRoot a α) ≠ 0

/-- Off the walls of `R`, the denominators `θ_S(Λ)` are nonzero for the chambers `S` of `a` for any
root set `R' ⊆ R` of which `a` is a Levi space. -/
theorem theta_ne_zero_of_offWalls {R' : Finset E} (hR' : IsRootSet R') (ha' : IsLeviSpace R' a)
    (hsub : R' ⊆ R) {S : Finset E} (hS : S ∈ parabolics R' a) {Λ : StrongDual ℝ a}
    (hΛ : OffWalls R a Λ) : theta a S Λ ≠ 0 := by
  have hli : LinearIndependent ℝ (fun v : simpleRoots a S => (v : a)) :=
    linearIndependent_simpleRoots hR' ha' hS
  have hliE : LinearIndependent ℝ (fun v : simpleRoots a S => ((v : a) : E)) :=
    hli.map' a.subtype (LinearMap.ker_eq_bot.mpr a.injective_subtype)
  have hg := ((gramVolume_pos_iff _).mpr hliE).ne'
  refine mul_ne_zero (inv_ne_zero (by exact_mod_cast hg))
    (Finset.prod_ne_zero_iff.mpr fun v _ => mul_ne_zero Complex.I_ne_zero ?_)
  obtain ⟨α, hα, hαv⟩ := Finset.mem_image.mp (Finset.mem_filter.mp v.property).1
  have hSR : S ⊆ R' := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  have hne : (v : a) ≠ 0 := hli.ne_zero v
  show (Λ (v : a) : ℂ) ≠ 0
  rw [← hαv] at hne ⊢
  exact_mod_cast hΛ α (hsub (hSR hα)) hne

theorem theta_ne_zero_of_offWalls_face (hR : IsRootSet R) (ha : IsLeviSpace R a) (w : a)
    {S : Finset E} (hS : S ∈ parabolics (leviRoots R (posSet R (w : E))) a) {Λ : StrongDual ℝ a}
    (hΛ : OffWalls R a Λ) : theta a S Λ ≠ 0 :=
  theta_ne_zero_of_offWalls (isRootSet_leviRoots_posSet hR _) (isLeviSpace_leviRoots ha w)
    (Finset.filter_subset _ _) hS hΛ

theorem offWalls_dualParam_iff (x : relativeSpace R a) :
    OffWalls R a (dualParam R a x) ↔ ∀ α ∈ R, restrictedRoot a α ≠ 0 → ⟪(x : E), α⟫ ≠ 0 := by
  have h (α : E) : dualParam R a x (restrictedRoot a α) = ⟪(x : E), α⟫ := by
    have h2 : ⟪(restrictedRoot a α : E), (x : E)⟫ = ⟪α, (x : E)⟫ :=
      inner_restrictedRoot_subtype a α ⟨x, x.property.1⟩
    rw [dualParam_apply, real_inner_comm, h2, real_inner_comm]
  simp only [OffWalls, h]

variable [MeasurableSpace E] [BorelSpace E]

/-- **Almost every point of `𝔞_M^G` is off the walls.** -/
theorem ae_offWalls (ha : IsLeviSpace R a) :
    ∀ᵐ x : relativeSpace R a, OffWalls R a (dualParam R a x) := by
  let V := relativeSpace R a
  let s := R.filter fun α => restrictedRoot a α ≠ 0
  let ℓ (α : E) : V →L[ℝ] ℝ := (innerSL ℝ α).comp V.subtypeL
  have hmem (α : E) (hα : α ∈ R) : (restrictedRoot a α : E) ∈ V :=
    ⟨(restrictedRoot a α).property,
      restrictedRoot_mem_orthogonal_centralSpace (centralSpace_le_of_isLeviSpace ha) hα⟩
  have hker (α : E) (hα : α ∈ s) : LinearMap.ker (ℓ α).toLinearMap ≠ ⊤ := by
    intro htop
    obtain ⟨hαR, hne⟩ := Finset.mem_filter.mp hα
    have h0 : ℓ α ⟨_, hmem α hαR⟩ = 0 := by
      have : (⟨_, hmem α hαR⟩ : V) ∈ LinearMap.ker (ℓ α).toLinearMap := htop ▸ Submodule.mem_top
      exact this
    simp only [ℓ, ContinuousLinearMap.coe_comp, Function.comp_apply, Submodule.subtypeL_apply,
      innerSL_apply_apply] at h0
    have h1 := inner_restrictedRoot_subtype a α (restrictedRoot a α)
    exact hne (inner_self_eq_zero.mp (h1.trans h0))
  have hnull : (volume : Measure V) (⋃ α ∈ s, (LinearMap.ker (ℓ α).toLinearMap : Set V)) = 0 :=
    (measure_biUnion_null_iff s.countable_toSet).mpr fun α hα =>
      Measure.addHaar_submodule volume _ (hker α hα)
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) hnull
  have hx' : ¬ OffWalls R a (dualParam R a x) := hx
  rw [offWalls_dualParam_iff] at hx'
  simp only [not_forall, not_not, exists_prop] at hx'
  obtain ⟨α, hα, hne, h0⟩ := hx'
  refine Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hα, hne⟩)) ?_
  change ℓ α x = 0
  simp only [ℓ, ContinuousLinearMap.coe_comp, Function.comp_apply, Submodule.subtypeL_apply,
    innerSL_apply_apply]
  rw [real_inner_comm]
  exact h0

end Langlands.GMFamily
