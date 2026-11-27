import Langlands.LinearAlgebra.GMFamilyGenericDisplacement

/-! # Splitting points and a displacement in general position

For two Levi spaces `L₁, L₂` with `d_M^G(L₁, L₂) ≠ 0` the decomposition `2ξ = ξ₁ - ξ₂`,
`ξᵢ ∈ 𝔞_{Lᵢ}^G`, of `ξ ∈ 𝔞_M^G` is unique, so `ξᵢ` depends linearly on `ξ`. The conditions of
general position in the alternate splitting formula are therefore the nonvanishing of finitely
many nonzero linear forms, and they hold on a dense set. -/

noncomputable section

open scoped RealInnerProductSpace Topology
open Finset Classical Filter

namespace Langlands.GMFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {R : Finset E} {a : Submodule ℝ E}

theorem restrictedRoot_levi_mem (hR : IsRootSet R) (ha : IsLeviSpace R a) {L : Submodule ℝ E}
    (hL : L ∈ leviSpaces R a) {α : E} (hα : α ∈ R) :
    (restrictedRoot L α : E) ∈ L ⊓ (centralSpace R)ᗮ ∧
      (restrictedRoot L α : E) ∈ relativeSpace R a := by
  have hLa := (mem_leviSpaces_iff hR ha L).mp hL
  have hc := restrictedRoot_mem_orthogonal_centralSpace
    (centralSpace_le_of_isLeviSpace hLa.2) hα
  exact ⟨⟨(restrictedRoot L α).property, hc⟩, ⟨hLa.1 (restrictedRoot L α).property, hc⟩⟩

section SplitPoints

variable (hR : IsRootSet R) (ha : IsLeviSpace R a) {L₁ L₂ : Submodule ℝ E}
  (hL₁ : L₁ ∈ leviSpaces R a) (hL₂ : L₂ ∈ leviSpaces R a) (hd : dCoeff R a L₁ L₂ ≠ 0)

include hR ha hL₁ hL₂ hd

/-- The first splitting point of `ξ`. -/
def splitPoint₁ (ξ : relativeSpace R a) : E :=
  (exists_unique_splitting_points hR ha hL₁ hL₂ hd ξ).choose

/-- The second splitting point of `ξ`. -/
def splitPoint₂ (ξ : relativeSpace R a) : E :=
  (exists_unique_splitting_points hR ha hL₁ hL₂ hd ξ).choose_spec.choose

theorem splitPoint_spec (ξ : relativeSpace R a) :
    splitPoint₁ hR ha hL₁ hL₂ hd ξ ∈ L₁ ⊓ (centralSpace R)ᗮ ∧
      splitPoint₂ hR ha hL₁ hL₂ hd ξ ∈ L₂ ⊓ (centralSpace R)ᗮ ∧
        (2 : ℝ) • (ξ : E) = splitPoint₁ hR ha hL₁ hL₂ hd ξ - splitPoint₂ hR ha hL₁ hL₂ hd ξ :=
  let h := (exists_unique_splitting_points hR ha hL₁ hL₂ hd ξ).choose_spec.choose_spec
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem splitPoint_eq (ξ : relativeSpace R a) {x₁ x₂ : E} (h₁ : x₁ ∈ L₁ ⊓ (centralSpace R)ᗮ)
    (h₂ : x₂ ∈ L₂ ⊓ (centralSpace R)ᗮ) (he : (2 : ℝ) • (ξ : E) = x₁ - x₂) :
    x₁ = splitPoint₁ hR ha hL₁ hL₂ hd ξ ∧ x₂ = splitPoint₂ hR ha hL₁ hL₂ hd ξ :=
  (exists_unique_splitting_points hR ha hL₁ hL₂ hd ξ).choose_spec.choose_spec.2.2.2 x₁ x₂ h₁ h₂ he

/-- The splitting points depend linearly on the displacement. -/
def splitPointLinear₁ : relativeSpace R a →ₗ[ℝ] E where
  toFun := splitPoint₁ hR ha hL₁ hL₂ hd
  map_add' ξ ξ' := by
    obtain ⟨a₁, a₂, ae⟩ := splitPoint_spec hR ha hL₁ hL₂ hd ξ
    obtain ⟨b₁, b₂, be⟩ := splitPoint_spec hR ha hL₁ hL₂ hd ξ'
    refine ((splitPoint_eq hR ha hL₁ hL₂ hd (ξ + ξ') (Submodule.add_mem _ a₁ b₁)
      (Submodule.add_mem _ a₂ b₂) ?_).1).symm
    rw [Submodule.coe_add, smul_add, ae, be]
    abel
  map_smul' c ξ := by
    obtain ⟨a₁, a₂, ae⟩ := splitPoint_spec hR ha hL₁ hL₂ hd ξ
    refine ((splitPoint_eq hR ha hL₁ hL₂ hd (c • ξ) (Submodule.smul_mem _ c a₁)
      (Submodule.smul_mem _ c a₂) ?_).1).symm
    rw [Submodule.coe_smul, smul_comm, ae, smul_sub]

def splitPointLinear₂ : relativeSpace R a →ₗ[ℝ] E where
  toFun := splitPoint₂ hR ha hL₁ hL₂ hd
  map_add' ξ ξ' := by
    obtain ⟨a₁, a₂, ae⟩ := splitPoint_spec hR ha hL₁ hL₂ hd ξ
    obtain ⟨b₁, b₂, be⟩ := splitPoint_spec hR ha hL₁ hL₂ hd ξ'
    refine ((splitPoint_eq hR ha hL₁ hL₂ hd (ξ + ξ') (Submodule.add_mem _ a₁ b₁)
      (Submodule.add_mem _ a₂ b₂) ?_).2).symm
    rw [Submodule.coe_add, smul_add, ae, be]
    abel
  map_smul' c ξ := by
    obtain ⟨a₁, a₂, ae⟩ := splitPoint_spec hR ha hL₁ hL₂ hd ξ
    refine ((splitPoint_eq hR ha hL₁ hL₂ hd (c • ξ) (Submodule.smul_mem _ c a₁)
      (Submodule.smul_mem _ c a₂) ?_).2).symm
    rw [Submodule.coe_smul, smul_comm, ae, smul_sub]

/-- The linear form `ξ ↦ ⟪α, ξ₁⟫` or `ξ ↦ ⟪α, ξ₂⟫`. -/
def splitForm (b : Bool) (α : E) : relativeSpace R a →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((innerₛₗ ℝ α).comp (if b then splitPointLinear₁ hR ha hL₁ hL₂ hd
      else splitPointLinear₂ hR ha hL₁ hL₂ hd))

theorem splitForm_apply (b : Bool) (α : E) (ξ : relativeSpace R a) :
    splitForm hR ha hL₁ hL₂ hd b α ξ =
      ⟪α, if b then splitPoint₁ hR ha hL₁ hL₂ hd ξ else splitPoint₂ hR ha hL₁ hL₂ hd ξ⟫ := by
  cases b <;> rfl

theorem splitForm_ne_zero (b : Bool) {α : E} (hα : α ∈ R)
    (hne : (if b then restrictedRoot L₁ α else restrictedRoot L₂ α : E) ≠ 0) :
    splitForm hR ha hL₁ hL₂ hd b α ≠ 0 := by
  intro hz
  cases b with
  | true =>
    obtain ⟨hm, hV⟩ := restrictedRoot_levi_mem hR ha hL₁ hα
    let ξ₀ : relativeSpace R a := (1 / 2 : ℝ) • ⟨_, hV⟩
    have heq := (splitPoint_eq hR ha hL₁ hL₂ hd ξ₀ hm (Submodule.zero_mem _) (by
      simp only [ξ₀, Submodule.coe_smul, smul_smul, sub_zero]
      norm_num)).1
    have h0 := congrArg (fun T => T ξ₀) hz
    simp only [splitForm_apply, ite_true, zero_apply, ← heq] at h0
    have h1 := inner_restrictedRoot_subtype L₁ α (restrictedRoot L₁ α)
    simp only [ite_true] at hne
    exact hne (by exact_mod_cast (inner_self_eq_zero.mp (h1.trans h0)))
  | false =>
    obtain ⟨hm, hV⟩ := restrictedRoot_levi_mem hR ha hL₂ hα
    let ξ₀ : relativeSpace R a := (-(1 / 2 : ℝ)) • ⟨_, hV⟩
    have heq := (splitPoint_eq hR ha hL₁ hL₂ hd ξ₀ (Submodule.zero_mem _) hm (by
      simp only [ξ₀, Submodule.coe_smul, smul_smul, zero_sub]
      norm_num)).2
    have h0 := congrArg (fun T => T ξ₀) hz
    simp only [splitForm_apply, Bool.false_eq_true, ite_false, zero_apply,
      ← heq] at h0
    have h1 := inner_restrictedRoot_subtype L₂ α (restrictedRoot L₂ α)
    simp only [Bool.false_eq_true, ite_false] at hne
    exact hne (by exact_mod_cast (inner_self_eq_zero.mp (h1.trans h0)))

end SplitPoints

/-- **A displacement in general position.** For every chamber `S₀` there is `ξ ∈ 𝔞_M^G` with
`-2ξ` in the chamber `S₀`, nonzero on every root nonvanishing on `a`, and satisfying the
regularity premise of the alternate splitting formula. -/
theorem exists_generic_displacement (hR : IsRootSet R) (ha : IsLeviSpace R a) {S₀ : Finset E}
    (hS₀ : S₀ ∈ parabolics R a) :
    ∃ ξ : relativeSpace R a, RegularDisplacement R a (ξ : E) ∧
      posSet R (-(2 : ℝ) • (ξ : E)) = S₀ ∧
      ∀ α ∈ R, restrictedRoot a α ≠ 0 → ⟪α, (ξ : E)⟫ ≠ 0 := by
  let V := relativeSpace R a
  obtain ⟨h₀, hh₀, rfl⟩ := mem_parabolics_iff.mp hS₀
  let ι := ((Submodule ℝ E × Submodule ℝ E) × E) × Bool
  let A : Finset ι := ((((leviSpaces R a ×ˢ leviSpaces R a).filter
      (fun L => dCoeff R a L.1 L.2 ≠ 0)) ×ˢ R) ×ˢ (Finset.univ : Finset Bool)).filter
    (fun p => (if p.2 then (restrictedRoot p.1.1.1 p.1.2 : E) else
      (restrictedRoot p.1.1.2 p.1.2 : E)) ≠ 0)
  let B : Finset E := R.filter (fun α => restrictedRoot a α ≠ 0)
  let l : ι ⊕ E → V →L[ℝ] ℝ := Sum.elim
    (fun p => if h : p.1.1.1 ∈ leviSpaces R a ∧ p.1.1.2 ∈ leviSpaces R a ∧
        dCoeff R a p.1.1.1 p.1.1.2 ≠ 0 then splitForm hR ha h.1 h.2.1 h.2.2 p.2 p.1.2 else 0)
    (fun α => (innerSL ℝ α).comp V.subtypeL)
  have hmemA {p : ι} (hp : p ∈ A) : (p.1.1.1 ∈ leviSpaces R a ∧ p.1.1.2 ∈ leviSpaces R a ∧
      dCoeff R a p.1.1.1 p.1.1.2 ≠ 0) ∧ p.1.2 ∈ R ∧
      (if p.2 then (restrictedRoot p.1.1.1 p.1.2 : E) else (restrictedRoot p.1.1.2 p.1.2 : E)) ≠ 0 := by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hp
    obtain ⟨h3, -⟩ := Finset.mem_product.mp h1
    obtain ⟨h4, h5⟩ := Finset.mem_product.mp h3
    obtain ⟨h6, h7⟩ := Finset.mem_filter.mp h4
    obtain ⟨h8, h9⟩ := Finset.mem_product.mp h6
    exact ⟨⟨h8, h9, h7⟩, h5, h2⟩
  have hrootV (α : E) (hα : α ∈ R) : (restrictedRoot a α : E) ∈ V :=
    ⟨(restrictedRoot a α).property,
      restrictedRoot_mem_orthogonal_centralSpace (centralSpace_le_of_isLeviSpace ha) hα⟩
  have hl : ∀ i ∈ A.disjSum B, l i ≠ 0 := by
    intro i hi
    rcases i with p | α
    · have hp := hmemA (Finset.inl_mem_disjSum.mp hi)
      simp only [l, Sum.elim_inl, dite_eq_left hp.1]
      exact splitForm_ne_zero hR ha hp.1.1 hp.1.2.1 hp.1.2.2 p.2 hp.2.1 hp.2.2
    · obtain ⟨hα, hne⟩ := Finset.mem_filter.mp (Finset.inr_mem_disjSum.mp hi)
      intro hz
      have h0 := congrArg (fun T => T ⟨_, hrootV α hα⟩) hz
      simp only [l, Sum.elim_inr, ContinuousLinearMap.coe_comp, Function.comp_apply,
        Submodule.subtypeL_apply, innerSL_apply_apply, zero_apply] at h0
      have h1 := inner_restrictedRoot_subtype a α (restrictedRoot a α)
      exact hne (inner_self_eq_zero.mp (h1.trans h0))
  have hD := dense_nonzero_forms (A.disjSum B) l hl
  -- the open set of displacements with `-2ξ` in the chamber
  let U : Set V := ⋂ α ∈ B, {ξ : V | 0 < ⟪α, h₀⟫ * ⟪α, -(2 : ℝ) • (ξ : E)⟫}
  have hU : IsOpen U := isOpen_biInter_finset fun α _ =>
    isOpen_lt continuous_const (continuous_const.mul (continuous_const.inner
      (continuous_const.smul continuous_subtype_val)))
  -- a point of `U`
  let Z := centralSpace R
  let p₀ : E := Zᗮ.starProjection h₀
  have hp₀Z : h₀ - p₀ ∈ Z := by
    have h := Submodule.sub_starProjection_mem_orthogonal (K := Zᗮ) h₀
    rwa [Submodule.orthogonal_orthogonal] at h
  have hp₀V : p₀ ∈ V := by
    refine ⟨?_, Submodule.starProjection_apply_mem _ _⟩
    have h1 : h₀ - (h₀ - p₀) ∈ a :=
      a.sub_mem hh₀.1 (centralSpace_le_of_isLeviSpace ha hp₀Z)
    simpa using h1
  have hp₀α (α : E) (hα : α ∈ R) : ⟪α, p₀⟫ = ⟪α, h₀⟫ := by
    have h := (root_mem_orthogonal_centralSpace hα) (h₀ - p₀) hp₀Z
    rw [inner_sub_left] at h
    rw [real_inner_comm p₀ α, real_inner_comm h₀ α]
    linarith
  let ξ₀ : V := (-(1 / 2 : ℝ)) • ⟨p₀, hp₀V⟩
  have hξ₀ : ξ₀ ∈ U := by
    refine Set.mem_iInter₂.mpr fun α hα => ?_
    obtain ⟨hαR, hne⟩ := Finset.mem_filter.mp hα
    have h2 : -(2 : ℝ) • (ξ₀ : E) = p₀ := by
      simp only [ξ₀, Submodule.coe_smul, smul_smul]
      norm_num
    simp only [Set.mem_ofPred_eq, h2, hp₀α α hαR]
    exact mul_self_pos.mpr (hh₀.2 α hαR hne)
  obtain ⟨ξ, hξU, hξD⟩ := hD.inter_open_nonempty U hU ⟨ξ₀, hξ₀⟩
  refine ⟨ξ, ?_, ?_, ?_⟩
  · intro L₁ hL₁ L₂ hL₂ hd x₁ x₂ h₁ h₂ he
    obtain ⟨e₁, e₂⟩ := splitPoint_eq hR ha hL₁ hL₂ hd ξ h₁ h₂ he
    refine ⟨⟨h₁.1, fun α hα hne => ?_⟩, ⟨h₂.1, fun α hα hne => ?_⟩⟩
    · let p : ι := (((L₁, L₂), α), true)
      have hpA : p ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hL₁, hL₂⟩, hd⟩, hα⟩,
          Finset.mem_univ _⟩, by simpa [p] using hne⟩
      have h := hξD (Sum.inl p) (Finset.inl_mem_disjSum.mpr hpA)
      simp only [l, Sum.elim_inl, p, dite_eq_left (show L₁ ∈ leviSpaces R a ∧ L₂ ∈ leviSpaces R a ∧
        dCoeff R a L₁ L₂ ≠ 0 from ⟨hL₁, hL₂, hd⟩)] at h
      rw [e₁]
      exact h
    · let p : ι := (((L₁, L₂), α), false)
      have hpA : p ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hL₁, hL₂⟩, hd⟩, hα⟩,
          Finset.mem_univ _⟩, by simpa [p] using hne⟩
      have h := hξD (Sum.inl p) (Finset.inl_mem_disjSum.mpr hpA)
      simp only [l, Sum.elim_inl, p, dite_eq_left (show L₁ ∈ leviSpaces R a ∧ L₂ ∈ leviSpaces R a ∧
        dCoeff R a L₁ L₂ ≠ 0 from ⟨hL₁, hL₂, hd⟩)] at h
      rw [e₂]
      exact h
  · ext α
    simp only [mem_posSet]
    refine and_congr_right fun hα => ?_
    by_cases hr : restrictedRoot a α = 0
    · have hz := (restrictedRoot_eq_zero_iff_forall_inner a α).mp hr
      rw [hz _ (a.smul_mem _ ξ.property.1), hz _ hh₀.1]
    · have h := Set.mem_iInter₂.mp hξU α (Finset.mem_filter.mpr ⟨hα, hr⟩)
      simp only [Set.mem_ofPred_eq] at h
      constructor
      · intro h1
        by_contra h2
        push Not at h2
        nlinarith
      · intro h1
        by_contra h2
        push Not at h2
        nlinarith
  · intro α hα hne
    have h := hξD (Sum.inr α) (Finset.inr_mem_disjSum.mpr (Finset.mem_filter.mpr ⟨hα, hne⟩))
    simpa [l] using h

section MainPair

omit [FiniteDimensional ℝ E] in
theorem centralSpace_mem_leviSpaces (hR : IsRootSet R) (ha : IsLeviSpace R a) :
    centralSpace R ∈ leviSpaces R a := by
  refine (mem_leviSpaces_iff hR ha _).mpr ⟨centralSpace_le_of_isLeviSpace ha, ⟨0, ?_⟩⟩
  have h : R.filter (fun α => ⟪α, (0 : E)⟫ = 0) = R :=
    Finset.filter_true_of_mem fun α _ => inner_zero_right α
  simp only [leviSpaceOf, centralSpace, h]

omit [FiniteDimensional ℝ E] in
theorem self_mem_leviSpaces (hR : IsRootSet R) (ha : IsLeviSpace R a) : a ∈ leviSpaces R a :=
  (mem_leviSpaces_iff hR ha a).mpr ⟨le_rfl, ha⟩

/-- `d_M^G(G, M) = 1`. -/
theorem dCoeff_centralSpace_self : dCoeff R a (centralSpace R) a = 1 := by
  unfold dCoeff measureFactor
  have h0 : Module.finrank ℝ ↥(a ⊓ aᗮ) = 0 := by
    rw [Submodule.inf_orthogonal_eq_bot, finrank_bot]
  rw [if_pos (by rw [h0, add_zero])]
  unfold gramVolume
  have hm : (Matrix.of fun i j => ⟪(Sum.elim
      (fun i => ((stdOrthonormalBasis ℝ ↥(a ⊓ (centralSpace R)ᗮ) i : ↥(a ⊓ (centralSpace R)ᗮ)) : E))
      (fun j => ((stdOrthonormalBasis ℝ ↥(a ⊓ aᗮ) j : ↥(a ⊓ aᗮ)) : E))) i,
      (Sum.elim
      (fun i => ((stdOrthonormalBasis ℝ ↥(a ⊓ (centralSpace R)ᗮ) i : ↥(a ⊓ (centralSpace R)ᗮ)) : E))
      (fun j => ((stdOrthonormalBasis ℝ ↥(a ⊓ aᗮ) j : ↥(a ⊓ aᗮ)) : E))) j⟫) = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · have h := orthonormal_iff_ite.mp
          (stdOrthonormalBasis ℝ ↥(a ⊓ (centralSpace R)ᗮ)).orthonormal i j
        simp only [Matrix.of_apply, Sum.elim_inl, Matrix.one_apply, Sum.inl.injEq]
        exact h
      · exact absurd j.isLt (by omega)
    · exact absurd i.isLt (by omega)
  rw [hm]
  convert Real.sqrt_one using 2
  convert Matrix.det_one
  infer_instance

omit [FiniteDimensional ℝ E] in
theorem posSet_zero : posSet R (0 : E) = ∅ := by
  ext α
  simp [posSet]

omit [FiniteDimensional ℝ E] in
/-- For every `ξ ∈ 𝔞_M^G`, the section of the pair `(𝔞_G, a)` is `(∅, posSet R (−2ξ))`. When
`−2ξ` is regular in `a` (as for a regular displacement), the second component is the chamber of
`a` containing `−2ξ`, equivalently `−ξ`; the first is the empty face, i.e. the group `G`. -/
theorem splittingSection_centralSpace_self (ξ : relativeSpace R a) :
    splittingSection R (ξ : E) (centralSpace R) a = (∅, posSet R (-(2 : ℝ) • (ξ : E))) := by
  have hmem : -(2 : ℝ) • (ξ : E) ∈ a ⊓ (centralSpace R)ᗮ :=
    Submodule.smul_mem _ _ ξ.property
  have h := splittingSection_eq_of_unique (R := R) (ξ := (ξ : E)) (L₁ := centralSpace R) (L₂ := a)
    (x₁ := 0) (x₂ := -(2 : ℝ) • (ξ : E)) (Submodule.zero_mem _) hmem
    (by rw [zero_sub, neg_smul, neg_neg]) (fun y₁ y₂ h₁ h₂ he => by
      have hy₁ : y₁ = 0 := by
        have h := Submodule.inf_orthogonal_eq_bot (centralSpace R)
        rw [h] at h₁
        exact (Submodule.mem_bot ℝ).mp h₁
      refine ⟨hy₁, ?_⟩
      rw [hy₁, zero_sub] at he
      rw [neg_smul, he, neg_neg])
  rw [h, posSet_zero]

omit [FiniteDimensional ℝ E] in
theorem splittingSection_fst_face {ξ : E} {L₁ L₂ : Submodule ℝ E} (hL₁ : L₁ ≤ a) :
    ∃ w : a, (splittingSection R ξ L₁ L₂).1 = posSet R (w : E) := by
  unfold splittingSection
  split_ifs with h
  · exact ⟨⟨h.choose, hL₁ h.choose_spec.choose_spec.1.1⟩, rfl⟩
  · exact ⟨0, by simp [posSet_zero]⟩

omit [FiniteDimensional ℝ E] in
theorem splittingSection_snd_face {ξ : E} {L₁ L₂ : Submodule ℝ E} (hL₂ : L₂ ≤ a) :
    ∃ w : a, (splittingSection R ξ L₁ L₂).2 = posSet R (w : E) := by
  unfold splittingSection
  split_ifs with h
  · exact ⟨⟨h.choose_spec.choose, hL₂ h.choose_spec.choose_spec.2.1.1⟩, rfl⟩
  · exact ⟨0, by simp [posSet_zero]⟩

/-- **Among pairs with nonzero coefficient, `(𝔞_G, 𝔞_M)` is the only one whose first section is
the empty face.** For a regular displacement `ξ` and a pair `(L₁, L₂)` with
`dCoeff R a L₁ L₂ ≠ 0`, an empty first section forces `L₁ = 𝔞_G` and `L₂ = a`. The hypothesis
`dCoeff ≠ 0` is needed: in positive relative rank the pair `(𝔞_G, 𝔞_G)` has zero coefficient, and
its first section is empty (for `ξ ≠ 0` by the fallback value `(∅, ∅)` of `splittingSection`). -/
theorem eq_centralSpace_self_of_section_empty (hR : IsRootSet R) (ha : IsLeviSpace R a)
    {L₁ L₂ : Submodule ℝ E} (hL₁ : L₁ ∈ leviSpaces R a) (hL₂ : L₂ ∈ leviSpaces R a)
    (hd : dCoeff R a L₁ L₂ ≠ 0) (ξ : relativeSpace R a) (hreg : RegularDisplacement R a (ξ : E))
    (h : (splittingSection R (ξ : E) L₁ L₂).1 = ∅) : L₁ = centralSpace R ∧ L₂ = a := by
  obtain ⟨h₁, h₂, he⟩ := splitPoint_spec hR ha hL₁ hL₂ hd ξ
  have hsec := splittingSection_eq_of_unique h₁ h₂ he
    (fun y₁ y₂ k₁ k₂ ke => splitPoint_eq hR ha hL₁ hL₂ hd ξ k₁ k₂ ke)
  rw [hsec] at h
  dsimp only at h
  have hreg₁ := (hreg L₁ hL₁ L₂ hL₂ hd _ _ h₁ h₂ he).1
  have hzero : ∀ α ∈ R, ⟪α, splitPoint₁ hR ha hL₁ hL₂ hd ξ⟫ = 0 := by
    intro α hα
    by_contra hne
    rcases lt_or_gt_of_ne hne with hn | hp
    · have hm : -α ∈ posSet R (splitPoint₁ hR ha hL₁ hL₂ hd ξ) :=
        mem_posSet.mpr ⟨hR.neg_mem hα, by rw [inner_neg_left]; linarith⟩
      rw [h] at hm
      exact Finset.notMem_empty _ hm
    · have hm : α ∈ posSet R (splitPoint₁ hR ha hL₁ hL₂ hd ξ) := mem_posSet.mpr ⟨hα, hp⟩
      rw [h] at hm
      exact Finset.notMem_empty _ hm
  have hres : ∀ α ∈ R, restrictedRoot L₁ α = 0 := fun α hα => by
    by_contra hne
    exact hreg₁.2 α hα hne (hzero α hα)
  have hLa₁ := (mem_leviSpaces_iff hR ha L₁).mp hL₁
  have hLa₂ := (mem_leviSpaces_iff hR ha L₂).mp hL₂
  have hL₁le : L₁ ≤ centralSpace R := fun z hz => mem_centralSpace_iff.mpr fun α hα => by
    have h' := inner_restrictedRoot_subtype L₁ α ⟨z, hz⟩
    rw [hres α hα, inner_zero_left] at h'
    exact h'.symm
  have hL₁eq : L₁ = centralSpace R :=
    le_antisymm hL₁le (centralSpace_le_of_isLeviSpace hLa₁.2)
  refine ⟨hL₁eq, ?_⟩
  have hU : a ⊓ L₁ᗮ ≤ a ⊓ (centralSpace R)ᗮ :=
    inf_le_inf_left _ (Submodule.orthogonal_le (centralSpace_le_of_isLeviSpace hLa₁.2))
  have hW : a ⊓ L₂ᗮ ≤ a ⊓ (centralSpace R)ᗮ :=
    inf_le_inf_left _ (Submodule.orthogonal_le (centralSpace_le_of_isLeviSpace hLa₂.2))
  obtain ⟨hdis, -⟩ := (measureFactor_ne_zero_iff hU hW).mp hd
  rw [hL₁eq] at hdis
  have hW0 : a ⊓ L₂ᗮ = ⊥ := eq_bot_iff.mpr fun x hx =>
    (Submodule.mem_bot ℝ).mpr ((Submodule.disjoint_def.mp hdis) x (hW hx) hx)
  have hsup := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hLa₂.1
  rw [inf_comm, hW0, sup_bot_eq] at hsup
  exact hsup

end MainPair

section OffWallIdentity

theorem eq_of_continuousAt_of_dense {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {f g : X → Y} {s : Set X} (hs : Dense s) (h : ∀ x ∈ s, f x = g x) {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) : f x = g x := by
  have : (𝓝[s] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hs x)
  have h1 : Tendsto f (𝓝[s] x) (𝓝 (f x)) := hf.tendsto.mono_left (nhdsWithin_le_nhds (s := s))
  have h2 : Tendsto f (𝓝[s] x) (𝓝 (g x)) :=
    (hg.tendsto.mono_left (nhdsWithin_le_nhds (s := s))).congr'
      (eventually_nhdsWithin_of_forall fun y hy => (h y hy).symm)
  exact tendsto_nhds_unique h1 h2

theorem continuousAt_cQM_face (hR : IsRootSet R) (ha : IsLeviSpace R a) (w : a)
    {c : Finset E → StrongDual ℝ a → ℂ} (hc : ∀ S, Continuous (c S)) {Λ : StrongDual ℝ a}
    (hΛ : OffWalls R a Λ) : ContinuousAt (cQM R a c (posSet R (w : E))) Λ := by
  unfold cQM
  refine tendsto_finsetSum _ fun S hS => ?_
  exact (hc _).continuousAt.mul ((theta_hasTemperateGrowth S).1.continuous.continuousAt.inv₀
    (theta_ne_zero_of_offWalls_face hR ha w hS hΛ))

omit [FiniteDimensional ℝ E] in
theorem dense_inner_ne_zero (E₀ : Finset a) (h0 : (0 : a) ∉ E₀) :
    Dense {y : a | ∀ e ∈ E₀, innerSL ℝ e y ≠ 0} := by
  refine dense_nonzero_forms E₀ (fun e : a => innerSL ℝ e) fun e he hz => ?_
  have hne : e ≠ 0 := fun h => h0 (h ▸ he)
  have h1 : innerSL ℝ e e = 0 := by rw [hz]; rfl
  rw [innerSL_apply_apply] at h1
  exact hne (inner_self_eq_zero.mp h1)

theorem continuousAt_cM_familyMul (hR : IsRootSet R) (ha : IsLeviSpace R a)
    {c d : Finset E → StrongDual ℝ a → ℂ} (hcc : ∀ S, Continuous (c S))
    (hdc : ∀ S, Continuous (d S)) {Λ : StrongDual ℝ a} (hΛ : OffWalls R a Λ) :
    ContinuousAt (cM R a (familyMul a c d)) Λ := by
  unfold cM familyMul
  refine tendsto_finsetSum _ fun S hS => ?_
  exact ((hcc S).continuousAt.mul (hdc S).continuousAt).mul
    ((theta_hasTemperateGrowth S).1.continuous.continuousAt.inv₀
      (theta_ne_zero_of_offWalls hR ha subset_rfl hS hΛ))

theorem continuousAt_splittingSum (hR : IsRootSet R) (ha : IsLeviSpace R a)
    {c d : Finset E → StrongDual ℝ a → ℂ} (hcc : ∀ S, Continuous (c S))
    (hdc : ∀ S, Continuous (d S)) (ξ : E) {Λ : StrongDual ℝ a} (hΛ : OffWalls R a Λ) :
    ContinuousAt (fun Λ' => ∑ L₁ ∈ leviSpaces R a, ∑ L₂ ∈ leviSpaces R a,
      (dCoeff R a L₁ L₂ : ℂ) * cQM R a c (splittingSection R ξ L₁ L₂).1 Λ' *
        cQM R a d (splittingSection R ξ L₁ L₂).2 Λ') Λ := by
  refine tendsto_finsetSum _ fun L₁ hL₁ => tendsto_finsetSum _ fun L₂ hL₂ => ?_
  obtain ⟨w₁, hw₁⟩ := splittingSection_fst_face (R := R) (ξ := ξ) (L₂ := L₂)
    ((mem_leviSpaces_iff hR ha L₁).mp hL₁).1
  obtain ⟨w₂, hw₂⟩ := splittingSection_snd_face (R := R) (ξ := ξ) (L₁ := L₁)
    ((mem_leviSpaces_iff hR ha L₂).mp hL₂).1
  rw [hw₁, hw₂]
  exact (continuousAt_const.mul (continuousAt_cQM_face hR ha w₁ hcc hΛ)).mul
    (continuousAt_cQM_face hR ha w₂ hdc hΛ)

/-- **The alternate splitting formula off the walls.** For `(G, M)`-families `c`, `d` with
continuous members, a regular displacement `ξ ∈ 𝔞_M^G` and `y ∈ a` with `Λ_y = ⟪y, ·⟫` off the
walls, `(cd)_M(Λ_y) = ∑_{L₁, L₂} d_M^G(L₁, L₂) c_M^{Q₁}(Λ_y) d_M^{Q₂}(Λ_y)` with
`(Q₁, Q₂) = splittingSection R ξ L₁ L₂`. -/
theorem alternateSplitting_of_offWalls (hR : IsRootSet R) (ha : IsLeviSpace R a)
    {c d : Finset E → StrongDual ℝ a → ℂ} (hc : IsFamily R a c) (hd : IsFamily R a d)
    (hcc : ∀ S, Continuous (c S)) (hdc : ∀ S, Continuous (d S)) (ξ : relativeSpace R a)
    (hreg : RegularDisplacement R a (ξ : E)) {y : a} (hΛ : OffWalls R a (innerSL ℝ y)) :
    cM R a (familyMul a c d) (innerSL ℝ y) =
      ∑ L₁ ∈ leviSpaces R a, ∑ L₂ ∈ leviSpaces R a, (dCoeff R a L₁ L₂ : ℂ) *
        cQM R a c (splittingSection R (ξ : E) L₁ L₂).1 (innerSL ℝ y) *
          cQM R a d (splittingSection R (ξ : E) L₁ L₂).2 (innerSL ℝ y) := by
  obtain ⟨E₀, h0, hE⟩ := alternateSplittingFormula R a hR ha c d hc hd (ξ : E) ξ.property hreg
  refine eq_of_continuousAt_of_dense (f := fun y' : a => cM R a (familyMul a c d) (innerSL ℝ y'))
    (g := fun y' : a => ∑ L₁ ∈ leviSpaces R a, ∑ L₂ ∈ leviSpaces R a, (dCoeff R a L₁ L₂ : ℂ) *
        cQM R a c (splittingSection R (ξ : E) L₁ L₂).1 (innerSL ℝ y') *
          cQM R a d (splittingSection R (ξ : E) L₁ L₂).2 (innerSL ℝ y'))
    (dense_inner_ne_zero E₀ h0) (fun y' hy' => hE _ fun e he => ?_) ?_ ?_
  · have h := hy' e he
    rw [innerSL_apply_apply] at h ⊢
    rwa [real_inner_comm]
  · exact (continuousAt_cM_familyMul hR ha hcc hdc hΛ).comp (innerSL ℝ).continuous.continuousAt
  · exact (continuousAt_splittingSum hR ha hcc hdc _ hΛ).comp
      (innerSL ℝ).continuous.continuousAt

end OffWallIdentity

end Langlands.GMFamily
