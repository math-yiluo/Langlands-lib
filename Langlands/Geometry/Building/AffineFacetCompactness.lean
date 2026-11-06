import Langlands.Geometry.Building.AffineChamberSeparation
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Compact convex closures of facets in essential affine root systems -/

noncomputable section

universe u

namespace Langlands.Geometry.Building.AffineRootSystem

open Set

private theorem weak_sign_region (c : ℝ) :
    {t : ℝ | SignType.sign t = 0 ∨ SignType.sign t = SignType.sign c} =
      if c < 0 then Iic 0 else if c = 0 then {0} else Ici 0 := by
  rcases lt_trichotomy c 0 with hc | hc | hc
  · rw [ite_eq_left hc]
    ext t
    simp only [mem_ofPred_eq, sign_neg hc, sign_eq_zero_iff,
      sign_eq_neg_one_iff, mem_Iic]
    exact ⟨fun h => h.elim le_of_eq le_of_lt, fun h => (lt_or_eq_of_le h).symm⟩
  · rw [ite_eq_right (by linarith), ite_eq_left hc]
    simp [hc, sign_eq_zero_iff]
  · rw [ite_eq_right (by linarith), ite_eq_right (ne_of_gt hc)]
    ext t
    simp only [mem_ofPred_eq, sign_pos hc, sign_eq_zero_iff,
      sign_eq_one_iff, mem_Ici]
    constructor
    · rintro (h | h)
      · exact le_of_eq h.symm
      · exact le_of_lt h
    · intro h
      exact (lt_or_eq_of_le h).elim Or.inr (fun h => Or.inl h.symm)

private theorem isClosed_weak_sign_region (c : ℝ) :
    IsClosed {t : ℝ | SignType.sign t = 0 ∨ SignType.sign t = SignType.sign c} := by
  rw [weak_sign_region]
  split_ifs <;> first | exact isClosed_Iic | exact isClosed_singleton | exact isClosed_Ici

private theorem convex_weak_sign_region (c : ℝ) :
    Convex ℝ {t : ℝ | SignType.sign t = 0 ∨ SignType.sign t = SignType.sign c} := by
  rw [weak_sign_region]
  split_ifs <;> first | exact convex_Iic 0 | exact convex_singleton 0 | exact convex_Ici 0

section Topology

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {Ψ : Set (V →ᵃ[ℝ] ℝ)}

omit [FiniteDimensional ℝ V] in
/-- Evaluation coordinates indexed by the actual derivative roots. -/
def derivativeCoordinates (Ψ : Set (V →ᵃ[ℝ] ℝ)) :
    V →ₗ[ℝ] (derivativeRoots Ψ → ℝ) where
  toFun y a := (a : Module.Dual ℝ V) y
  map_add' x y := funext fun a => map_add a.val x y
  map_smul' c y := funext fun a => map_smul a.val c y

/-- Weak sign conditions make every facet closure closed. -/
theorem isClosed_facetClosure (Ψ : Set (V →ᵃ[ℝ] ℝ)) (p : V) :
    IsClosed (facetClosure Ψ p) := by
  have hs : facetClosure Ψ p =
      ⋂ ψ ∈ Ψ, ψ ⁻¹' {t : ℝ |
        SignType.sign t = 0 ∨ SignType.sign t = SignType.sign (ψ p)} := by
    ext y
    simp [facetClosure]
  rw [hs]
  exact isClosed_iInter fun ψ => isClosed_iInter fun _ =>
    (isClosed_weak_sign_region (ψ p)).preimage ψ.continuous_of_finiteDimensional

omit [FiniteDimensional ℝ V] in
/-- Facet closures are convex intersections of closed affine half-spaces. -/
theorem convex_facetClosure (Ψ : Set (V →ᵃ[ℝ] ℝ)) (p : V) :
    Convex ℝ (facetClosure Ψ p) := by
  have hs : facetClosure Ψ p =
      ⋂ ψ ∈ Ψ, ψ ⁻¹' {t : ℝ |
        SignType.sign t = 0 ∨ SignType.sign t = SignType.sign (ψ p)} := by
    ext y
    simp [facetClosure]
  rw [hs]
  exact convex_iInter fun ψ => convex_iInter fun _ =>
    (convex_weak_sign_region (ψ p)).affine_preimage ψ

omit [FiniteDimensional ℝ V] in
/-- Each derivative has parallel affine roots on both sides of every point. -/
theorem IsAffineRootSystemWithRankZero.exists_parallel_roots_opposite_sign
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p : V)
    {ψ : V →ᵃ[ℝ] ℝ} (hψ : ψ ∈ Ψ) :
    ∃ η ∈ Ψ, ∃ χ ∈ Ψ, η.linear = ψ.linear ∧ χ.linear = ψ.linear ∧
      η p < 0 ∧ 0 < χ p := by
  obtain ⟨η, ⟨hη, hlin⟩, hout⟩ := (hΨ.infinite_fiber ψ hψ).exists_notMem_finite
    (hΨ.finite_bounded_at p (fun _ => 2 * |ψ p| + 1))
  have hlarge : 2 * |ψ p| + 1 < |η p| := by
    by_contra h
    exact hout ⟨hη, le_of_not_gt h⟩
  obtain ⟨v, hv⟩ := hΨ.exists_isCoroot ψ hψ
  let χ : V →ᵃ[ℝ] ℝ := -(η - (2 : ℝ) • ψ)
  have hχ : χ ∈ Ψ := by
    apply hΨ.neg_mem
    have h := hv.2 η hη
    rwa [hlin, hv.1] at h
  have hχlin : χ.linear = ψ.linear := by
    change -(η.linear - (2 : ℝ) • ψ.linear) = ψ.linear
    rw [hlin, two_smul]
    abel
  have hχp : χ p = 2 * ψ p - η p := by
    change -(η p - (2 : ℝ) • ψ p) = _
    simp only [smul_eq_mul]
    ring
  rcases lt_or_gt_of_ne (show η p ≠ 0 by
    intro he
    rw [he, abs_zero] at hlarge
    linarith [abs_nonneg (ψ p)]) with hn | hp
  · refine ⟨η, hη, χ, hχ, hlin, hχlin, hn, ?_⟩
    rw [hχp]
    rw [abs_of_neg hn] at hlarge
    linarith [neg_abs_le (ψ p)]
  · refine ⟨χ, hχ, η, hη, hχlin, hlin, ?_, hp⟩
    rw [hχp]
    rw [abs_of_pos hp] at hlarge
    linarith [le_abs_self (ψ p)]

omit [FiniteDimensional ℝ V] in
/-- Every derivative coordinate is bounded throughout a fixed facet closure. -/
theorem IsAffineRootSystemWithRankZero.exists_bound_derivative_facetClosure
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p : V)
    (a : derivativeRoots Ψ) :
    ∃ M : ℝ, ∀ y ∈ facetClosure Ψ p, |(a : Module.Dual ℝ V) y| ≤ M := by
  obtain ⟨ψ, hψ, hψa⟩ := a.property
  change ψ.linear = (a : Module.Dual ℝ V) at hψa
  obtain ⟨η, hη, χ, hχ, hηlin, hχlin, hηp, hχp⟩ :=
    hΨ.exists_parallel_roots_opposite_sign p hψ
  refine ⟨|η 0| + |χ 0|, fun y hy => ?_⟩
  have hηy : η y ≤ 0 := by
    rcases hy η hη with h | h
    · exact le_of_eq (sign_eq_zero_iff.mp h)
    · rw [sign_neg hηp, sign_eq_neg_one_iff] at h
      exact le_of_lt h
  have hχy : 0 ≤ χ y := by
    rcases hy χ hχ with h | h
    · exact le_of_eq (sign_eq_zero_iff.mp h).symm
    · rw [sign_pos hχp, sign_eq_one_iff] at h
      exact le_of_lt h
  have hηeq : (a : Module.Dual ℝ V) y = η y - η 0 := by
    rw [← hψa, ← hηlin]
    simpa using η.linearMap_vsub y 0
  have hχeq : (a : Module.Dual ℝ V) y = χ y - χ 0 := by
    rw [← hψa, ← hχlin]
    simpa using χ.linearMap_vsub y 0
  exact abs_le.mpr ⟨by linarith [le_abs_self (χ 0), abs_nonneg (η 0)],
    by linarith [neg_abs_le (η 0), abs_nonneg (χ 0)]⟩

/-- Full corrected affine root axioms imply compactness of every facet closure.
Derivative spanning includes the rank-zero case. -/
theorem IsAffineRootSystemWithRankZero.isCompact_facetClosure
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p : V) :
    IsCompact (facetClosure Ψ p) := by
  let e := derivativeCoordinates Ψ
  have he : LinearMap.ker e = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    apply sub_eq_zero.mp
    apply (Module.forall_dual_apply_eq_zero_iff ℝ (x - y)).mp
    intro φ
    have hvan : ∀ a ∈ Submodule.span ℝ (derivativeRoots Ψ), a (x - y) = 0 := by
      intro a ha
      induction ha using Submodule.span_induction with
      | mem a ha =>
        have h := congrFun hxy ⟨a, ha⟩
        simpa only [e, derivativeCoordinates, LinearMap.coe_mk, AddHom.coe_mk,
          map_sub, sub_eq_zero] using h
      | zero => simp
      | add a b _ _ ha hb => simp [ha, hb]
      | smul c a _ ha => simp [ha]
    have hφ := hvan φ (hΨ.span_derivativeRoots_eq_top ▸ Submodule.mem_top)
    exact hφ
  choose M hM using hΨ.exists_bound_derivative_facetClosure p
  have hk : IsCompact {z : derivativeRoots Ψ → ℝ | ∀ a, z a ∈ Icc (-M a) (M a)} :=
    isCompact_pi_infinite fun _ => isCompact_Icc
  have hpre := (LinearMap.isClosedEmbedding_of_injective he).isCompact_preimage hk
  apply hpre.of_isClosed_subset (isClosed_facetClosure Ψ p)
  intro y hy a
  exact abs_le.mp (hM a y hy)

end Topology

end Langlands.Geometry.Building.AffineRootSystem
