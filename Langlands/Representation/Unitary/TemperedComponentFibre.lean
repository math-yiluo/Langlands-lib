import Langlands.Representation.Unitary.TemperedComponentGlobalKernel

/-! # The smoothed maps of a cone element for the global relations

Let `F` be a bounded cone element for the relations `globalRel` (the word relations and the
support relation for `W₀ = closure j(H₀)`). On the Hilbert space `VL hF` of the left ideal, the
bounded maps `B_k = (w ↦ vec 1 k w)^* ∘ ι : VL hF → W` satisfy
`B_{k(n)} σ(a) σ(ψ_k) = π_W(ψ_{k(n)}) π_W(a) B_k`, take values in `W₀`, and some `B_k` is nonzero
when `F ≠ 0` and `ψ_{k(n)}` is an approximate identity.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Analysis.TemperedComponent

open Langlands.Archimedean Langlands.Analysis.KernelCone

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {π : G →* (H →L[ℂ] H)} {hπ : IsContinuousRepresentation π}
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
variable {πW : G →* (W →L[ℂ] W)} {hπW : IsContinuousRepresentation πW}
variable {j : H →L[ℂ] W} {H₀ : Submodule ℂ H} [H₀.HasOrthogonalProjection]
variable {κ : Type*} {ψ : κ → G → ℂ} {hψ : ∀ k, IsTestFunction (ψ k)}
variable {hπu : ∀ g, π g ∈ unitary (H →L[ℂ] H)} {nIdx : ℕ → κ}
variable {F : Coord (algebra μ π hπ) κ W → ℂ}
variable (hF : IsConeElement (globalRel μ π hπ πW hπW j H₀ ψ hψ hπu nIdx) F)
variable (hB : IsBoundedForm F)

/-- The bounded maps `B_k : VL hF → W`. -/
def opB (k : κ) : VL hF →L[ℂ] W :=
  (ContinuousLinearMap.adjoint (vecL hF hB 1 k)).comp (iotaL hF).toContinuousLinearMap

theorem inner_opB_vec (k k' : κ) (y : leftIdeal μ π hπ) (w w' : W) :
    ⟪w, opB hF hB k (vecL' hF y k' w')⟫_ℂ =
      F (k, k', ⟨y, leftIdeal_le_algebra π hπ y.2⟩, w, w') := by
  rw [opB, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  change ⟪vec hF 1 k w, iotaL hF (vecL' hF y k' w')⟫_ℂ = _
  rw [iotaL_vec, inner_vec, star_one, one_mul]

include hπu in
theorem wordOp_sigma_vec (a : Word G) (y : leftIdeal μ π hπ) (k : κ) (w : W) :
    wordOp μ (sigma hF hπu) (isContinuousRepresentation_sigma hF hπu) a (vecL' hF y k w) =
      vecL' hF ⟨wordOp μ π hπ a * y, wordOp_mul_mem_leftIdeal π hπ hπu a y.2⟩ k w := by
  induction a with
  | nil =>
    rw [wordOp_nil, one_apply_eq_self]
    congr 1
  | cons l a ih =>
    rw [wordOp_cons, mul_apply_eq_comp, ih]
    rcases l with g | φ
    · change sigma hF hπu g _ = _
      rw [sigma_vec]
      congr 1
    · change testOp μ (sigma hF hπu) (isContinuousRepresentation_sigma hF hπu) φ.1 φ.2 _ = _
      rw [testOp_sigma_vec]
      congr 1

include hπu in
/-- The relation `B_{k(n)} σ(a) σ(ψ_k) = π_W(ψ_{k(n)}) π_W(a) B_k`. -/
theorem opB_relation (n : ℕ) (a : Word G) (k : κ) (v : VL hF) :
    opB hF hB (nIdx n) (wordOp μ (sigma hF hπu) (isContinuousRepresentation_sigma hF hπu) a
      (testOp μ (sigma hF hπu) (isContinuousRepresentation_sigma hF hπu) (ψ k) (hψ k) v)) =
    testOp μ πW hπW (ψ (nIdx n)) (hψ (nIdx n)) (wordOp μ πW hπW a (opB hF hB k v)) := by
  have h : (opB hF hB (nIdx n)).comp ((wordOp μ (sigma hF hπu)
      (isContinuousRepresentation_sigma hF hπu) a).comp
        (testOp μ (sigma hF hπu) (isContinuousRepresentation_sigma hF hπu) (ψ k) (hψ k))) =
      (testOp μ πW hπW (ψ (nIdx n)) (hψ (nIdx n)) * wordOp μ πW hπW a).comp (opB hF hB k) := by
    refine clm_extL hF fun y k' w' => ext_inner_left ℂ fun w => ?_
    simp only [ContinuousLinearMap.comp_apply]
    rw [testOp_sigma_vec, wordOp_sigma_vec, inner_opB_vec, ← ContinuousLinearMap.adjoint_inner_left,
      inner_opB_vec]
    have hr : ((nIdx n, ⟨wordOp μ π hπ a * testOp μ π hπ (ψ k) (hψ k),
        leftIdeal_le_algebra π hπ (wordOp_mul_mem_leftIdeal π hπ hπu a
          (testOp_mem_leftIdeal π hπ (ψ k) (hψ k)))⟩, k,
        ContinuousLinearMap.adjoint (testOp μ πW hπW (ψ (nIdx n)) (hψ (nIdx n)) *
          wordOp μ πW hπW a)) : κ × algebra μ π hπ × κ × (W →L[ℂ] W)) ∈
          globalRel μ π hπ πW hπW j H₀ ψ hψ hπu nIdx :=
      Or.inl ⟨n, a, k, rfl⟩
    have h2 := hF.rel _ hr k' ⟨y, leftIdeal_le_algebra π hπ y.2⟩ w w'
    refine Eq.trans ?_ h2
    congr 3
  have h3 := congrArg (fun A => A v) h
  simpa only [ContinuousLinearMap.comp_apply, mul_apply_eq_comp] using h3

/-- The maps `B_k` take values in `W₀`. -/
theorem opB_mem_wSub (k : κ) (v : VL hF) : opB hF hB k v ∈ wSub j H₀ := by
  set P := (wSub j H₀).starProjection
  have hPs : ∀ u z, ⟪P u, z⟫_ℂ = ⟪u, P z⟫_ℂ := fun u z =>
    (isSelfAdjoint_starProjection (wSub j H₀)).isSymmetric u z
  have hrel : ∀ w : W, (innerSL ℂ w).comp (opB hF hB k) =
      (innerSL ℂ (P w)).comp (opB hF hB k) := fun w => by
    refine clm_extL hF fun y k' w' => ?_
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply]
    rw [inner_opB_vec, inner_opB_vec]
    have hr : ((k, 1, k, P) : κ × algebra μ π hπ × κ × (W →L[ℂ] W)) ∈
        globalRel μ π hπ πW hπW j H₀ ψ hψ hπu nIdx := Or.inr ⟨k, rfl⟩
    have h2 := hF.rel _ hr k' ⟨y, leftIdeal_le_algebra π hπ y.2⟩ w w'
    simpa only [one_mul] using h2
  have heq : opB hF hB k v = P (opB hF hB k v) := by
    refine ext_inner_left ℂ fun w => ?_
    have h := congrArg (fun A => A v) (hrel w)
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] at h
    rw [h, hPs]
  rw [heq]
  exact (wSub j H₀).starProjection_apply_mem _

include hπu in
/-- Some `B_k` is nonzero when `F ≠ 0` and the `ψ_{k(n)}` form an approximate identity. -/
theorem exists_opB_ne_zero (hχ : IsApproxIdentity μ fun n => ψ (nIdx n)) (hne : F ≠ 0) :
    ∃ k v, opB hF hB k v ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have hL : ∀ k k' (y : leftIdeal μ π hπ) w w',
      F (k, k', ⟨y, leftIdeal_le_algebra π hπ y.2⟩, w, w') = 0 := fun k k' y w w' => by
    rw [← inner_opB_vec hF hB, hcon, inner_zero_right]
  have hdiag : ∀ k k' (u w' : W), F (k, k', 1, u, w') = 0 := fun k k' u w' => by
    set z := ContinuousLinearMap.adjoint (vecL hF hB 1 k) (vec hF 1 k' w')
    have hFz : ∀ u', F (k, k', 1, u', w') = ⟪u', z⟫_ℂ := fun u' => by
      rw [ContinuousLinearMap.adjoint_inner_right, vecL_apply, inner_vec, star_one, one_mul]
    have hz : ∀ n, testOp μ πW hπW (ψ (nIdx n)) (hψ (nIdx n)) z = 0 := fun n => by
      refine ext_inner_left ℂ fun u' => ?_
      have hr : ((nIdx n, ⟨wordOp μ π hπ [] * testOp μ π hπ (ψ k) (hψ k),
          leftIdeal_le_algebra π hπ (wordOp_mul_mem_leftIdeal π hπ hπu []
            (testOp_mem_leftIdeal π hπ (ψ k) (hψ k)))⟩, k,
          ContinuousLinearMap.adjoint (testOp μ πW hπW (ψ (nIdx n)) (hψ (nIdx n)) *
            wordOp μ πW hπW [])) : κ × algebra μ π hπ × κ × (W →L[ℂ] W)) ∈
            globalRel μ π hπ πW hπW j H₀ ψ hψ hπu nIdx :=
        Or.inl ⟨n, [], k, rfl⟩
      have h2 := hF.rel _ hr k' 1 u' w'
      rw [mul_one] at h2
      have h3 := hL (nIdx n) k' ⟨wordOp μ π hπ [] * testOp μ π hπ (ψ k) (hψ k),
        wordOp_mul_mem_leftIdeal π hπ hπu [] (testOp_mem_leftIdeal π hπ (ψ k) (hψ k))⟩ u' w'
      rw [h3, hFz, ContinuousLinearMap.adjoint_inner_left] at h2
      rw [inner_zero_right, h2]
      simp only [wordOp_nil, mul_one]
    have hlim := hχ.tendsto πW hπW z
    simp only [hz] at hlim
    rw [hFz, (tendsto_nhds_unique tendsto_const_nhds hlim).symm, inner_zero_right]
  apply hne
  funext p
  obtain ⟨k, k', x, w, w'⟩ := p
  have hv : vec hF 1 k w = 0 := by
    rw [← norm_eq_zero, ← sq_eq_zero_iff, norm_vec_sq, star_one, one_mul,
      hdiag, Complex.zero_re]
  have h := inner_vec hF 1 k w x k' w'
  rw [hv, inner_zero_left, star_one, one_mul] at h
  exact h.symm

end Langlands.Analysis.TemperedComponent
