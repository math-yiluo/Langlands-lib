import Langlands.Representation.Unitary.TemperedComponentGNS
import Langlands.Analysis.HilbertSchmidtIdealProof
import Langlands.Analysis.HilbertSchmidtBasisProof

/-! # The global kernel of the smoothed maps `j ∘ π(ψ_k)`

Let `π` be a unitary representation on `H` with a closed invariant subspace `H₀` (projection
`P₀`), `π_W` a continuous representation on `W` and `j : H → W` an equivariant bounded map. For a
family `ψ_k` of test functions put `T_k = j ∘ π(ψ_k)` and `A_k = P₀ ∘ T_k^*`. The *global kernel*
`F⁰ (k, k', x, w, w') = ⟪A_k w, x (A_{k'} w')⟫` over the algebra `algebra μ π hπ` is a bounded
cone element for the relations

* `F (k₀, k', π(a) π(ψ_k) x, w, w') = F (k, k', x, (π_W(ψ_{k₀}) π_W(a))^* w, w')` for words `a`, and
* `F (k, k', x, w, w') = F (k, k', x, P_{W₀} w, w')` with `W₀` the closure of `j(H₀)`,

and its diagonal values are `Re F⁰ (k, k, 1, w, w) = ‖A_k w‖²` (`re_globalKernel_diag`). Hence,
for positive weights `c_k`, its weighted trace is `∑_k c_k ∑_b ‖A_k e_b‖²`, finite when every `T_k`
is Hilbert–Schmidt and the weights are suitably small.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

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

/-- The closure of a submodule has an orthogonal projection. -/
instance hasOrthogonalProjection_topologicalClosure (S : Submodule ℂ W) :
    S.topologicalClosure.HasOrthogonalProjection := by
  have : CompleteSpace S.topologicalClosure := S.isClosed_topologicalClosure.completeSpace_coe
  infer_instance

/-- The projection onto a closed invariant subspace commutes with a unitary representation. -/
theorem starProjection_commute_of_unitary {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (ρ : G →* (E →L[ℂ] E))
    (hρu : ∀ g, ρ g ∈ unitary (E →L[ℂ] E)) (M : Submodule ℂ E) [M.HasOrthogonalProjection]
    (hMinv : ∀ (g : G), ∀ v ∈ M, ρ g v ∈ M) (g : G) (v : E) :
    M.starProjection (ρ g v) = ρ g (M.starProjection v) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (hMinv g _ (M.starProjection_apply_mem v)) fun w hw => ?_
  have hstar : star (ρ g) = ρ g⁻¹ := by
    calc star (ρ g) = star (ρ g) * (ρ g * ρ g⁻¹) := by
          rw [← map_mul, mul_inv_cancel, map_one, mul_one]
      _ = ρ g⁻¹ := by rw [← mul_assoc, (Unitary.mem_iff.mp (hρu g)).1, one_mul]
  rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    hstar]
  have h := Submodule.inner_right_of_mem_orthogonal (hMinv g⁻¹ w hw)
    (M.sub_starProjection_mem_orthogonal v)
  rwa [inner_eq_zero_symm] at h

section Global

variable (μ) (π) (hπ)
variable (πW : G →* (W →L[ℂ] W)) (hπW : IsContinuousRepresentation πW)
variable (j : H →L[ℂ] W) (hj : ∀ g x, j (π g x) = πW g (j x))
variable (H₀ : Submodule ℂ H) [H₀.HasOrthogonalProjection]
variable {κ : Type*} (ψ : κ → G → ℂ) (hψ : ∀ k, IsTestFunction (ψ k))

/-- The closure `W₀` of `j(H₀)`. -/
abbrev wSub : Submodule ℂ W := (H₀.map (j : H →ₗ[ℂ] W)).topologicalClosure

theorem coe_wSub : (wSub j H₀ : Set W) = closure (j '' (H₀ : Set H)) := by
  rw [wSub, Submodule.topologicalClosure_coe, Submodule.map_coe]
  rfl

/-- The operators `T_k = j ∘ π(ψ_k)`. -/
def opT (k : κ) : H →L[ℂ] W := j.comp (testOp μ π hπ (ψ k) (hψ k))

/-- The operators `A_k = P₀ ∘ T_k^*`. -/
def opA (k : κ) : W →L[ℂ] H := H₀.starProjection.comp (ContinuousLinearMap.adjoint (opT μ π hπ j ψ hψ k))

/-- The global kernel `F⁰ (k, k', x, w, w') = ⟪A_k w, x (A_{k'} w')⟫`. -/
def globalKernel : Coord (algebra μ π hπ) κ W → ℂ :=
  fun p => ⟪opA μ π hπ j H₀ ψ hψ p.1 p.2.2.2.1, (p.2.2.1 : H →L[ℂ] H) (opA μ π hπ j H₀ ψ hψ p.2.1 p.2.2.2.2)⟫_ℂ

variable (hπu : ∀ g, π g ∈ unitary (H →L[ℂ] H))
include hπu

/-- The relations: word relations and the support relation for `W₀`. -/
def globalRel (nIdx : ℕ → κ) : Set (κ × algebra μ π hπ × κ × (W →L[ℂ] W)) :=
  {r | (∃ (n : ℕ) (a : Word G) (k : κ), r = (nIdx n,
      ⟨wordOp μ π hπ a * testOp μ π hπ (ψ k) (hψ k),
        leftIdeal_le_algebra π hπ (wordOp_mul_mem_leftIdeal π hπ hπu a
          (testOp_mem_leftIdeal π hπ (ψ k) (hψ k)))⟩, k,
      ContinuousLinearMap.adjoint (testOp μ πW hπW (ψ (nIdx n)) (hψ (nIdx n)) * wordOp μ πW hπW a))) ∨
    ∃ k : κ, r = (k, 1, k, (wSub j H₀).starProjection)}

omit hπu in
theorem globalKernel_apply (k k' : κ) (x : algebra μ π hπ) (w w' : W) :
    globalKernel μ π hπ j H₀ ψ hψ (k, k', x, w, w') =
      ⟪opA μ π hπ j H₀ ψ hψ k w, (x : H →L[ℂ] H) (opA μ π hπ j H₀ ψ hψ k' w')⟫_ℂ := rfl

omit hπu in
theorem adjoint_starProjection_eq : ContinuousLinearMap.adjoint H₀.starProjection =
    H₀.starProjection := by
  rw [← ContinuousLinearMap.star_eq_adjoint]
  exact (isSelfAdjoint_starProjection H₀).star_eq

omit hπu in
theorem adjoint_opA (k : κ) : ContinuousLinearMap.adjoint (opA μ π hπ j H₀ ψ hψ k) =
    (opT μ π hπ j ψ hψ k).comp H₀.starProjection := by
  rw [opA, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    adjoint_starProjection_eq]

omit hπu in
/-- The inner products defining the global kernel as Gram products. -/
theorem globalKernel_star_mul (k k' : κ) (x y : algebra μ π hπ) (w w' : W) :
    globalKernel μ π hπ j H₀ ψ hψ (k, k', star x * y, w, w') =
      ⟪(x : H →L[ℂ] H) (opA μ π hπ j H₀ ψ hψ k w),
        (y : H →L[ℂ] H) (opA μ π hπ j H₀ ψ hψ k' w')⟫_ℂ := by
  rw [globalKernel_apply]
  change ⟪_, (star (x : H →L[ℂ] H) * y) _⟫_ℂ = _
  rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

variable (hH₀c : IsClosed (H₀ : Set H)) (hH₀ : ∀ g, ∀ x ∈ H₀, π g x ∈ H₀)
include hj hH₀

omit hj in
theorem starProjection_wordOp (a : Word G) (y : H) :
    H₀.starProjection (wordOp μ π hπ a y) = wordOp μ π hπ a (H₀.starProjection y) :=
  congrArg (fun A => A y) (intertwiner_comp_wordOp π hπ π hπ H₀.starProjection
    (starProjection_commute_of_unitary π hπu H₀ hH₀) a)

omit hj in
theorem starProjection_testOp (φ : G → ℂ) (hφ : IsTestFunction φ) (y : H) :
    H₀.starProjection (testOp μ π hπ φ hφ y) = testOp μ π hπ φ hφ (H₀.starProjection y) :=
  congrArg (fun A => A y) (intertwiner_comp_testOp π hπ π hπ H₀.starProjection
    (starProjection_commute_of_unitary π hπu H₀ hH₀) φ hφ)

omit hH₀ hπu in
theorem j_wordOp (a : Word G) (y : H) :
    j (wordOp μ π hπ a y) = wordOp μ πW hπW a (j y) :=
  congrArg (fun A => A y) (intertwiner_comp_wordOp π hπ πW hπW j hj a)

omit hH₀ hπu in
theorem j_testOp (φ : G → ℂ) (hφ : IsTestFunction φ) (y : H) :
    j (testOp μ π hπ φ hφ y) = testOp μ πW hπW φ hφ (j y) :=
  congrArg (fun A => A y) (intertwiner_comp_testOp π hπ πW hπW j hj φ hφ)

/-- The word relation for the operators `A_k`. -/
theorem adjoint_word_opA (k₀ k : κ) (a : Word G) (w : W) :
    ContinuousLinearMap.adjoint (wordOp μ π hπ a * testOp μ π hπ (ψ k) (hψ k))
      (opA μ π hπ j H₀ ψ hψ k₀ w) =
    opA μ π hπ j H₀ ψ hψ k (ContinuousLinearMap.adjoint
      (testOp μ πW hπW (ψ k₀) (hψ k₀) * wordOp μ πW hπW a) w) := by
  have h : (ContinuousLinearMap.adjoint (opA μ π hπ j H₀ ψ hψ k₀)).comp
      (wordOp μ π hπ a * testOp μ π hπ (ψ k) (hψ k)) =
      (testOp μ πW hπW (ψ k₀) (hψ k₀) * wordOp μ πW hπW a).comp
        (ContinuousLinearMap.adjoint (opA μ π hπ j H₀ ψ hψ k)) := by
    ext y
    simp only [adjoint_opA, ContinuousLinearMap.comp_apply, mul_apply_eq_comp, opT]
    rw [starProjection_wordOp μ π hπ H₀ hπu hH₀, starProjection_testOp μ π hπ H₀ hπu hH₀,
      j_testOp μ π hπ πW hπW j hj, j_wordOp μ π hπ πW hπW j hj]
  have h2 := congrArg ContinuousLinearMap.adjoint h
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.adjoint_adjoint] at h2
  exact congrArg (fun A => A w) h2

include hH₀c in
omit hj hπu in
/-- `A_k` vanishes on the orthogonal complement of `W₀`. -/
theorem opA_starProjection_wSub (k : κ) (w : W) :
    opA μ π hπ j H₀ ψ hψ k ((wSub j H₀).starProjection w) = opA μ π hπ j H₀ ψ hψ k w := by
  rw [← sub_eq_zero, ← map_sub, opA, ContinuousLinearMap.comp_apply,
    Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
  intro u hu
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hz : (wSub j H₀).starProjection w - w ∈ (wSub j H₀)ᗮ := by
    rw [← neg_mem_iff, neg_sub]
    exact (wSub j H₀).sub_starProjection_mem_orthogonal w
  have hmem : opT μ π hπ j ψ hψ k u ∈ wSub j H₀ := by
    refine Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem ?_)
    exact testOp_mem π hπ (ψ k) (hψ k) H₀ hH₀c hH₀ hu
  exact (Submodule.mem_orthogonal _ _).mp hz _ hmem

include hH₀c in
theorem isConeElement_globalKernel (nIdx : ℕ → κ) :
    IsConeElement (globalRel μ π hπ πW hπW j H₀ ψ hψ hπu nIdx) (globalKernel μ π hπ j H₀ ψ hψ) where
  add_mid k k' x y w w' := by
    simp only [globalKernel_apply]
    change ⟪_, ((x : H →L[ℂ] H) + y) _⟫_ℂ = _
    rw [add_apply, inner_add_right]
  smul_mid k k' r x w w' := by
    simp only [globalKernel_apply]
    change ⟪_, (r • (x : H →L[ℂ] H)) _⟫_ℂ = _
    rw [smul_apply, inner_smul_right]
  add_left k k' x w₁ w₂ w' := by simp only [globalKernel_apply, map_add, inner_add_left]
  smul_left k k' x r w w' := by simp only [globalKernel_apply, map_smul, inner_smul_left]
  add_right k k' x w w₁ w₂ := by simp only [globalKernel_apply, map_add, inner_add_right]
  smul_right k k' x w r w' := by simp only [globalKernel_apply, map_smul, inner_smul_right]
  herm k k' x w w' := by
    simp only [globalKernel_apply]
    rw [inner_conj_symm]
    change ⟪(star (x : H →L[ℂ] H)) _, _⟫_ℂ = _
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  pos f := by
    have e : kernelOf (globalKernel μ π hπ j H₀ ψ hψ) = fun i j' =>
        ⟪(1 : H →L[ℂ] H) ((i.1 : H →L[ℂ] H) (opA μ π hπ j H₀ ψ hψ i.2.1 i.2.2)),
          (j'.1 : H →L[ℂ] H) (opA μ π hπ j H₀ ψ hψ j'.2.1 j'.2.2)⟫_ℂ := by
      funext i j'
      exact globalKernel_star_mul μ π hπ j H₀ ψ hψ _ _ _ _ _ _
    rw [e, kernelForm_inner, one_apply_eq_self]
    exact inner_self_nonneg (𝕜 := ℂ)
  mul_le a f := by
    have e : (fun i j' => kernelOf (globalKernel μ π hπ j H₀ ψ hψ) (lmul a i) (lmul a j')) =
        fun i j' => ⟪(1 : H →L[ℂ] H) ((a : H →L[ℂ] H) ((i.1 : H →L[ℂ] H)
          (opA μ π hπ j H₀ ψ hψ i.2.1 i.2.2))),
          (a : H →L[ℂ] H) ((j'.1 : H →L[ℂ] H) (opA μ π hπ j H₀ ψ hψ j'.2.1 j'.2.2))⟫_ℂ := by
      funext i j'
      exact globalKernel_star_mul μ π hπ j H₀ ψ hψ _ _ _ _ _ _
    have e' : kernelOf (globalKernel μ π hπ j H₀ ψ hψ) = fun i j' =>
        ⟪(1 : H →L[ℂ] H) ((i.1 : H →L[ℂ] H) (opA μ π hπ j H₀ ψ hψ i.2.1 i.2.2)),
          (j'.1 : H →L[ℂ] H) (opA μ π hπ j H₀ ψ hψ j'.2.1 j'.2.2)⟫_ℂ := by
      funext i j'
      exact globalKernel_star_mul μ π hπ j H₀ ψ hψ _ _ _ _ _ _
    rw [e, e', kernelForm_inner, kernelForm_inner, one_apply_eq_self, one_apply_eq_self]
    set ξ := f.sum fun i b => b • (i.1 : H →L[ℂ] H) (opA μ π hπ j H₀ ψ hψ i.2.1 i.2.2)
    have hξ : (f.sum fun i b => b • (a : H →L[ℂ] H) ((i.1 : H →L[ℂ] H)
        (opA μ π hπ j H₀ ψ hψ i.2.1 i.2.2))) = (a : H →L[ℂ] H) ξ := by
      rw [map_finsuppSum]
      simp only [map_smul]
    have h1 : (⟪(a : H →L[ℂ] H) ξ, (a : H →L[ℂ] H) ξ⟫_ℂ).re = ‖(a : H →L[ℂ] H) ξ‖ ^ 2 :=
      (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
    have h2 : (⟪ξ, ξ⟫_ℂ).re = ‖ξ‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
    rw [hξ, h1, h2]
    calc ‖(a : H →L[ℂ] H) ξ‖ ^ 2 ≤ (‖(a : H →L[ℂ] H)‖ * ‖ξ‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) ((a : H →L[ℂ] H).le_opNorm ξ) 2
      _ = ‖a‖ ^ 2 * ‖ξ‖ ^ 2 := by rw [mul_pow]; rfl
  rel r hr k' x w w' := by
    rcases hr with ⟨n, a, k, rfl⟩ | ⟨k, rfl⟩
    · simp only [globalKernel_apply]
      change ⟪_, ((wordOp μ π hπ a * testOp μ π hπ (ψ k) (hψ k)) * (x : H →L[ℂ] H)) _⟫_ℂ = _
      rw [mul_apply_eq_comp, ← ContinuousLinearMap.adjoint_inner_left,
        adjoint_word_opA μ π hπ πW hπW j hj H₀ ψ hψ hπu hH₀]
    · simp only [globalKernel_apply, one_mul]
      rw [opA_starProjection_wSub μ π hπ j H₀ ψ hψ hH₀c hH₀ k w]

include hH₀c in
omit hj hH₀ in
theorem isBoundedForm_globalKernel : IsBoundedForm (globalKernel μ π hπ j H₀ ψ hψ) := by
  intro k k' x
  refine ⟨‖opA μ π hπ j H₀ ψ hψ k‖ * ‖x‖ * ‖opA μ π hπ j H₀ ψ hψ k'‖, fun w w' => ?_⟩
  rw [globalKernel_apply]
  calc ‖⟪opA μ π hπ j H₀ ψ hψ k w, (x : H →L[ℂ] H) (opA μ π hπ j H₀ ψ hψ k' w')⟫_ℂ‖
      ≤ ‖opA μ π hπ j H₀ ψ hψ k w‖ * ‖(x : H →L[ℂ] H) (opA μ π hπ j H₀ ψ hψ k' w')‖ :=
        norm_inner_le_norm _ _
    _ ≤ (‖opA μ π hπ j H₀ ψ hψ k‖ * ‖w‖) * (‖x‖ * (‖opA μ π hπ j H₀ ψ hψ k'‖ * ‖w'‖)) := by
        refine mul_le_mul ((opA μ π hπ j H₀ ψ hψ k).le_opNorm w) ?_ (norm_nonneg _)
          (by positivity)
        exact ((x : H →L[ℂ] H).le_opNorm _).trans (mul_le_mul_of_nonneg_left
          ((opA μ π hπ j H₀ ψ hψ k').le_opNorm w') (norm_nonneg _))
    _ = _ := by ring

omit hj hH₀ hπu in
theorem re_globalKernel_diag (k : κ) (w : W) :
    (globalKernel μ π hπ j H₀ ψ hψ (k, k, 1, w, w)).re = ‖opA μ π hπ j H₀ ψ hψ k w‖ ^ 2 := by
  rw [globalKernel_apply]
  change (⟪_, (1 : H →L[ℂ] H) _⟫_ℂ).re = _
  rw [one_apply_eq_self]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm

end Global

end Langlands.Analysis.TemperedComponent
