import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchwartzActionConvolution
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TraceCoefficientFamily
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.L2
import Langlands.Representation.Plancherel.CoefficientTensorForm
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # The Fourier transform `f ↦ f̂(ω, P)` and Lemma VII.1.1 of Waldspurger

For a smooth representation `A` with smooth dual `Ã`, a tensor `v ⊗ ℓ ∈ A ⊗ Ã` gives the
endomorphism `w ↦ ℓ(w) v` of `A`. This is Waldspurger's embedding VII.1 (1)
`L(ω, P) = E ⊗ Ě ↪ End(E)`, here for an arbitrary smooth representation in place of
`I_P^G E`. Its image consists of finite-rank operators, and the trace of the image of a
tensor `t` is the value at `1` of its coefficient `g ↦ ⟨π(g) v, ℓ⟩`.

If `A` is admissible with tempered coefficients and `f ∈ C(G)`, then `π(f)` lies in the image
of the embedding, provided `G` has a compact open subgroup and the Haar measure is left and
right invariant. So `π(f)` is a tensor `schwartzActionTensor f`. For a real `d` (Waldspurger's
formal degree `d(ω)`), `coefficientFourierTransform d f = d · π(f̌)` is Waldspurger's
`f̂(ω, P)`, with `f̌(g) = f(g⁻¹)`.

Lemma VII.1.1:
* (i) `(ρ(g) λ(h) f)^ = (π(g) ⊗ π̌(h)) f̂`;
* (ii) `∫_G conj(E ψ(g)) f(g) dg = (ψ, f̂)`, where `E ψ` is the coefficient of `ψ` and the
  form on `A ⊗ Ã` is `d⁻¹` times the tensor form `(v₁, v₂)(ℓ₁, ℓ₂)` of a positive invariant
  form `b` on `A` and the form it induces on `Ã`;
* (iii) `E f̂ (g) = d θ_π(λ(g) f̌)`.
-/

noncomputable section

universe u v

open MeasureTheory Filter
open scoped TensorProduct ComplexConjugate
open Langlands.Plancherel (CoefficientTensor coefficientTensorMap coefficientTensorMap_tmul
  coefficientTensorAction coefficientTensorAction_tmul coefficientTensorMap_action
  coefficientTensorInvariantForm coefficientTensorInvariantForm_inner_tmul)

namespace Langlands.HarishChandraSchwartz

section Embedding

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : SmoothRep.{0, u, v} ℂ G)

/-- Waldspurger VII.1 (1): the linear map `A ⊗ Ã → End(A)`, `v ⊗ ℓ ↦ (w ↦ ℓ(w) v)`. -/
def coefficientTensorToEnd : CoefficientTensor A →ₗ[ℂ] Module.End ℂ A :=
  TensorProduct.lift (LinearMap.mk₂ ℂ
    (fun (v : A) (ℓ : SmoothDual A.representation) => ℓ.val.smulRight v)
    (fun v₁ v₂ ℓ => LinearMap.ext fun w => smul_add (ℓ.val w) v₁ v₂)
    (fun c v ℓ => LinearMap.ext fun w => smul_comm (ℓ.val w) c v)
    (fun v ℓ₁ ℓ₂ => LinearMap.ext fun w => add_smul (ℓ₁.val w) (ℓ₂.val w) v)
    (fun c v ℓ => LinearMap.ext fun w => mul_smul c (ℓ.val w) v))

omit [IsTopologicalGroup G] in
@[simp]
theorem coefficientTensorToEnd_tmul (v : A) (ℓ : SmoothDual A.representation) (w : A) :
    coefficientTensorToEnd A (v ⊗ₜ[ℂ] ℓ) w = ℓ.val w • v :=
  rfl

omit [IsTopologicalGroup G] in
/-- For a basis `ℬ` of `A`, the `i`-th coefficient in `t = ∑ᵢ ℬᵢ ⊗ ℓᵢ` is read off from the
`i`-th coordinate of the endomorphism of `t`. -/
theorem equivFinsuppOfBasisLeft_apply_val {ι : Type*} [DecidableEq ι] (ℬ : Module.Basis ι ℂ A)
    (t : CoefficientTensor A) (i : ι) (w : A) :
    (TensorProduct.equivFinsuppOfBasisLeft ℬ t i).val w =
      ℬ.coord i (coefficientTensorToEnd A t w) := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, coefficientTensorToEnd_tmul,
      map_smul, Module.Basis.coord_apply, smul_eq_mul, mul_comm]
    rfl
  | add x y hx hy =>
    rw [map_add, Finsupp.add_apply, Submodule.coe_add, LinearMap.add_apply, hx, hy, map_add,
      LinearMap.add_apply, map_add]

omit [IsTopologicalGroup G] in
/-- The map `A ⊗ Ã → End(A)` is injective, so it is an embedding as in VII.1 (1). -/
theorem coefficientTensorToEnd_injective : Function.Injective (coefficientTensorToEnd A) := by
  classical
  let ℬ := Module.Basis.ofVectorSpace ℂ A
  refine (injective_iff_map_eq_zero _).mpr fun t ht => ?_
  have h0 : TensorProduct.equivFinsuppOfBasisLeft ℬ t = 0 := by
    ext i : 1
    refine Subtype.ext (LinearMap.ext fun w => ?_)
    rw [equivFinsuppOfBasisLeft_apply_val A ℬ t i w, ht]
    simp
  exact (TensorProduct.equivFinsuppOfBasisLeft ℬ).map_eq_zero_iff.mp h0

omit [IsTopologicalGroup G] in
/-- The endomorphism of a tensor has finite rank. -/
theorem coefficientTensorToEnd_mem_finiteRankEnd (t : CoefficientTensor A) :
    coefficientTensorToEnd A t ∈ finiteRankEnd A := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    have h : coefficientTensorToEnd A (v ⊗ₜ[ℂ] ℓ) = (FiniteRankEnd.rankOne ℓ.val v).val :=
      LinearMap.ext fun _ => rfl
    rw [h]
    exact Subtype.property _
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

/-- The embedding `A ⊗ Ã → End(A)` with values in the finite-rank endomorphisms. -/
def coefficientTensorFiniteRank : CoefficientTensor A →ₗ[ℂ] finiteRankEnd A :=
  (coefficientTensorToEnd A).codRestrict (finiteRankEnd A)
    (coefficientTensorToEnd_mem_finiteRankEnd A)

omit [IsTopologicalGroup G] in
@[simp]
theorem coefficientTensorFiniteRank_val (t : CoefficientTensor A) :
    (coefficientTensorFiniteRank A t).val = coefficientTensorToEnd A t :=
  rfl

/-- The trace of the endomorphism of `t` is the value at `1` of the coefficient of `t`: the
composite of the trace with VII.1 (1) is `v ⊗ ℓ ↦ ℓ(v)`. -/
theorem trace_coefficientTensorFiniteRank (t : CoefficientTensor A) :
    FiniteRankEnd.trace (coefficientTensorFiniteRank A t) = coefficientTensorMap A t 1 := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    have h : coefficientTensorFiniteRank A (v ⊗ₜ[ℂ] ℓ) = FiniteRankEnd.rankOne ℓ.val v :=
      Subtype.ext (LinearMap.ext fun _ => rfl)
    rw [h, FiniteRankEnd.trace_rankOne, coefficientTensorMap_tmul, map_one, Module.End.one_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, LocallyConstant.add_apply]

/-- The action of `(g, h)` on `A ⊗ Ã` becomes `T ↦ π(g) T π(h)⁻¹` on endomorphisms. -/
theorem coefficientTensorToEnd_action (x : G × G) (t : CoefficientTensor A) :
    coefficientTensorToEnd A (coefficientTensorAction A x t) =
      A.representation x.1 * coefficientTensorToEnd A t * A.representation x.2⁻¹ := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    refine LinearMap.ext fun w => ?_
    rw [coefficientTensorAction_tmul, coefficientTensorToEnd_tmul, Module.End.mul_apply,
      Module.End.mul_apply, coefficientTensorToEnd_tmul, map_smul]
    rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, mul_add, add_mul]

/-- The coefficient of `t` at `g` is the trace of `π(g)` composed with the endomorphism of
`t`. -/
theorem coefficientTensorMap_eq_trace (t : CoefficientTensor A) (g : G) :
    coefficientTensorMap A t g =
      FiniteRankEnd.trace (coefficientTensorFiniteRank A (coefficientTensorAction A (g, 1) t)) := by
  rw [trace_coefficientTensorFiniteRank, coefficientTensorMap_action]
  simp

end Embedding

section Form

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : SmoothRep.{0, u, v} ℂ G)
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
  (hA : IsAdmissible A.representation)

/-- The form of `v ⊗ ℓ` against a tensor `t` is `b(v, T(v'))`, where `T` is the endomorphism of
`t` and `v'` is the vector with `ℓ = b(v', -)`. -/
theorem coefficientTensorInvariantForm_inner_tmul_left
    (b : InvariantPositiveForm A.representation) (v : A) (ℓ : SmoothDual A.representation)
    (t : CoefficientTensor A) :
    (coefficientTensorInvariantForm A hcof hA b).inner (v ⊗ₜ[ℂ] ℓ) t =
      b.inner v (coefficientTensorToEnd A t ((b.smoothDualEquiv hcof hA).symm ℓ)) := by
  induction t using TensorProduct.inductionOn with
  | tmul w m =>
    rw [coefficientTensorInvariantForm_inner_tmul, coefficientTensorToEnd_tmul]
    have hm : m.val ((b.smoothDualEquiv hcof hA).symm ℓ) =
        b.inner ((b.smoothDualEquiv hcof hA).symm m) ((b.smoothDualEquiv hcof hA).symm ℓ) := by
      conv_lhs => rw [← (b.smoothDualEquiv hcof hA).apply_symm_apply m]
      rfl
    have hs : b.inner v (m.val ((b.smoothDualEquiv hcof hA).symm ℓ) • w) =
        m.val ((b.smoothDualEquiv hcof hA).symm ℓ) * b.inner v w := by
      let := b.toInnerProductCore
      exact InnerProductSpace.Core.inner_smul_right _ _
    rw [hs, hm, mul_comm]
    rfl
  | add x y hx hy =>
    rw [InvariantPositiveForm.add_right, hx, hy, map_add, LinearMap.add_apply,
      InvariantPositiveForm.add_right]

end Form

section Operator

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
  [Nonempty (CompactOpenSubgroup G)]
  {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {Ξ σ : G → ℝ}
  (A : SmoothRep.{0, u, v} ℂ G) (hw : L2Weights μ Ξ σ) (hA : IsAdmissible A.representation)
  (hT : HasTemperedCoefficients Ξ σ A.representation)

omit [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G] in
/-- Every `f ∈ C(G)` is right invariant under some compact open subgroup. -/
theorem Space.exists_rightInvariant (f : Space Ξ σ) :
    ∃ K : CompactOpenSubgroup G, ∀ k ∈ K.toSubgroup, ∀ g, f (g * k) = f g := by
  obtain ⟨K, hK⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (Space.coe_mem f)
  refine ⟨K, fun k hk g => ?_⟩
  have h₁ := hK.1 1 (one_mem _) k hk g
  rw [one_mul] at h₁
  exact h₁

/-- For `f` right invariant under `H` and a right invariant measure, `π(f) π(k) = π(f)` for
`k ∈ H`. -/
theorem schwartzAction_apply_rho_of_mem {H : Subgroup G} {f : Space Ξ σ}
    (hf : ∀ k ∈ H, ∀ g, f (g * k) = f g) {k : G} (hk : k ∈ H) (w : A) :
    schwartzAction hw hA hT f (A.representation k w) = schwartzAction hw hA hT f w := by
  refine ext_smoothDual hA.1 fun ℓ => ?_
  rw [schwartzAction_eval, schwartzAction_eval]
  rw [← integral_mul_right_eq_self (fun x => f x * ℓ.val (A.representation x w)) k]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  change f x * ℓ.val (A.representation x (A.representation k w)) =
    f (x * k) * ℓ.val (A.representation (x * k) w)
  rw [hf k hk x, map_mul, Module.End.mul_apply]

/-- Waldspurger VII.1: `π(f)`, `f ∈ C(G)`, lies in the image of `A ⊗ Ã ↪ End(A)`. -/
theorem exists_coefficientTensorToEnd_eq_schwartzAction (f : Space Ξ σ) :
    ∃ t : CoefficientTensor A, coefficientTensorToEnd A t = schwartzAction hw hA hT f := by
  classical
  obtain ⟨K, hK⟩ := Space.exists_rightInvariant f
  have : FiniteDimensional ℂ (fixedVectors A.representation K.toSubgroup) := hA.2 K.1
  let b := Module.finBasis ℂ (fixedVectors A.representation K.toSubgroup)
  refine ⟨∑ i, schwartzAction hw hA hT f (b i) ⊗ₜ[ℂ]
    fixedFunctional A.representation hA.1 K (b.coord i), LinearMap.ext fun w => ?_⟩
  rw [map_sum, LinearMap.sum_apply]
  simp only [coefficientTensorToEnd_tmul]
  have hsum : ∑ i, (fixedFunctional A.representation hA.1 K (b.coord i)).val w •
      schwartzAction hw hA hT f (b i) =
      schwartzAction hw hA hT f (averageProjection A.representation hA.1 K w : A) := by
    conv_rhs => rw [← b.sum_repr (averageProjection A.representation hA.1 K w)]
    rw [Submodule.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, map_smul]
    rfl
  rw [hsum, averageProjection_apply]
  exact Jacquet.map_averageMap_of_forall_eq A.representation hA.1 K.1 K.2
    (schwartzAction hw hA hT f) w _
    fun k => schwartzAction_apply_rho_of_mem A hw hA hT hK k.2 w

/-- The tensor of `π(f)`: the unique `t ∈ A ⊗ Ã` whose endomorphism is `π(f)`, linear in
`f ∈ C(G)`. -/
def schwartzActionTensor : Space Ξ σ →ₗ[ℂ] CoefficientTensor A :=
  (LinearEquiv.ofInjective (coefficientTensorToEnd A)
      (coefficientTensorToEnd_injective A)).symm.toLinearMap ∘ₗ
    (schwartzAction hw hA hT).codRestrict (LinearMap.range (coefficientTensorToEnd A))
      fun f => LinearMap.mem_range.mpr (exists_coefficientTensorToEnd_eq_schwartzAction A hw hA hT f)

@[simp]
theorem coefficientTensorToEnd_schwartzActionTensor (f : Space Ξ σ) :
    coefficientTensorToEnd A (schwartzActionTensor A hw hA hT f) = schwartzAction hw hA hT f :=
  congrArg Subtype.val ((LinearEquiv.ofInjective (coefficientTensorToEnd A)
    (coefficientTensorToEnd_injective A)).apply_symm_apply
      ⟨schwartzAction hw hA hT f, LinearMap.mem_range.mpr
        (exists_coefficientTensorToEnd_eq_schwartzAction A hw hA hT f)⟩)

/-- Uniqueness: a tensor whose endomorphism is `π(f)` is `schwartzActionTensor f`. -/
theorem schwartzActionTensor_eq_of_coefficientTensorToEnd_eq {f : Space Ξ σ}
    {t : CoefficientTensor A} (h : coefficientTensorToEnd A t = schwartzAction hw hA hT f) :
    schwartzActionTensor A hw hA hT f = t :=
  coefficientTensorToEnd_injective A (by rw [coefficientTensorToEnd_schwartzActionTensor, h])

variable (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g)

/-- Waldspurger VII.1: the Fourier transform `f̂ = d · π(f̌) ∈ A ⊗ Ã`, `f ∈ C(G)`, where
`f̌(g) = f(g⁻¹)` and `π(f̌)` is identified with a tensor by VII.1 (1). For `A = I_P^G E` and
`d = d(ω)` this is Waldspurger's `f̂(ω, P)`. -/
def coefficientFourierTransform (d : ℝ) : Space Ξ σ →ₗ[ℂ] CoefficientTensor A :=
  (d : ℂ) • (schwartzActionTensor A hw hA hT ∘ₗ (Space.check hΞ hσ).toLinearMap)

theorem coefficientFourierTransform_apply (d : ℝ) (f : Space Ξ σ) :
    coefficientFourierTransform A hw hA hT hΞ hσ d f =
      (d : ℂ) • schwartzActionTensor A hw hA hT (Space.check hΞ hσ f) :=
  rfl

/-- The endomorphism of `f̂` is `d · π(f̌)`. -/
theorem coefficientTensorToEnd_coefficientFourierTransform (d : ℝ) (f : Space Ξ σ) :
    coefficientTensorToEnd A (coefficientFourierTransform A hw hA hT hΞ hσ d f) =
      (d : ℂ) • schwartzAction hw hA hT (Space.check hΞ hσ f) := by
  rw [coefficientFourierTransform_apply, map_smul, coefficientTensorToEnd_schwartzActionTensor]

omit [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
  [Nonempty (CompactOpenSubgroup G)] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] in
/-- `(ρ(g) λ(h) f)ˇ = ρ(h) λ(g) f̌`. -/
theorem Space.check_translate (ht : TranslationWeights Ξ σ) (g h : G) (f : Space Ξ σ) :
    Space.check hΞ hσ (Space.translate ht g h f) = Space.translate ht h g (Space.check hΞ hσ f) :=
  Space.ext fun x => by
    simp only [Space.coe_check, check_apply, Space.translate_apply, mul_inv_rev, inv_inv,
      mul_assoc]

/-- Lemma VII.1.1 (i): `(ρ(g) λ(h) f)^ = (π(g) ⊗ π̌(h)) f̂`. -/
theorem coefficientFourierTransform_translate (ht : TranslationWeights Ξ σ) (d : ℝ) (g h : G)
    (f : Space Ξ σ) :
    coefficientFourierTransform A hw hA hT hΞ hσ d (Space.translate ht g h f) =
      coefficientTensorAction A (g, h) (coefficientFourierTransform A hw hA hT hΞ hσ d f) := by
  rw [coefficientFourierTransform_apply, coefficientFourierTransform_apply, map_smul]
  congr 1
  refine schwartzActionTensor_eq_of_coefficientTensorToEnd_eq A hw hA hT ?_
  rw [coefficientTensorToEnd_action, coefficientTensorToEnd_schwartzActionTensor,
    Space.check_translate]
  have h₁ : Space.translate ht h g (Space.check hΞ hσ f) =
      Space.translate ht 1 g (Space.translate ht h 1 (Space.check hΞ hσ f)) :=
    Space.ext fun x => by simp only [Space.translate_apply, inv_one, one_mul, mul_one]
  rw [h₁, schwartzAction_translate_left hw ht hA hT, schwartzAction_translate_right hw ht hA hT,
    mul_assoc]

/-- Lemma VII.1.1 (iii): `E f̂ (g) = d θ_π(λ(g) f̌)`, where `E` sends a tensor to its
coefficient and `θ_π` is the character of `π`. -/
theorem coefficientTensorMap_coefficientFourierTransform (ht : TranslationWeights Ξ σ) (d : ℝ)
    (f : Space Ξ σ) (g : G) :
    coefficientTensorMap A (coefficientFourierTransform A hw hA hT hΞ hσ d f) g =
      d * schwartzCharacter hw hA hT (Space.translate ht 1 g (Space.check hΞ hσ f)) := by
  rw [coefficientFourierTransform_apply, map_smul, LocallyConstant.coe_smul, Pi.smul_apply,
    smul_eq_mul, coefficientTensorMap_eq_trace, schwartzCharacter_apply]
  congr 2
  refine Subtype.ext ?_
  rw [coefficientTensorFiniteRank_val, coefficientTensorToEnd_action,
    coefficientTensorToEnd_schwartzActionTensor, finiteRankSchwartzAction_val,
    schwartzAction_translate_left hw ht hA hT, inv_one, map_one, mul_one]

/-- Lemma VII.1.1 (iii) at `g = 1`: the trace of `f̂` (the value at `1` of its coefficient) is
`d θ_π(f̌)`. -/
theorem coefficientTensorMap_coefficientFourierTransform_one (d : ℝ) (f : Space Ξ σ) :
    coefficientTensorMap A (coefficientFourierTransform A hw hA hT hΞ hσ d f) 1 =
      d * schwartzCharacter hw hA hT (Space.check hΞ hσ f) := by
  rw [coefficientFourierTransform_apply, map_smul, LocallyConstant.coe_smul, Pi.smul_apply,
    smul_eq_mul, ← trace_coefficientTensorFiniteRank, schwartzCharacter_apply]
  congr 2
  exact Subtype.ext (coefficientTensorToEnd_schwartzActionTensor A hw hA hT _)

omit [MeasurableMul G] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] in
include hw hA hT in
/-- `g ↦ conj(E ψ(g)) f(g)` is integrable for every tensor `ψ` and `f ∈ C(G)`. -/
theorem integrable_conj_coefficientTensorMap_mul (ψ : CoefficientTensor A) (f : Space Ξ σ) :
    Integrable (fun g => conj (coefficientTensorMap A ψ g) * f g) μ := by
  induction ψ using TensorProduct.inductionOn with
  | tmul v ℓ =>
    refine (integrable_coefficient hw hA.1 hT f v ℓ).mono ?_
      (Eventually.of_forall fun g => le_of_eq ?_)
    · exact ((Complex.continuous_conj.comp (continuous_coefficient hA.1 v ℓ)).mul
        (Space.continuous f)).aestronglyMeasurable
    · rw [coefficientTensorMap_tmul, norm_mul, norm_mul, Complex.norm_conj, mul_comm]
  | add x y hx hy =>
    have h : (fun g => conj (coefficientTensorMap A (x + y) g) * f g) =
        fun g => conj (coefficientTensorMap A x g) * f g +
          conj (coefficientTensorMap A y g) * f g := by
      funext g
      rw [map_add, LocallyConstant.add_apply, map_add, add_mul]
    rw [h]
    exact hx.add hy

/-- The computation in the proof of Lemma VII.1.1 (ii), before the factor `d`:
`∫_G conj(E ψ(g)) f(g) dg = (ψ, π(f̌))` for the tensor form of `b`. -/
theorem integral_conj_coefficientTensorMap_mul [MeasurableInv G] [μ.IsInvInvariant]
    (b : InvariantPositiveForm A.representation) (ψ : CoefficientTensor A) (f : Space Ξ σ) :
    ∫ g, conj (coefficientTensorMap A ψ g) * f g ∂μ =
      (coefficientTensorInvariantForm A CompactOpenSubgroup.cofinal hA b).inner ψ
        (schwartzActionTensor A hw hA hT (Space.check hΞ hσ f)) := by
  induction ψ using TensorProduct.inductionOn with
  | tmul v ℓ =>
    rw [coefficientTensorInvariantForm_inner_tmul_left,
      coefficientTensorToEnd_schwartzActionTensor]
    set v' := (b.smoothDualEquiv CompactOpenSubgroup.cofinal hA).symm ℓ with hv'
    have hℓ : ∀ x, ℓ.val x = b.inner v' x := fun x => by
      conv_lhs => rw [← (b.smoothDualEquiv CompactOpenSubgroup.cofinal hA).apply_symm_apply ℓ]
      rfl
    have hR : b.inner v (schwartzAction hw hA hT (Space.check hΞ hσ f) v') =
        ∫ x, f x⁻¹ * b.inner v (A.representation x v') ∂μ :=
      schwartzAction_eval hw hA hT _ v' (b.toSmoothDual hA.1 v)
    rw [hR, ← integral_inv_eq_self (fun x => f x⁻¹ * b.inner v (A.representation x v')) μ]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    change conj (ℓ.val (A.representation g v)) * f g =
      f g⁻¹⁻¹ * b.inner v (A.representation g⁻¹ v')
    rw [hℓ, b.conj_inner_symm, inv_inv, ← b.invariant g⁻¹ (A.representation g v) v',
      Representation.inv_self_apply, mul_comm]
  | add x y hx hy =>
    have h : (fun g => conj (coefficientTensorMap A (x + y) g) * f g) =
        fun g => conj (coefficientTensorMap A x g) * f g +
          conj (coefficientTensorMap A y g) * f g := by
      funext g
      rw [map_add, LocallyConstant.add_apply, map_add, add_mul]
    rw [h, integral_add (integrable_conj_coefficientTensorMap_mul A hw hA hT x f)
      (integrable_conj_coefficientTensorMap_mul A hw hA hT y f), hx, hy,
      (coefficientTensorInvariantForm A CompactOpenSubgroup.cofinal hA b).add_left]

/-- Lemma VII.1.1 (ii): `(E ψ, f)_G = (ψ, f̂)`, where `(φ₁, φ₂)_G = ∫_G conj(φ₁(g)) φ₂(g) dg`
and the form on `A ⊗ Ã` is `d⁻¹ (v₁, v₂)(ℓ₁, ℓ₂)` for a positive invariant form `b` on `A`
and the form it induces on `Ã`. -/
theorem integral_conj_coefficientTensorMap_mul_eq_inner [MeasurableInv G] [μ.IsInvInvariant]
    (d : ℝ) (hd : 0 < d) (b : InvariantPositiveForm A.representation) (ψ : CoefficientTensor A)
    (f : Space Ξ σ) :
    ∫ g, conj (coefficientTensorMap A ψ g) * f g ∂μ =
      ((coefficientTensorInvariantForm A CompactOpenSubgroup.cofinal hA b).rescale d⁻¹
        (inv_pos.mpr hd)).inner ψ (coefficientFourierTransform A hw hA hT hΞ hσ d f) := by
  rw [InvariantPositiveForm.rescale_inner, coefficientFourierTransform_apply,
    integral_conj_coefficientTensorMap_mul A hw hA hT hΞ hσ b ψ f]
  have hs : (coefficientTensorInvariantForm A CompactOpenSubgroup.cofinal hA b).inner ψ
      ((d : ℂ) • schwartzActionTensor A hw hA hT (Space.check hΞ hσ f)) =
      (d : ℂ) * (coefficientTensorInvariantForm A CompactOpenSubgroup.cofinal hA b).inner ψ
        (schwartzActionTensor A hw hA hT (Space.check hΞ hσ f)) := by
    let := (coefficientTensorInvariantForm A CompactOpenSubgroup.cofinal hA b).toInnerProductCore
    exact InnerProductSpace.Core.inner_smul_right _ _
  rw [hs, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hd.ne', Complex.ofReal_one, one_mul]

end Operator

end Langlands.HarishChandraSchwartz
