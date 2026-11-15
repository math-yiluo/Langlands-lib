import Langlands.Representation.Archimedean.BGChaseReps
import Langlands.Algebra.UniversalEnvelopingFiltration
import Langlands.Representation.Archimedean.RealGKInfinitesimalCharacter
import Langlands.Representation.Archimedean.Kostant.Center

/-!
# The enveloping algebra of `𝔤𝔩_n(ℂ)`: helpers for the Bernstein–Gelfand chase

The adjoint representation of `𝔤𝔩_n(ℂ)` on `U = U(𝔤𝔩_n(ℂ))` and its integral weights, the
stability of the degree filtration, the transpose anti-automorphism of `U`, and the right
action `u ↦ Λ(uᵗ)` of `U` attached to a representation, with its central character.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean.BGChase

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Algebra.UniversalEnveloping

universe uV uX uY

variable {n : ℕ}

local notation "gl" => Matrix (Fin n) (Fin n) ℂ
local notation "U" => UniversalEnvelopingAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ)

/-! ## Representations of `U` -/

section Env

variable {X : Type uX} [AddCommGroup X] [Module ℂ X] {Y : Type uY} [AddCommGroup Y] [Module ℂ Y]

/-- A linear map intertwining two Lie algebra representations intertwines the actions of the
enveloping algebra. -/
theorem env_intertwine (σ : gl →ₗ⁅ℂ⁆ Module.End ℂ X) (τ : gl →ₗ⁅ℂ⁆ Module.End ℂ Y)
    (g : X →ₗ[ℂ] Y) (hg : ∀ a x, g (σ a x) = τ a (g x)) (u : U) (x : X) :
    g (envelopingAction σ u x) = envelopingAction τ u (g x) := by
  induction u using InfinitesimalCharacter.envInduction generalizing x with
  | algebraMap c =>
    simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
  | ι a =>
    simp only [UniversalEnvelopingAlgebra.lift_ι_apply, hg]
  | mul a b ha hb =>
    simp only [map_mul, Module.End.mul_apply, ha, hb]
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, ha, hb]

/-- Operators commuting with a representation commute with its enveloping action. -/
theorem env_commute (σ : gl →ₗ⁅ℂ⁆ Module.End ℂ X) (T : Module.End ℂ X)
    (hT : ∀ a, σ a * T = T * σ a) (u : U) :
    envelopingAction σ u * T = T * envelopingAction σ u := by
  induction u using InfinitesimalCharacter.envInduction with
  | algebraMap c =>
    rw [AlgHom.commutes, Algebra.commutes]
  | ι a =>
    rw [UniversalEnvelopingAlgebra.lift_ι_apply, hT]
  | mul a b ha hb =>
    rw [map_mul, mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | add a b ha hb =>
    rw [map_add, add_mul, mul_add, ha, hb]

end Env

/-! ## The adjoint representation on `U` -/

/-- The adjoint action `Y ↦ [ι Y, -]` of `𝔤𝔩_n(ℂ)` on `U(𝔤𝔩_n(ℂ))`. -/
def adU : gl →ₗ⁅ℂ⁆ Module.End ℂ U :=
  (LieAlgebra.ad ℂ U).comp (UniversalEnvelopingAlgebra.ι ℂ)

theorem adU_apply (Y : gl) (u : U) :
    adU Y u = UniversalEnvelopingAlgebra.ι ℂ Y * u - u * UniversalEnvelopingAlgebra.ι ℂ Y := by
  simp [adU, LieAlgebra.ad_apply, Ring.lie_def]

theorem lie_single_diag (p a b : Fin n) :
    Matrix.single p p (1 : ℂ) * Matrix.single a b 1 - Matrix.single a b 1 * Matrix.single p p 1 =
      (((Pi.single a 1 - Pi.single b 1 : Fin n → ℤ) p : ℤ) : ℂ) • Matrix.single a b 1 := by
  by_cases hpa : p = a <;> by_cases hpb : p = b
  · subst hpa; subst hpb; simp
  · subst hpa
    simp [hpb, Ne.symm hpb]
  · subst hpb
    simp [hpa]
  · simp [hpa, hpb, Ne.symm hpb]

theorem isWt_adU_single (a b : Fin n) :
    IsWt (diagOps (adU (n := n))) (Pi.single a 1 - Pi.single b 1)
      (UniversalEnvelopingAlgebra.ι ℂ (Matrix.single a b 1)) := by
  intro p
  change adU _ _ = _
  simp only [adU, LieHom.coe_comp, Function.comp_apply, LieAlgebra.ad_apply]
  rw [← LieHom.map_lie, Ring.lie_def, lie_single_diag, map_smul]

theorem adU_mul (Y : gl) (a b : U) : adU Y (a * b) = adU Y a * b + a * adU Y b := by
  simp only [adU_apply]
  noncomm_ring

theorem adU_algebraMap (Y : gl) (c : ℂ) : adU Y (algebraMap ℂ U c) = 0 := by
  rw [adU_apply, ← Algebra.commutes, sub_self]

theorem isWt_adU_mul {m₁ m₂ : Fin n → ℤ} {a b : U} (ha : IsWt (diagOps (adU (n := n))) m₁ a)
    (hb : IsWt (diagOps (adU (n := n))) m₂ b) :
    IsWt (diagOps (adU (n := n))) (m₁ + m₂) (a * b) := by
  intro p
  change adU _ (a * b) = _
  rw [adU_mul]
  change diagOps adU p a * b + a * diagOps adU p b = _
  rw [ha p, hb p, smul_mul_assoc, mul_smul_comm, ← add_smul]
  simp only [Pi.add_apply, Int.cast_add]

theorem intSpan_adU_mul_le :
    intSpan (diagOps (adU (n := n))) * intSpan (diagOps (adU (n := n))) ≤
      intSpan (diagOps (adU (n := n))) := by
  rw [intSpan, Submodule.span_mul_span]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, ⟨m₁, ha⟩, b, ⟨m₂, hb⟩, rfl⟩
  exact mem_intSpan_of_isWt (isWt_adU_mul ha hb)

/-- The adjoint representation of `𝔤𝔩_n(ℂ)` on `U(𝔤𝔩_n(ℂ))` has integral weights. -/
theorem intSpan_adU : intSpan (diagOps (adU (n := n))) = ⊤ := by
  rw [eq_top_iff]
  rintro u -
  induction u using InfinitesimalCharacter.envInduction with
  | algebraMap c =>
    exact mem_intSpan_of_isWt (m := 0) fun p => by
      change adU _ _ = _
      simp [adU_algebraMap]
  | ι x =>
    rw [Matrix.matrix_eq_sum_single x]
    simp only [map_sum]
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
    have h : Matrix.single a b (x a b) = x a b • Matrix.single a b (1 : ℂ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [h, map_smul]
    exact Submodule.smul_mem _ _ (mem_intSpan_of_isWt (isWt_adU_single a b))
  | mul a b ha hb => exact intSpan_adU_mul_le (Submodule.mul_mem_mul ha hb)
  | add a b ha hb => exact Submodule.add_mem _ ha hb

/-- The adjoint action preserves the degree filtration. -/
theorem adU_mem_degreeFiltration (Y : gl) {d : ℕ} {u : U}
    (hu : u ∈ degreeFiltration ℂ gl d) : adU Y u ∈ degreeFiltration ℂ gl d := by
  rw [adU_apply]
  exact commutator_degreeOne_mem ℂ gl (generator_mem_degreeOne ℂ gl Y) hu

/-! ## The transpose anti-automorphism -/

/-- The Lie algebra map `Y ↦ ι(Yᵀ)` into the opposite algebra of `U`. -/
def trLie : gl →ₗ⁅ℂ⁆ Uᵐᵒᵖ where
  toFun Y := MulOpposite.op (UniversalEnvelopingAlgebra.ι ℂ Y.transpose)
  map_add' X Y := by simp [Matrix.transpose_add]
  map_smul' c Y := by simp [Matrix.transpose_smul]
  map_lie' {X Y} := by
    have h : Y.transpose * X.transpose - X.transpose * Y.transpose =
        ⁅Y.transpose, X.transpose⁆ := (Ring.lie_def _ _).symm
    change MulOpposite.op (UniversalEnvelopingAlgebra.ι ℂ (⁅X, Y⁆ : gl).transpose) = _
    rw [Ring.lie_def X Y, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, h,
      LieHom.map_lie, Ring.lie_def, Ring.lie_def, MulOpposite.op_sub, MulOpposite.op_mul,
      MulOpposite.op_mul]

/-- The transpose as an algebra map `U → Uᵐᵒᵖ`. -/
def trOp : U →ₐ[ℂ] Uᵐᵒᵖ := UniversalEnvelopingAlgebra.lift ℂ trLie

/-- The transpose `u ↦ uᵗ` of `U`: the linear anti-automorphism with `(ι Y)ᵗ = ι(Yᵀ)`. -/
def trU : U →ₗ[ℂ] U :=
  (MulOpposite.opLinearEquiv ℂ).symm.toLinearMap ∘ₗ (trOp (n := n)).toLinearMap

theorem trU_apply (u : U) : trU u = MulOpposite.unop (trOp u) := rfl

theorem trU_mul (a b : U) : trU (a * b) = trU b * trU a := by
  simp only [trU_apply, map_mul, MulOpposite.unop_mul]

theorem trU_ι (Y : gl) :
    trU (UniversalEnvelopingAlgebra.ι ℂ Y) = UniversalEnvelopingAlgebra.ι ℂ Y.transpose := by
  simp only [trU_apply, trOp, UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

theorem trU_algebraMap (c : ℂ) : trU (algebraMap ℂ U c) = algebraMap ℂ U c := by
  simp only [trU_apply, AlgHom.commutes, MulOpposite.algebraMap_apply, MulOpposite.unop_op]

theorem trU_one : trU (1 : U) = 1 := by
  simpa using trU_algebraMap (n := n) 1

theorem trU_trU (u : U) : trU (trU u) = u := by
  induction u using InfinitesimalCharacter.envInduction with
  | algebraMap c => rw [trU_algebraMap, trU_algebraMap]
  | ι x => rw [trU_ι, trU_ι, Matrix.transpose_transpose]
  | mul a b ha hb => rw [trU_mul, trU_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem trU_mem_center {z : U} (hz : z ∈ Subalgebra.center ℂ U) :
    trU z ∈ Subalgebra.center ℂ U := by
  refine Kostant.mem_center_of_commute ℂ gl fun x => ?_
  have hx : UniversalEnvelopingAlgebra.ι ℂ x =
      trU (UniversalEnvelopingAlgebra.ι ℂ x.transpose) := by
    rw [trU_ι, Matrix.transpose_transpose]
  rw [hx, ← trU_mul, ← trU_mul, (Subalgebra.mem_center_iff.1 hz _)]

/-! ## The right action attached to a representation -/

section Right

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The right action `u ↦ Λ(uᵗ)` of `U` on `V` attached to a representation `ℓ`, where `Λ` is
the enveloping action of `ℓ`: `ρ(u v) = ρ(v) ρ(u)` and `ρ(ι Y) = ℓ(Yᵀ)`. -/
def rhoR (ℓ : gl →ₗ⁅ℂ⁆ Module.End ℂ V) : U →ₗ[ℂ] Module.End ℂ V :=
  (envelopingAction ℓ).toLinearMap ∘ₗ trU

theorem rhoR_apply (ℓ : gl →ₗ⁅ℂ⁆ Module.End ℂ V) (u : U) : rhoR ℓ u = envelopingAction ℓ (trU u) := rfl

theorem rhoR_mul (ℓ : gl →ₗ⁅ℂ⁆ Module.End ℂ V) (a b : U) : rhoR ℓ (a * b) = rhoR ℓ b * rhoR ℓ a := by
  rw [rhoR_apply, trU_mul, map_mul]
  rfl

theorem rhoR_one (ℓ : gl →ₗ⁅ℂ⁆ Module.End ℂ V) : rhoR ℓ 1 = 1 := by
  rw [rhoR_apply, trU_one, map_one]

theorem rhoR_algebraMap (ℓ : gl →ₗ⁅ℂ⁆ Module.End ℂ V) (c : ℂ) : rhoR ℓ (algebraMap ℂ U c) = algebraMap ℂ _ c := by
  rw [rhoR_apply, trU_algebraMap, AlgHom.commutes]

theorem rhoR_ι (ℓ : gl →ₗ⁅ℂ⁆ Module.End ℂ V) (Y : gl) : rhoR ℓ (UniversalEnvelopingAlgebra.ι ℂ Y) = ℓ Y.transpose := by
  rw [rhoR_apply, trU_ι, UniversalEnvelopingAlgebra.lift_ι_apply]

/-- Operators commuting with `ℓ` commute with the right action. -/
theorem rhoR_commute (ℓ : gl →ₗ⁅ℂ⁆ Module.End ℂ V) (T : Module.End ℂ V) (hT : ∀ a, ℓ a * T = T * ℓ a) (u : U) :
    rhoR ℓ u * T = T * rhoR ℓ u :=
  env_commute ℓ T hT (trU u)

/-- If the center acts by scalars through `ℓ` and `V ≠ 0`, it acts by scalars through the right
action, via a character. -/
theorem exists_rhoR_character (ℓ : gl →ₗ⁅ℂ⁆ Module.End ℂ V) [Nontrivial V] (hℓ : HasInfinitesimalCharacter ℓ) :
    ∃ χ : Subalgebra.center ℂ U →ₐ[ℂ] ℂ,
      ∀ z : Subalgebra.center ℂ U, rhoR ℓ z = algebraMap ℂ (Module.End ℂ V) (χ z) := by
  have hinj : Function.Injective (algebraMap ℂ (Module.End ℂ V)) := by
    intro a b h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h' := LinearMap.congr_fun h v
    simp only [Module.algebraMap_end_apply] at h'
    exact smul_left_injective ℂ hv h'
  have hc : ∀ z : Subalgebra.center ℂ U, ∃ c : ℂ,
      rhoR ℓ z = algebraMap ℂ (Module.End ℂ V) c := fun z => hℓ _ (trU_mem_center z.2)
  choose c hc using hc
  have h1 : c 1 = 1 := hinj (by rw [← hc, map_one, OneMemClass.coe_one, rhoR_one])
  have h2 : ∀ z w, c (z * w) = c z * c w := fun z w => hinj (by
    rw [← hc, map_mul, Subalgebra.coe_mul, rhoR_mul, hc w, hc z, ← map_mul, ← map_mul,
      mul_comm])
  have h3 : c 0 = 0 := hinj (by rw [← hc, map_zero, ZeroMemClass.coe_zero, map_zero])
  have h4 : ∀ z w, c (z + w) = c z + c w := fun z w => hinj (by
    rw [← hc, map_add, ← hc, ← hc, Subalgebra.coe_add, map_add])
  have h5 : ∀ a : ℂ, c (algebraMap ℂ (Subalgebra.center ℂ U) a) = a := fun a => hinj (by
    rw [← hc]
    exact rhoR_algebraMap ℓ a)
  exact ⟨{ toFun := c, map_one' := h1, map_mul' := h2, map_zero' := h3, map_add' := h4,
           commutes' := h5 }, hc⟩

end Right

end Langlands.Archimedean.BGChase
