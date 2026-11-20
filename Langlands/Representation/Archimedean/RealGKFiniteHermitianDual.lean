import Langlands.Representation.Archimedean.RealContragredientProof
import Langlands.Representation.Unitary.HermitianDual

/-! # A positive form identifies an irreducible real module with its finite dual -/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false

namespace Langlands.FiniteVectors

universe uG uV uW

variable {K : Type uG} [Monoid K] {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ K V} {σ : Representation ℂ K W}

/-- Compact finiteness is preserved by a conjugate-linear intertwiner. -/
theorem IsFiniteVector.map_conjugateLinear (T : V →ₗ⋆[ℂ] W)
    (hT : ∀ k v, T (ρ k v) = σ k (T v)) {v : V} (hv : IsFiniteVector ρ v) :
    IsFiniteVector σ (T v) := by
  have : FiniteDimensional ℂ (orbitSpan ρ v) := hv
  have he : (orbitSpan ρ v).map T = orbitSpan σ (T v) := by
    unfold orbitSpan
    rw [Submodule.map_span, ← Set.range_comp]
    apply congrArg (Submodule.span ℂ)
    exact congrArg Set.range (funext fun k => hT k v)
  change FiniteDimensional ℂ (orbitSpan σ (T v))
  rw [← he]
  infer_instance

end Langlands.FiniteVectors

namespace Langlands.InvariantPositiveForm

open KFiniteDual

universe uK uV

variable {K : Type uK} [Group K] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ K V}

/-- The conjugate-linear map `v ↦ b(v, -)` for the finite dual. -/
def toKFiniteDual (b : InvariantPositiveForm ρ)
    (hfin : ∀ v : V, FiniteVectors.IsFiniteVector ρ v) : V →ₗ⋆[ℂ] kDual ρ where
  toFun v := ⟨b.rightFunctional v, by
    let T : V →ₗ⋆[ℂ] Module.Dual ℂ V :=
      ⟨⟨b.rightFunctional, b.rightFunctional_add⟩, b.rightFunctional_smul⟩
    exact (hfin v).map_conjugateLinear T (fun k v => (b.dual_rightFunctional k v).symm)⟩
  map_add' v w := Subtype.ext (b.rightFunctional_add v w)
  map_smul' c v := Subtype.ext (b.rightFunctional_smul c v)

@[simp]
theorem toKFiniteDual_apply_apply (b : InvariantPositiveForm ρ)
    (hfin : ∀ v : V, FiniteVectors.IsFiniteVector ρ v) (v w : V) :
    (b.toKFiniteDual hfin v : Module.Dual ℂ V) w = b.inner v w := rfl

/-- The form map intertwines the compact action with its dual. -/
theorem toKFiniteDual_compact (b : InvariantPositiveForm ρ)
    (hfin : ∀ v : V, FiniteVectors.IsFiniteVector ρ v) (k : K) (v : V) :
    b.toKFiniteDual hfin (ρ k v) = kDualRep ρ k (b.toKFiniteDual hfin v) :=
  Subtype.ext (b.dual_rightFunctional k v).symm

/-- The form map is injective by definiteness. -/
theorem toKFiniteDual_injective (b : InvariantPositiveForm ρ)
    (hfin : ∀ v : V, FiniteVectors.IsFiniteVector ρ v) :
    Function.Injective (b.toKFiniteDual hfin) := by
  refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
  apply b.definite v
  simpa using congrArg (fun ℓ : kDual ρ => (ℓ : Module.Dual ℂ V) v) hv

end Langlands.InvariantPositiveForm

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.KFiniteDual Langlands.InvariantPositiveForm RealContragredient

universe uV

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V}
  (hgk : IsRealGKModule n ρ π) (b : InvariantPositiveForm ρ)
  (hb : ∀ (X : Matrix (Fin n) (Fin n) ℝ) (v w : V),
    b.inner (π (1 ⊗ₜ X) v) w + b.inner v (π (1 ⊗ₜ X) w) = 0)

include hb

/-- Skewness gives intertwining of the real Lie actions with the finite dual. -/
theorem realGK_toKFiniteDual_lie (X : Matrix (Fin n) (Fin n) ℝ) (v : V) :
    b.toKFiniteDual hgk.1 (π (1 ⊗ₜ X) v) =
      dualLie hgk (1 ⊗ₜ X) (b.toKFiniteDual hgk.1 v) := by
  apply Subtype.ext
  ext w
  rw [toKFiniteDual_apply_apply, dualLie_apply_apply, toKFiniteDual_apply_apply]
  exact eq_neg_of_add_eq_zero_left (hb X v w)

/-- The conjugate-linear positive-form map is onto the finite dual of an irreducible
admissible real module. -/
theorem realGK_toKFiniteDual_surjective
    (hirr : IsIrreducibleGKModule ρ π) (hadm : IsAdmissibleGKModule ρ) :
    Function.Surjective (b.toKFiniteDual hgk.1) := by
  let T := b.toKFiniteDual hgk.1
  have hK : ∀ k w, w ∈ LinearMap.range T → kDualRep ρ k w ∈ LinearMap.range T := by
    rintro k _ ⟨v, rfl⟩
    exact ⟨ρ k v, b.toKFiniteDual_compact hgk.1 k v⟩
  have hL : ∀ X w, w ∈ LinearMap.range T → dualLie hgk X w ∈ LinearMap.range T := by
    intro X
    induction X using TensorProduct.inductionOn with
    | tmul c X =>
      rintro _ ⟨v, rfl⟩
      have hc : c ⊗ₜ[ℝ] X = c • (1 ⊗ₜ[ℝ] X) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hc, map_smul, LinearMap.smul_apply]
      exact (LinearMap.range T).smul_mem c ⟨π (1 ⊗ₜ X) v, realGK_toKFiniteDual_lie hgk b hb X v⟩
    | add X Y hX hY =>
      intro w hw
      rw [map_add, LinearMap.add_apply]
      exact (LinearMap.range T).add_mem (hX w hw) (hY w hw)
  rcases (isIrreducible_kDual hgk hirr hadm).2 (LinearMap.range T) hK hL with hbot | htop
  · let := hirr.1
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hTv : T v ∈ LinearMap.range T := ⟨v, rfl⟩
    rw [hbot, Submodule.mem_bot] at hTv
    exact (hv (b.toKFiniteDual_injective hgk.1 (by simpa only [map_zero] using hTv))).elim
  · exact LinearMap.range_eq_top.1 htop

end Langlands.Archimedean
