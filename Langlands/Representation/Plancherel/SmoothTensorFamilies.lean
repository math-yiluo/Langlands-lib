import Langlands.Representation.Plancherel.RationalOrbitSmoothFunctions
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RepresentationTheory.Invariants

/-! # Finite smooth families and diagonal tensor invariants -/

noncomputable section

open scoped TensorProduct ContDiff

namespace Langlands.Plancherel

universe uJ uV uS

variable (J : Type uJ) [Fintype J]

/-- Scalar smooth functions on the finite torus, with pointwise operations. -/
def smoothFiniteTorusFunctions : Subalgebra ℂ ((J → Circle) → ℂ) where
  carrier := {f | IsSmoothFiniteTorusFunction f}
  algebraMap_mem' c := by
    change ContDiff ℝ ∞ (fun _ => c)
    exact contDiff_const
  zero_mem' := by
    change ContDiff ℝ ∞ (fun _ => (0 : ℂ))
    exact contDiff_const
  one_mem' := by
    change ContDiff ℝ ∞ (fun _ => (1 : ℂ))
    exact contDiff_const
  add_mem' hf hg := by
    change ContDiff ℝ ∞ _ at hf hg ⊢
    exact hf.add hg
  mul_mem' hf hg := by
    change ContDiff ℝ ∞ _ at hf hg ⊢
    exact hf.mul hg

variable (V : Type uV) [AddCommGroup V] [Module ℂ V]

local instance smoothTensorAddCommGroup :
    AddCommGroup (smoothFiniteTorusFunctions J ⊗[ℂ] V) :=
  TensorProduct.addCommGroup

/-- Actual evaluation of a scalar-function tensor on the torus. No topology on
the coefficient module is required. -/
def smoothTensorEvaluation :
    smoothFiniteTorusFunctions J ⊗[ℂ] V →ₗ[ℂ] ((J → Circle) → V) :=
  TensorProduct.lift
    { toFun := fun f =>
        { toFun := fun v z => f.val z • v
          map_add' := by intros; funext z; exact smul_add _ _ _
          map_smul' := by intros; funext z; exact smul_comm _ _ _ }
      map_add' := by intros; ext v z; exact add_smul _ _ _
      map_smul' := by
        intro c f
        apply LinearMap.ext
        intro v
        funext z
        exact (smul_smul c (f.val z) v).symm }

@[simp]
theorem smoothTensorEvaluation_tmul (f : smoothFiniteTorusFunctions J) (v : V)
    (z : J → Circle) :
    smoothTensorEvaluation J V (f ⊗ₜ[ℂ] v) z = f.val z • v := rfl

/-- Evaluation determines every scalar coefficient in an arbitrary basis. -/
theorem smoothTensorEvaluation_basisCoord {B : Type*} [DecidableEq B]
    (b : Module.Basis B ℂ V) (t : smoothFiniteTorusFunctions J ⊗[ℂ] V)
    (i : B) (z : J → Circle) :
    (TensorProduct.equivFinsuppOfBasisRight b t i).val z =
      b.coord i (smoothTensorEvaluation J V t z) := by
  induction t using TensorProduct.inductionOn with
  | tmul f v =>
      simp [Module.Basis.coord_apply, mul_comm]
  | add t u ht hu =>
      simp only [map_add, Finsupp.add_apply, Subalgebra.coe_add, Pi.add_apply, ht, hu]

/-- Algebraic tensor evaluation is faithful even for infinite-dimensional
coefficient modules. -/
theorem smoothTensorEvaluation_injective :
    Function.Injective (smoothTensorEvaluation J V) := by
  classical
  let b := Module.Free.chooseBasis ℂ V
  intro t u h
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  apply Finsupp.ext
  intro i
  apply Subtype.ext
  funext z
  rw [smoothTensorEvaluation_basisCoord, smoothTensorEvaluation_basisCoord, h]

/-- Finite smooth families are the actual submodule spanned by functions
`z ↦ f(z) • v`, with smooth scalar `f` and a fixed vector `v`. -/
def finiteSmoothFamilies : Submodule ℂ ((J → Circle) → V) :=
  Submodule.span ℂ {F | ∃ (f : smoothFiniteTorusFunctions J) (v : V),
    F = fun z => f.val z • v}

theorem range_smoothTensorEvaluation :
    (smoothTensorEvaluation J V).range = finiteSmoothFamilies J V := by
  apply le_antisymm
  · rintro F ⟨t, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul f v =>
        exact Submodule.subset_span ⟨f, v, rfl⟩
    | add t u ht hu =>
        simpa only [map_add] using (finiteSmoothFamilies J V).add_mem ht hu
  · apply Submodule.span_le.mpr
    rintro F ⟨f, v, rfl⟩
    exact ⟨f ⊗ₜ[ℂ] v, rfl⟩

/-- Concrete finite-sum characterization, with no bound on the coefficient
dimension or choice of coefficient topology. -/
theorem mem_finiteSmoothFamilies_iff (F : (J → Circle) → V) :
    F ∈ finiteSmoothFamilies J V ↔
      ∃ (n : ℕ) (f : Fin n → smoothFiniteTorusFunctions J) (v : Fin n → V),
        ∀ z, F z = ∑ i, (f i).val z • v i := by
  rw [← range_smoothTensorEvaluation]
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨n, f, v, ht⟩ := TensorProduct.exists_sum_tmul_eq t
    refine ⟨n, f, v, ?_⟩
    intro z
    rw [ht, map_sum]
    simp
  · rintro ⟨n, f, v, hF⟩
    refine ⟨∑ i, f i ⊗ₜ[ℂ] v i, ?_⟩
    funext z
    simpa using (hF z).symm

/-- The algebraic smooth tensor is the space of actual finite smooth families. -/
def smoothTensorFamilyEquiv :
    smoothFiniteTorusFunctions J ⊗[ℂ] V ≃ₗ[ℂ] finiteSmoothFamilies J V :=
  (LinearEquiv.ofInjective (smoothTensorEvaluation J V)
    (smoothTensorEvaluation_injective J V)).trans
      (LinearEquiv.ofEq _ _ (range_smoothTensorEvaluation J V))

@[simp]
theorem smoothTensorFamilyEquiv_apply (t : smoothFiniteTorusFunctions J ⊗[ℂ] V)
    (z : J → Circle) :
    (smoothTensorFamilyEquiv J V t).val z = smoothTensorEvaluation J V t z := rfl

variable {S : Type uS} [Group S] (τ : S →* (J → Circle))
  (ρ : Representation ℂ S V)

/-- Translation acts by inverse parameter translation, so diagonal invariance
has covariance `F(z * τ(s)) = ρ(s)(F(z))`. -/
def smoothTorusTranslation : Representation ℂ S (smoothFiniteTorusFunctions J) where
  toFun s :=
    { toFun := fun f => ⟨fun z => f.val (z * (τ s)⁻¹),
        (isSmoothFiniteTorusFunction_mul_const_iff _ _).mpr f.property⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f z; simp
  map_mul' s t := by ext f z; simp [mul_assoc, mul_comm]

@[simp]
theorem smoothTorusTranslation_apply (s : S) (f : smoothFiniteTorusFunctions J)
    (z : J → Circle) :
    (smoothTorusTranslation J τ s f).val z = f.val (z * (τ s)⁻¹) := rfl

/-- The diagonal action retains the supplied, possibly nontrivial, coefficient
representation. -/
def smoothTensorRepresentation :
    Representation ℂ S (smoothFiniteTorusFunctions J ⊗[ℂ] V) :=
  (smoothTorusTranslation J τ).tprod ρ

theorem smoothTensorEvaluation_action (s : S)
    (t : smoothFiniteTorusFunctions J ⊗[ℂ] V) (z : J → Circle) :
    smoothTensorEvaluation J V (smoothTensorRepresentation J V τ ρ s t) z =
      ρ s (smoothTensorEvaluation J V t (z * (τ s)⁻¹)) := by
  induction t using TensorProduct.inductionOn with
  | tmul f v => simp [smoothTensorRepresentation, Representation.tprod_apply]
  | add t u ht hu => simp only [map_add, Pi.add_apply, ht, hu]

theorem mem_smoothTensorInvariants_iff (t : smoothFiniteTorusFunctions J ⊗[ℂ] V) :
    t ∈ (smoothTensorRepresentation J V τ ρ).invariants ↔
      ∀ (s : S) (z : J → Circle),
        smoothTensorEvaluation J V t (z * τ s) =
          ρ s (smoothTensorEvaluation J V t z) := by
  constructor
  · intro ht s z
    have h := congrArg (fun u => smoothTensorEvaluation J V u (z * τ s)) (ht s)
    rw [smoothTensorEvaluation_action] at h
    simpa only [mul_inv_cancel_right] using h.symm
  · intro ht s
    apply smoothTensorEvaluation_injective J V
    funext z
    rw [smoothTensorEvaluation_action]
    simpa only [inv_mul_cancel_right] using (ht s (z * (τ s)⁻¹)).symm

/-- Actual finite smooth families satisfying the coefficient covariance law. -/
def finiteSmoothEquivariantFamilies : Submodule ℂ ((J → Circle) → V) where
  carrier := {F | F ∈ finiteSmoothFamilies J V ∧
    ∀ (s : S) (z : J → Circle), F (z * τ s) = ρ s (F z)}
  zero_mem' := ⟨(finiteSmoothFamilies J V).zero_mem, by intros; simp⟩
  add_mem' hF hH := ⟨(finiteSmoothFamilies J V).add_mem hF.1 hH.1, by
    intro s z
    simp only [Pi.add_apply, map_add, hF.2 s z, hH.2 s z]⟩
  smul_mem' c F hF := ⟨(finiteSmoothFamilies J V).smul_mem c hF.1, by
    intro s z
    simp only [Pi.smul_apply, map_smul, hF.2 s z]⟩

/-- Evaluation restricted to the diagonal invariant subspace. -/
def smoothTensorInvariantEvaluation :
    (smoothTensorRepresentation J V τ ρ).invariants →ₗ[ℂ]
      finiteSmoothEquivariantFamilies J V τ ρ :=
  ((smoothTensorEvaluation J V).comp
    (smoothTensorRepresentation J V τ ρ).invariants.subtype).codRestrict _ fun t =>
      ⟨by rw [← range_smoothTensorEvaluation]; exact ⟨t.val, rfl⟩,
        (mem_smoothTensorInvariants_iff J V τ ρ t.val).mp t.property⟩

theorem smoothTensorInvariantEvaluation_bijective :
    Function.Bijective (smoothTensorInvariantEvaluation J V τ ρ) := by
  constructor
  · intro t u h
    apply Subtype.ext
    apply smoothTensorEvaluation_injective J V
    exact congrArg Subtype.val h
  · intro F
    have hF : F.val ∈ (smoothTensorEvaluation J V).range := by
      rw [range_smoothTensorEvaluation]
      exact F.property.1
    obtain ⟨t, ht⟩ := hF
    refine ⟨⟨t, (mem_smoothTensorInvariants_iff J V τ ρ t).mpr ?_⟩, ?_⟩
    · intro s z
      rw [ht]
      exact F.property.2 s z
    · exact Subtype.ext ht

/-- Concrete finite smooth equivariant functions are precisely the diagonal
invariant scalar-function tensors. No finiteness assumption on `S` is used. -/
def smoothTensorInvariantFamilyEquiv :
    (smoothTensorRepresentation J V τ ρ).invariants ≃ₗ[ℂ]
      finiteSmoothEquivariantFamilies J V τ ρ :=
  LinearEquiv.ofBijective (smoothTensorInvariantEvaluation J V τ ρ)
    (smoothTensorInvariantEvaluation_bijective J V τ ρ)

@[simp]
theorem smoothTensorInvariantFamilyEquiv_apply
    (t : (smoothTensorRepresentation J V τ ρ).invariants) (z : J → Circle) :
    (smoothTensorInvariantFamilyEquiv J V τ ρ t).val z =
      smoothTensorEvaluation J V t.val z := rfl

@[simp]
theorem smoothTensorInvariantFamilyEquiv_symm_evaluation
    (F : finiteSmoothEquivariantFamilies J V τ ρ) (z : J → Circle) :
    smoothTensorEvaluation J V
        ((smoothTensorInvariantFamilyEquiv J V τ ρ).symm F).val z = F.val z := by
  exact congrArg (fun H => H.val z)
    ((smoothTensorInvariantFamilyEquiv J V τ ρ).apply_symm_apply F)

end Langlands.Plancherel
