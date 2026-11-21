import Langlands.Representation.Archimedean.SmoothLieActionUnits
import Langlands.Representation.Archimedean.SmoothFiniteActionUnits
import Langlands.Representation.Archimedean.SmoothKFiniteAdmissibility
import Langlands.Representation.Archimedean.PrincipalSeriesGKModule

/-! # The real `(𝔤, K)`-module of genuine compact-finite smooth vectors -/

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.Analysis (hasDerivAt_iff_tendsto_slope_tvs)

/-- A curve in a finite-dimensional subspace of a Hausdorff topological vector space, with a
derivative in the ambient space, is differentiated by every linear functional. -/
theorem hasDerivAt_apply_of_mem_finiteDimensional {D : Type*} [AddCommGroup D] [Module ℂ D]
    [Module ℝ D] [IsScalarTower ℝ ℂ D] [TopologicalSpace D] [IsTopologicalAddGroup D]
    [ContinuousSMul ℂ D] [ContinuousSMul ℝ D] [T2Space D]
    (P : Submodule ℂ D) [FiniteDimensional ℂ P] (g : D →ₗ[ℂ] ℂ) {f : ℝ → D} {f' : D}
    (hf : ∀ t, f t ∈ P) (hf' : f' ∈ P) (hd : HasDerivAt f f' 0) :
    HasDerivAt (fun t => g (f t)) (g f') 0 := by
  let L : P →ₗ[ℂ] ℂ := g.comp P.subtype
  have hL : Continuous L := LinearMap.continuous_of_finiteDimensional L
  have hmem (t : ℝ) : slope f 0 t ∈ P := by
    rw [slope_def_module]
    exact P.smul_of_tower_mem _ (P.sub_mem (hf t) (hf 0))
  have hsP : Tendsto (fun t => (⟨slope f 0 t, hmem t⟩ : P)) (𝓝[≠] 0) (𝓝 ⟨f', hf'⟩) :=
    tendsto_subtype_rng.mpr (hasDerivAt_iff_tendsto_slope_tvs.mp hd)
  apply hasDerivAt_iff_tendsto_slope_tvs.mpr
  refine ((hL.tendsto _).comp hsP).congr fun t => ?_
  simp only [Function.comp_apply, L, LinearMap.comp_apply, Submodule.subtype_apply,
    slope_def_module, map_sub, LinearMap.map_smul_of_tower]

namespace RealSmoothGK

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (R : Langlands.GeneralLinear n ℝ →* (E →L[ℂ] E))

/-- Genuine derivatives on compact-finite smooth vectors, real linear in the direction. -/
def realDerivative : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Module.End ℂ (smoothKFinite ℝ n R) where
  toFun X := DerivativeSmoothVectors.finiteVectorsOperator R Unitary.toUnits X
  map_add' X Y := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun (map_add (DerivativeSmoothVectors.operatorDirection R) X Y) v.val
  map_smul' c X := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun (map_smul (DerivativeSmoothVectors.operatorDirection R) c X) v.val

theorem coe_realDerivative (X : Matrix (Fin n) (Fin n) ℝ) (v : smoothKFinite ℝ n R) :
    ((realDerivative n R X v : smoothKFinite ℝ n R) :
        DerivativeSmoothVectors (matrixModel ℝ n) R) =
      DerivativeSmoothVectors.operator (matrixModel ℝ n) R X v := rfl

theorem realDerivative_commutator (hR : IsContinuousRepresentation R)
    (X Y : Matrix (Fin n) (Fin n) ℝ) :
    realDerivative n R (X * Y - Y * X) =
      realDerivative n R X * realDerivative n R Y - realDerivative n R Y * realDerivative n R X := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact DerivativeSmoothVectors.operator_commutator_units R hR X Y v.val

/-- The complex-linear extension `z ⊗ X ↦ z • dR(X)`. -/
def complexDerivative :
    (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ[ℂ] Module.End ℂ (smoothKFinite ℝ n R) :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℂ _ (realDerivative n R))

theorem complexDerivative_tmul (z : ℂ) (X : Matrix (Fin n) (Fin n) ℝ) :
    complexDerivative n R (z ⊗ₜ X) = z • realDerivative n R X := by
  simp [complexDerivative]

/-- The complexified genuine derivative action on compact-finite smooth vectors. -/
def lieAction (hR : IsContinuousRepresentation R) :
    (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ (smoothKFinite ℝ n R) :=
  { complexDerivative n R with
    map_lie' := by
      intro x y
      rw [LinearMap.toFun_eq_coe]
      induction x using TensorProduct.inductionOn with
      | add x₁ x₂ h₁ h₂ =>
        simp only [LieRing.of_associative_ring_bracket] at h₁ h₂ ⊢
        erw [add_lie x₁ x₂ y]
        rw [map_add, h₁, h₂, map_add, add_mul, mul_add]
        abel
      | tmul z X =>
        induction y using TensorProduct.inductionOn with
        | add y₁ y₂ h₁ h₂ =>
          simp only [LieRing.of_associative_ring_bracket] at h₁ h₂ ⊢
          erw [lie_add]
          rw [map_add, h₁, h₂, map_add, add_mul, mul_add]
          abel
        | tmul w Y =>
          rw [LieAlgebra.ExtendScalars.bracket_tmul, complexDerivative_tmul,
            complexDerivative_tmul, complexDerivative_tmul]
          simp only [LieRing.of_associative_ring_bracket]
          rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm w z,
            realDerivative_commutator n R hR]
          exact smul_sub (z * w) (realDerivative n R X * realDerivative n R Y)
            (realDerivative n R Y * realDerivative n R X) }

theorem lieAction_one_tmul (hR : IsContinuousRepresentation R) (X : Matrix (Fin n) (Fin n) ℝ)
    (v : smoothKFinite ℝ n R) :
    ((lieAction n R hR ((1 : ℂ) ⊗ₜ X) v : smoothKFinite ℝ n R) :
        DerivativeSmoothVectors (matrixModel ℝ n) R) =
      DerivativeSmoothVectors.operator (matrixModel ℝ n) R X v := by
  change ((complexDerivative n R ((1 : ℂ) ⊗ₜ X) v : smoothKFinite ℝ n R) :
    DerivativeSmoothVectors (matrixModel ℝ n) R) = _
  rw [complexDerivative_tmul, one_smul]
  rfl

/-- The inclusion intertwines the compact actions and the derivative actions. -/
theorem isSmoothGKIntertwiner (hR : IsContinuousRepresentation R) :
    IsSmoothGKIntertwiner ℝ n R (smoothKFiniteRepresentation ℝ n R) (lieAction n R hR)
      (smoothKFinite ℝ n R).subtype :=
  ⟨fun _ _ => rfl, fun X v => lieAction_one_tmul n R hR X v⟩

/-- The genuine compact-finite smooth vectors form a real `(𝔤, K)`-module. -/
theorem isRealGKModule (hR : IsContinuousRepresentation R) :
    IsRealGKModule n (smoothKFiniteRepresentation ℝ n R) (lieAction n R hR) := by
  let ρ0 := (DerivativeSmoothVectors.representation (matrixModel ℝ n) R).comp
    (Unitary.toUnits : Matrix.unitaryGroup (Fin n) ℝ →* Langlands.GeneralLinear n ℝ)
  let ρ := smoothKFiniteRepresentation ℝ n R
  have hfin : ∀ v : smoothKFinite ℝ n R, FiniteVectors.IsFiniteVector ρ v := fun v =>
    (FiniteVectors.isFiniteVector_map_iff (FiniteVectors.inclusion ρ0)
      (FiniteVectors.inclusion_injective ρ0) v).mp v.prop
  refine ⟨hfin, ?_, ?_, ?_⟩
  · intro v ℓ
    obtain ⟨g, hg⟩ := LinearMap.exists_extend ℓ
    let O := FiniteVectors.orbitSpan ρ v
    have : FiniteDimensional ℂ O := hfin v
    let P := O.map (smoothKFinite ℝ n R).subtype
    have : FiniteDimensional ℂ P := by dsimp only [P]; infer_instance
    let L : P →ₗ[ℂ] ℂ := g.comp P.subtype
    have hL : Continuous L := LinearMap.continuous_of_finiteDimensional L
    have horb : Continuous (fun k : Matrix.unitaryGroup (Fin n) ℝ =>
        (⟨((ρ k v : smoothKFinite ℝ n R) : DerivativeSmoothVectors (matrixModel ℝ n) R),
          ⟨ρ k v, FiniteVectors.action_mem_orbitSpan ρ k v, rfl⟩⟩ : P)) := by
      refine Continuous.subtype_mk ?_ _
      exact (DerivativeSmoothVectors.continuous_representation_units R hR).comp
        ((continuous_unitary_toUnits (N := n) (F := ℝ)).prodMk continuous_const)
    refine (hL.comp horb).congr fun k => ?_
    exact LinearMap.congr_fun hg (ρ k v)
  · intro γ X hγ0 hγ v ℓ
    let c : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t => (γ t : Matrix (Fin n) (Fin n) ℝ)
    have hc : HasDerivAt c X 0 := hasDerivAt_matrix_of_entries (N := n) (F := ℝ) hγ
    have hc0 : c 0 = ((1 : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) := by
      simp [c, hγ0]
    have horb := DerivativeSmoothVectors.hasDerivAt_unitsChartOrbit R hR 1
      (v : DerivativeSmoothVectors (matrixModel ℝ n) R) hc hc0
    simp only [inv_one, Units.val_one, one_mul, map_one, Module.End.one_apply] at horb
    have hfun : (fun u => DerivativeSmoothVectors.unitsChartAction R (c u,
        (v : DerivativeSmoothVectors (matrixModel ℝ n) R))) =
        fun u => ((ρ (γ u) v : smoothKFinite ℝ n R) :
          DerivativeSmoothVectors (matrixModel ℝ n) R) :=
      funext fun u => DerivativeSmoothVectors.unitsChartAction_val R (Unitary.toUnits (γ u)) _
    rw [hfun] at horb
    obtain ⟨g, hg⟩ := LinearMap.exists_extend ℓ
    have hgu (u : smoothKFinite ℝ n R) : g u = ℓ u := LinearMap.congr_fun hg u
    let O := FiniteVectors.orbitSpan ρ v
    have : FiniteDimensional ℂ O := hfin v
    let P := (O ⊔ ℂ ∙ (lieAction n R hR ((1 : ℂ) ⊗ₜ X) v)).map (smoothKFinite ℝ n R).subtype
    have : FiniteDimensional ℂ P := by dsimp only [P]; infer_instance
    have hf (t : ℝ) : ((ρ (γ t) v : smoothKFinite ℝ n R) :
        DerivativeSmoothVectors (matrixModel ℝ n) R) ∈ P :=
      ⟨ρ (γ t) v, Submodule.mem_sup_left (FiniteVectors.action_mem_orbitSpan ρ (γ t) v), rfl⟩
    have hf' : DerivativeSmoothVectors.operator (matrixModel ℝ n) R X v ∈ P :=
      ⟨_, Submodule.mem_sup_right (Submodule.mem_span_singleton_self _),
        lieAction_one_tmul n R hR X v⟩
    have h := hasDerivAt_apply_of_mem_finiteDimensional P g hf hf' horb
    rw [← lieAction_one_tmul n R hR X v] at h
    simpa only [hgu] using h
  · intro k X v
    apply Subtype.ext
    change DerivativeSmoothVectors.representation (matrixModel ℝ n) R (Unitary.toUnits k)
        ((lieAction n R hR ((1 : ℂ) ⊗ₜ X) v : smoothKFinite ℝ n R) :
          DerivativeSmoothVectors (matrixModel ℝ n) R) =
      ((lieAction n R hR ((1 : ℂ) ⊗ₜ ((k : Matrix (Fin n) (Fin n) ℝ) * X *
        (star k : Matrix (Fin n) (Fin n) ℝ))) (ρ k v) : smoothKFinite ℝ n R) :
          DerivativeSmoothVectors (matrixModel ℝ n) R)
    rw [lieAction_one_tmul, lieAction_one_tmul]
    change _ = DerivativeSmoothVectors.operator (matrixModel ℝ n) R _
      (DerivativeSmoothVectors.representation (matrixModel ℝ n) R (Unitary.toUnits k) (v : _))
    have hk : star (k : Matrix (Fin n) (Fin n) ℝ) * (k : Matrix (Fin n) (Fin n) ℝ) = 1 :=
      Unitary.star_mul_self_of_mem k.prop
    have hX : DerivativeSmoothVectors.inverseConjugationCLM (Unitary.toUnits k)
        ((k : Matrix (Fin n) (Fin n) ℝ) * X * star (k : Matrix (Fin n) (Fin n) ℝ)) = X := by
      rw [DerivativeSmoothVectors.inverseConjugationCLM_apply]
      change star (k : Matrix (Fin n) (Fin n) ℝ) *
        ((k : Matrix (Fin n) (Fin n) ℝ) * X * star (k : Matrix (Fin n) (Fin n) ℝ)) *
          (k : Matrix (Fin n) (Fin n) ℝ) = X
      rw [← mul_assoc, ← mul_assoc, hk, one_mul, mul_assoc, hk, mul_one]
    rw [DerivativeSmoothVectors.operator_representation_units, hX]

end RealSmoothGK

end Langlands.Archimedean
