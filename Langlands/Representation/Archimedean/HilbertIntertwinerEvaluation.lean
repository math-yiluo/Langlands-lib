import Langlands.Representation.Archimedean.GKModuleDensity
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-! # Evaluation of bounded Hilbert intertwiners -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 40000
set_option backward.isDefEq.respectTransparency false
open scoped Matrix

namespace Langlands.Archimedean

universe uG uK uE uH

section BoundedIntertwiners

variable {G : Type uG} [Group G]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℂ H]
  (π : G →* (E →L[ℂ] E)) (σ : G →* (H →L[ℂ] H))

/-- Bounded operators intertwining the two given actions, with their operator norm. -/
def boundedIntertwiners : Submodule ℂ (E →L[ℂ] H) where
  carrier := {T | ∀ g x, T (π g x) = σ g (T x)}
  zero_mem' := fun g x => by simp
  add_mem' := fun hT hS g x => by simp [hT g x, hS g x]
  smul_mem' := fun a T hT g x => by simp [hT g x]

theorem isClosed_boundedIntertwiners : IsClosed (boundedIntertwiners π σ : Set (E →L[ℂ] H)) := by
  change IsClosed {T : E →L[ℂ] H | ∀ g x, T (π g x) = σ g (T x)}
  rw [show {T : E →L[ℂ] H | ∀ g x, T (π g x) = σ g (T x)} =
      ⋂ g, ⋂ x, {T | T (π g x) = σ g (T x)} from by ext T; simp]
  refine isClosed_iInter fun g => isClosed_iInter fun x => isClosed_eq ?_ ?_
  · exact (ContinuousLinearMap.apply ℂ H (π g x)).continuous
  · exact (σ g).continuous.comp (ContinuousLinearMap.apply ℂ H x).continuous

/-- Evaluation of a bounded intertwiner at one vector as a bounded linear map. -/
def boundedIntertwinerEval (x : E) : boundedIntertwiners π σ →L[ℂ] H :=
  (ContinuousLinearMap.apply ℂ H x).comp (boundedIntertwiners π σ).subtypeL

@[simp] theorem boundedIntertwinerEval_apply (x : E) (T : boundedIntertwiners π σ) :
    boundedIntertwinerEval π σ x T = T.val x := rfl

end BoundedIntertwiners

section ScalarCommutant

variable {G : Type uG} [Group G]
  {K : Type uK} [Group K] [TopologicalSpace K] (i : K →* G)
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (π : G →* (E →L[ℂ] E))

private theorem exists_eigenvector_of_boundedIntertwiner
    (hcont : IsContinuousRepresentation (π.comp i))
    (hadm : IsAdmissibleGKModule (linearRepresentation (π.comp i)))
    {v : E} (hv : v ≠ 0) (hfin : FiniteVectors.IsFiniteVector (linearRepresentation (π.comp i)) v)
    (Z : boundedIntertwiners π π) :
    ∃ (c : ℂ) (x : E), x ≠ 0 ∧ Z.val x = c • x := by
  let ρ := linearRepresentation (π.comp i)
  let S := FiniteVectors.orbitSubrepresentation ρ v
  let W := S.toSubmodule
  let : FiniteDimensional ℂ W := hfin
  let d := Module.finrank ℂ W
  let b : Module.Basis (Fin d) ℂ W := Module.finBasis ℂ W
  have hW (k : K) (w : E) (hw : w ∈ W) : ρ k w ∈ W := S.apply_mem_toSubmodule k hw
  let τ := GKModuleDensity.matrixRep W hW b
  have hτ : Continuous τ := by
    refine continuous_matrix fun j l => ?_
    have hOrbit : Continuous (fun k : K => S.toRepresentation k (b l)) :=
      (hcont.comp (continuous_id.prodMk (continuous_const (y := (b l : E))))).subtype_mk _
    have h : Continuous (fun k : K => b.coord j (S.toRepresentation k (b l))) :=
      (b.coord j).continuous_of_finiteDimensional.comp hOrbit
    have he (k : K) : (ρ k).restrict (hW k) (b l) = S.toRepresentation k (b l) := rfl
    simpa only [τ, GKModuleDensity.matrixRep, MonoidHom.coe_mk, OneHom.coe_mk,
      LinearMap.toMatrix_apply, Module.Basis.coord_apply, he] using h
  let I := gkIntertwiners ρ d τ
  let : FiniteDimensional ℂ I := hadm d τ hτ
  let T₀ : I := ⟨GKModuleDensity.inclusion W b, GKModuleDensity.inclusion_mem W hW b⟩
  let y : W := ⟨v, FiniteVectors.self_mem_orbitSpan ρ v⟩
  have h₀ : T₀.val (b.equivFun y) = v := by
    change (b.equivFun.symm (b.equivFun y) : E) = v
    rw [LinearEquiv.symm_apply_apply]
  let : Nontrivial I := ⟨⟨T₀, 0, fun h => hv <| by
    rw [← h₀, h]
    rfl⟩⟩
  let Φ : Module.End ℂ I :=
    { toFun := fun T => ⟨Z.val.toLinearMap.comp T.val, fun k x => by
        change Z.val (T.val (τ k *ᵥ x)) = ρ k (Z.val (T.val x))
        rw [T.property k x]
        exact Z.property (i k) (T.val x)⟩
      map_add' := fun T U => Subtype.ext (LinearMap.ext fun x => by simp)
      map_smul' := fun a T => Subtype.ext (LinearMap.ext fun x => by simp) }
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue Φ
  obtain ⟨T, hT⟩ := hc.exists_hasEigenvector
  obtain ⟨z, hz⟩ : ∃ z, T.val z ≠ 0 := by
    by_contra! h
    exact hT.2 (Subtype.ext (LinearMap.ext h))
  exact ⟨c, T.val z, hz, congrArg (fun U : I => U.val z) hT.apply_eq_smul⟩

/-- A nonzero compact-finite vector in an admissible restriction supplies an
eigenvector for every bounded endomorphism in the commutant. Irreducibility
then makes its closed eigenspace the entire Hilbert representation. -/
theorem boundedIntertwiner_eq_smul_id
    (hcont : IsContinuousRepresentation (π.comp i))
    (hadm : IsAdmissibleGKModule (linearRepresentation (π.comp i)))
    {v : E} (hv : v ≠ 0) (hfin : FiniteVectors.IsFiniteVector (linearRepresentation (π.comp i)) v)
    (hirr : IsTopologicallyIrreducible π) (Z : boundedIntertwiners π π) :
    ∃ c : ℂ, Z.val = c • ContinuousLinearMap.id ℂ E := by
  obtain ⟨c, x, hx, hZx⟩ := exists_eigenvector_of_boundedIntertwiner i π hcont hadm hv hfin Z
  let L := Z.val - c • ContinuousLinearMap.id ℂ E
  have hmem (y : E) : y ∈ L.ker ↔ Z.val y = c • y := by
    change Z.val y - c • y = 0 ↔ _
    rw [sub_eq_zero]
  have hstable (g : G) (y : E) (hy : y ∈ L.ker) : π g y ∈ L.ker := by
    rw [hmem, Z.property g y, (hmem y).mp hy, map_smul]
  have hxL : x ∈ L.ker := (hmem x).mpr hZx
  have htop := (hirr.2 L.ker L.isClosed_ker hstable).resolve_left fun hb => by
    rw [hb, Submodule.mem_bot] at hxL
    exact hx hxL
  refine ⟨c, ContinuousLinearMap.ext fun y => (hmem y).mp ?_⟩
  rw [htop]
  exact Submodule.mem_top

end ScalarCommutant

section Evaluation

variable {G : Type uG} [Group G]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : G →* (E →L[ℂ] E)) (σ : G →* (H →L[ℂ] H))

omit [CompleteSpace E] in
private theorem inner_action_eq (A : G →* (E →L[ℂ] E))
    (hA : ∀ g x y, inner ℂ (A g x) (A g y) = inner ℂ x y) (g : G) (x y : E) :
    inner ℂ (A g x) y = inner ℂ x (A g⁻¹ y) := by
  have hinv : A g (A g⁻¹ y) = y := by
    change (A g * A g⁻¹) y = y
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  calc
    inner ℂ (A g x) y = inner ℂ (A g x) (A g (A g⁻¹ y)) :=
      congrArg (inner ℂ (A g x)) hinv.symm
    _ = inner ℂ x (A g⁻¹ y) := hA g x _

/-- The adjoint of a bounded intertwiner of unitary actions intertwines in reverse. -/
theorem adjoint_mem_boundedIntertwiners
    (hπ : ∀ g x y, inner ℂ (π g x) (π g y) = inner ℂ x y)
    (hσ : ∀ g x y, inner ℂ (σ g x) (σ g y) = inner ℂ x y)
    (T : boundedIntertwiners π σ) :
    T.val.adjoint ∈ boundedIntertwiners σ π := by
  intro g y
  apply ext_inner_left ℂ
  intro x
  calc
    inner ℂ x (T.val.adjoint (σ g y)) = inner ℂ (T.val x) (σ g y) :=
      T.val.adjoint_inner_right x _
    _ = inner ℂ (σ g⁻¹ (T.val x)) y := by
      simpa only [inv_inv] using (inner_action_eq σ hσ g⁻¹ (T.val x) y).symm
    _ = inner ℂ (T.val (π g⁻¹ x)) y := by rw [T.property g⁻¹ x]
    _ = inner ℂ (π g⁻¹ x) (T.val.adjoint y) := (T.val.adjoint_inner_right _ _).symm
    _ = inner ℂ x (π g (T.val.adjoint y)) := by
      simpa only [inv_inv] using inner_action_eq π hπ g⁻¹ x (T.val.adjoint y)

/-- Evaluation at a unit vector is a linear isometry when the source
commutant is scalar and both actions are unitary. -/
def boundedIntertwinerEvaluationIsometry
    (hπ : ∀ g x y, inner ℂ (π g x) (π g y) = inner ℂ x y)
    (hσ : ∀ g x y, inner ℂ (σ g x) (σ g y) = inner ℂ x y)
    (hscalar : ∀ Z : boundedIntertwiners π π, ∃ c : ℂ, Z.val = c • ContinuousLinearMap.id ℂ E)
    (x₀ : E) (h₀ : ‖x₀‖ = 1) : boundedIntertwiners π σ →ₗᵢ[ℂ] H where
  toLinearMap := (boundedIntertwinerEval π σ x₀).toLinearMap
  norm_map' T := by
    let A : boundedIntertwiners π π := ⟨T.val.adjoint.comp T.val, fun g x => by
      change T.val.adjoint (T.val (π g x)) = π g (T.val.adjoint (T.val x))
      rw [T.property g x]
      exact adjoint_mem_boundedIntertwiners π σ hπ hσ T g (T.val x)⟩
    obtain ⟨c, hc⟩ := hscalar A
    have hs : inner ℂ (T.val x₀) (T.val x₀) = c := by
      rw [← T.val.adjoint_inner_right]
      change inner ℂ x₀ (A.val x₀) = c
      rw [hc, smul_apply, ContinuousLinearMap.id_apply,
        inner_smul_right, inner_self_eq_norm_sq_to_K, h₀]
      simp
    have hnorm := congrArg norm hs
    rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm] at hnorm
    have hle : ‖T.val‖ * ‖T.val‖ ≤ ‖c‖ := by
      rw [← T.val.norm_adjoint_comp_self]
      change ‖A.val‖ ≤ ‖c‖
      rw [hc, norm_smul]
      exact mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le
    change ‖T.val x₀‖ = ‖T.val‖
    have hge : ‖T.val x₀‖ ≤ ‖T.val‖ := by
      simpa only [h₀, mul_one] using T.val.le_opNorm x₀
    exact le_antisymm hge (by nlinarith [norm_nonneg (T.val x₀), norm_nonneg T.val])

/-- Evaluation of the bounded intertwiner space has a bounded left inverse.
It is the inverse isometry on the evaluation range composed with orthogonal
projection onto that range. -/
theorem exists_boundedIntertwinerEval_leftInverse
    (hπ : ∀ g x y, inner ℂ (π g x) (π g y) = inner ℂ x y)
    (hσ : ∀ g x y, inner ℂ (σ g x) (σ g y) = inner ℂ x y)
    (hscalar : ∀ Z : boundedIntertwiners π π, ∃ c : ℂ, Z.val = c • ContinuousLinearMap.id ℂ E)
    (x₀ : E) (h₀ : ‖x₀‖ = 1) :
    ∃ L : H →L[ℂ] boundedIntertwiners π σ, ∀ T, L (T.val x₀) = T := by
  let : CompleteSpace (boundedIntertwiners π σ) :=
    (isClosed_boundedIntertwiners π σ).completeSpace_coe
  let J := boundedIntertwinerEvaluationIsometry π σ hπ hσ hscalar x₀ h₀
  let R := LinearMap.range J.toLinearMap
  let : CompleteSpace R := J.isometry.isUniformInducing.isComplete_range.completeSpace_coe
  let L := J.equivRange.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    R.orthogonalProjectionOnto
  refine ⟨L, fun T => ?_⟩
  have he : R.orthogonalProjectionOnto (T.val x₀) = J.equivRange T :=
    Subtype.ext (R.starProjection_eq_self_iff.mpr ⟨T, rfl⟩)
  change J.equivRange.symm (R.orthogonalProjectionOnto (T.val x₀)) = T
  rw [he, LinearIsometryEquiv.symm_apply_apply]

end Evaluation

/-- For an irreducible unitary Hilbert representation with an admissible
restriction containing a nonzero finite vector, evaluation at a unit vector
recovers bounded intertwiners into any unitary Hilbert representation. -/
def HilbertIntertwinerEvaluationStatement : Prop :=
  ∀ (G : Type uG) [Group G]
    (K : Type uK) [Group K] [TopologicalSpace K] (i : K →* G)
    (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : G →* (E →L[ℂ] E)) (σ : G →* (H →L[ℂ] H)),
    IsContinuousRepresentation (π.comp i) →
    IsAdmissibleGKModule (linearRepresentation (π.comp i)) →
    (∃ v : E, v ≠ 0 ∧ FiniteVectors.IsFiniteVector (linearRepresentation (π.comp i)) v) →
    IsTopologicallyIrreducible π →
    (∀ g x y, inner ℂ (π g x) (π g y) = inner ℂ x y) →
    (∀ g x y, inner ℂ (σ g x) (σ g y) = inner ℂ x y) →
    ∀ x₀ : E, ‖x₀‖ = 1 →
      ∃ L : H →L[ℂ] boundedIntertwiners π σ, ∀ T, L (T.val x₀) = T

theorem hilbertIntertwinerEvaluation : HilbertIntertwinerEvaluationStatement.{uG,uK,uE,uH} := by
  intro G _ K _ _ i E _ _ _ H _ _ _ π σ hcont hadm ⟨v, hv, hfin⟩ hirr hπ hσ x₀ h₀
  exact exists_boundedIntertwinerEval_leftInverse π σ hπ hσ
    (boundedIntertwiner_eq_smul_id i π hcont hadm hv hfin hirr) x₀ h₀

end Langlands.Archimedean
