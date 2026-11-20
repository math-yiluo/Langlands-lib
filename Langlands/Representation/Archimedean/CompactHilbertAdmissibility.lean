import Langlands.Representation.KFiniteDual
import Langlands.Representation.Unitary.CompactIsometricAverage
import Mathlib.Analysis.Convex.Integral

/-! # Compact admissibility and recovery in a dense completion -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false

namespace Langlands.Archimedean

open MeasureTheory
open scoped Matrix

universe uK uV uE

variable {K : Type uK} [Group K] [TopologicalSpace K]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Postcomposition by the original compact-equivariant embedding. -/
def compactIntertwinerMap (κ : Representation ℂ K V) (π : K →* (E →L[ℂ] E))
    (j : V →ₗ[ℂ] E) (hj : ∀ k x, j (κ k x) = π k (j x))
    {d : ℕ} (τ : K →* Matrix (Fin d) (Fin d) ℂ) :
    gkIntertwiners κ d τ →ₗ[ℂ] gkIntertwiners (linearRepresentation π) d τ where
  toFun T := ⟨j.comp T.val, fun k x => by
    change j (T.val (τ k *ᵥ x)) = π k (j (T.val x))
    rw [T.property k x, hj]⟩
  map_add' T U := by
    apply Subtype.ext
    exact LinearMap.ext fun x => j.map_add (T.val x) (U.val x)
  map_smul' c T := by
    apply Subtype.ext
    exact LinearMap.ext fun x => j.map_smul c (T.val x)

section Average

variable [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [SecondCountableTopology K]
  (π : K →* (E →L[ℂ] E)) (hπ : IsContinuousRepresentation π)
  {d : ℕ} (τ : K →* Matrix (Fin d) (Fin d) ℂ) (hτ : Continuous τ)

local notation "ν" => Langlands.Analysis.compactProbabilityHaar K
local notation "D" => (Fin d → ℂ)
local notation "basis" => (Pi.basisFun ℂ (Fin d))

include hπ hτ

omit [CompleteSpace E] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    [SecondCountableTopology K] in
private theorem continuous_conjugate (T : D →ₗ[ℂ] E) (x : D) :
    Continuous (fun k : K => π k (T (τ k⁻¹ *ᵥ x))) := by
  have hx : Continuous (fun k : K => τ k⁻¹ *ᵥ x) :=
    (hτ.comp continuous_inv).matrix_mulVec continuous_const
  exact Continuous.comp hπ (continuous_id.prodMk (T.continuous_of_finiteDimensional.comp hx))

omit [CompleteSpace E] [SecondCountableTopology K] in
private theorem integrable_conjugate (T : D →ₗ[ℂ] E) (x : D) :
    Integrable (fun k : K => π k (T (τ k⁻¹ *ᵥ x))) ν :=
  (continuous_conjugate π hπ τ hτ T x).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private def averageMap (T : D →ₗ[ℂ] E) : D →ₗ[ℂ] E where
  toFun x := ∫ k : K, π k (T (τ k⁻¹ *ᵥ x)) ∂ν
  map_add' x y := by
    simp only [Matrix.mulVec_add, map_add]
    exact integral_add (integrable_conjugate π hπ τ hτ T x)
      (integrable_conjugate π hπ τ hτ T y)
  map_smul' c x := by
    simp only [Matrix.mulVec_smul, map_smul, RingHom.id_apply]
    exact integral_smul c _

omit [SecondCountableTopology K] in
private theorem averageMap_intertwines (T : D →ₗ[ℂ] E) (h : K) (x : D) :
    averageMap π hπ τ hτ T (τ h *ᵥ x) = π h (averageMap π hπ τ hτ T x) := by
  change (∫ k : K, π k (T (τ k⁻¹ *ᵥ (τ h *ᵥ x))) ∂ν) =
    π h (∫ k : K, π k (T (τ k⁻¹ *ᵥ x)) ∂ν)
  rw [← (π h).integral_comp_comm (integrable_conjugate π hπ τ hτ T x)]
  rw [← integral_mul_left_eq_self (μ := ν)
    (fun k : K => π k (T (τ k⁻¹ *ᵥ (τ h *ᵥ x)))) h]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro k
  change π (h * k) (T (τ (h * k)⁻¹ *ᵥ (τ h *ᵥ x))) = π h (π k (T (τ k⁻¹ *ᵥ x)))
  rw [Matrix.mulVec_mulVec, ← τ.map_mul, mul_inv_rev, inv_mul_cancel_right, π.map_mul]
  rfl

omit [SecondCountableTopology K] in
private theorem averageMap_eq_of_intertwines
    (T : gkIntertwiners (linearRepresentation π) d τ) :
    averageMap π hπ τ hτ T.val = T.val := by
  apply LinearMap.ext
  intro x
  change (∫ k : K, π k (T.val (τ k⁻¹ *ᵥ x)) ∂ν) = T.val x
  have h (k : K) : π k (T.val (τ k⁻¹ *ᵥ x)) = T.val x := by
    rw [T.property k⁻¹ x]
    change (π k * π k⁻¹) (T.val x) = T.val x
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  simp only [h, integral_const, probReal_univ, one_smul]

private theorem averageMap_continuous_columns (hnorm : ∀ k x, ‖π k x‖ = ‖x‖) (x : D) :
    Continuous (fun w : Fin d → E => averageMap π hπ τ hτ ((basis).constr ℂ w) x) := by
  let f (i : Fin d) (k : K) := (τ k⁻¹ *ᵥ x) i
  have hτx : Continuous (fun k : K => τ k⁻¹ *ᵥ x) :=
    (hτ.comp continuous_inv).matrix_mulVec continuous_const
  have hf (i : Fin d) : Integrable (f i) ν :=
    ((continuous_apply i).comp hτx).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hmeas (z : E) : AEStronglyMeasurable (fun k : K => π k z) ν :=
    Langlands.Analysis.compactIsometricOrbit_aestronglyMeasurable K π
      (fun y => Continuous.comp hπ (continuous_id.prodMk (continuous_const (y := y)))) z
  let A (i : Fin d) := Langlands.Analysis.integratedIsometricAction ν π hnorm hmeas (f i) (hf i)
  have heq (w : Fin d → E) :
      averageMap π hπ τ hτ ((basis).constr ℂ w) x = ∑ i, A i (w i) := by
    change (∫ k : K, π k (((basis).constr ℂ w) (τ k⁻¹ *ᵥ x)) ∂ν) = _
    simp only [Module.Basis.constr_apply_fintype, Pi.basisFun_equivFun, LinearEquiv.refl_apply,
      map_sum, map_smul]
    exact integral_finsetSum Finset.univ (fun i _ =>
      Langlands.Analysis.isometricActionIntegrand_integrable ν π hnorm hmeas (f i) (hf i) (w i))
  simp_rw [heq]
  exact continuous_finsetSum _ (fun i _ => (A i).continuous.comp (continuous_apply i))

omit [SecondCountableTopology K] in
private theorem averageMap_lifts (κ : Representation ℂ K V) (j : V →ₗ[ℂ] E)
    (hj : ∀ k x, j (κ k x) = π k (j x)) (hinj : Function.Injective j)
    (hfin : ∀ x, FiniteVectors.IsFiniteVector κ x) (v : Fin d → V) :
    ∃ L : gkIntertwiners κ d τ,
      j.comp L.val = averageMap π hπ τ hτ ((basis).constr ℂ (j ∘ v)) := by
  let W : Submodule ℂ E := ⨆ i, (FiniteVectors.orbitSpan κ (v i)).map j
  have (i : Fin d) : FiniteDimensional ℂ (FiniteVectors.orbitSpan κ (v i)) := hfin (v i)
  have : FiniteDimensional ℂ W := inferInstanceAs (FiniteDimensional ℂ
    (⨆ i, (FiniteVectors.orbitSpan κ (v i)).map j : Submodule ℂ E))
  have hle : W ≤ LinearMap.range j := iSup_le fun _ => LinearMap.map_le_range
  let T : D →ₗ[ℂ] E := (basis).constr ℂ (j ∘ v)
  let B := averageMap π hπ τ hτ T
  have hmem (x : D) : B x ∈ LinearMap.range j := by
    apply hle
    change (∫ k : K, π k (T (τ k⁻¹ *ᵥ x)) ∂ν) ∈ W
    apply (W.restrictScalars ℝ).convex.integral_mem W.closed_of_finiteDimensional _
      (integrable_conjugate π hπ τ hτ T x)
    apply Filter.Eventually.of_forall
    intro k
    change π k (T (τ k⁻¹ *ᵥ x)) ∈ W
    simp only [T, Module.Basis.constr_apply_fintype, map_sum, map_smul, Function.comp_apply]
    exact W.sum_mem fun i _ => W.smul_mem _ <| by
      rw [← hj]
      exact (le_iSup (fun i => (FiniteVectors.orbitSpan κ (v i)).map j) i)
        (Submodule.mem_map_of_mem (FiniteVectors.action_mem_orbitSpan κ k (v i)))
  let L := B.codRestrictOfInjective j hinj hmem
  have hL (x : D) : j (L x) = B x := LinearMap.codRestrictOfInjective_comp_apply B j hinj hmem x
  refine ⟨⟨L, fun k x => hinj ?_⟩, LinearMap.ext hL⟩
  rw [hL, hj, hL]
  exact averageMap_intertwines π hπ τ hτ T k x

/-- On a dense compact-finite admissible carrier, postcomposition identifies every
finite-dimensional compact intertwiner with one into the completion. -/
theorem compactIntertwinerMap_bijective (κ : Representation ℂ K V) (j : V →ₗ[ℂ] E)
    (hj : ∀ k x, j (κ k x) = π k (j x)) (hinj : Function.Injective j) (hd : DenseRange j)
    (hfin : ∀ x, FiniteVectors.IsFiniteVector κ x) (hadm : IsAdmissibleGKModule κ)
    (hnorm : ∀ k x, ‖π k x‖ = ‖x‖) : Function.Bijective (compactIntertwinerMap κ π j hj τ) := by
  constructor
  · intro T U h
    apply Subtype.ext
    exact LinearMap.ext fun x =>
      hinj (congrArg (fun L : gkIntertwiners (linearRepresentation π) d τ => L.val x) h)
  · intro T
    let columns : gkIntertwiners κ d τ →ₗ[ℂ] (Fin d → E) := {
      toFun L i := j (L.val (basis i))
      map_add' L M := funext fun i => j.map_add (L.val (basis i)) (M.val (basis i))
      map_smul' c L := funext fun i => j.map_smul c (L.val (basis i)) }
    let A (w : Fin d → E) (i : Fin d) := averageMap π hπ τ hτ ((basis).constr ℂ w) (basis i)
    have hA : Continuous A :=
      continuous_pi fun i => averageMap_continuous_columns π hπ τ hτ hnorm (basis i)
    have : FiniteDimensional ℂ (gkIntertwiners κ d τ) := hadm d τ hτ
    have hclosed : IsClosed (LinearMap.range columns : Set (Fin d → E)) :=
      (LinearMap.range columns).closed_of_finiteDimensional
    have hdpi : DenseRange (fun v : Fin d → V => j ∘ v) :=
      DenseRange.piMap (fun _ : Fin d => hd)
    have hall (w : Fin d → E) : A w ∈ LinearMap.range columns := by
      refine hdpi.induction_on w (hclosed.preimage hA) fun v => ?_
      obtain ⟨L, hL⟩ := averageMap_lifts π hπ τ hτ κ j hj hinj hfin v
      exact ⟨L, funext fun i => LinearMap.congr_fun hL (basis i)⟩
    obtain ⟨L, hL⟩ := hall (fun i => T.val (basis i))
    rw [show A (fun i => T.val (basis i)) = fun i => T.val (basis i) by
      funext i
      simp only [A, Module.Basis.constr_self, averageMap_eq_of_intertwines π hπ τ hτ T]] at hL
    refine ⟨L, Subtype.ext ((basis).ext fun i => ?_)⟩
    exact congrFun hL i

end Average

section Recovery

variable [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [SecondCountableTopology K]
  (κ : Representation ℂ K V) (π : K →* (E →L[ℂ] E)) (j : V →ₗ[ℂ] E)
  (hj : ∀ k x, j (κ k x) = π k (j x)) (hinj : Function.Injective j) (hd : DenseRange j)
  (hfin : ∀ x, FiniteVectors.IsFiniteVector κ x) (hadm : IsAdmissibleGKModule κ)
  (hπ : IsContinuousRepresentation π) (hnorm : ∀ k x, ‖π k x‖ = ‖x‖)

include hj hinj hd hfin hadm hπ hnorm

private theorem compactCompletion_admissible :
    IsAdmissibleGKModule (linearRepresentation π) := by
  intro d τ hτ
  have : FiniteDimensional ℂ (gkIntertwiners κ d τ) := hadm d τ hτ
  exact Module.Finite.of_surjective (compactIntertwinerMap κ π j hj τ)
    (compactIntertwinerMap_bijective π hπ τ hτ κ j hj hinj hd hfin hadm hnorm).2

private theorem compactCompletion_recover (x : E)
    (hx : FiniteVectors.IsFiniteVector (linearRepresentation π) x) :
    x ∈ LinearMap.range j := by
  let S := FiniteVectors.orbitSubrepresentation (linearRepresentation π) x
  have : FiniteDimensional ℂ S.toSubmodule := hx
  let d := Module.finrank ℂ S.toSubmodule
  let b : Module.Basis (Fin d) ℂ S.toSubmodule := Module.finBasis ℂ S.toSubmodule
  let τ := KFiniteDual.subMatrix S
  have hτ : Continuous τ := by
    refine continuous_matrix fun i l => ?_
    have hOrbit : Continuous (fun k : K => S.toRepresentation k (b l)) :=
      (Continuous.comp hπ (continuous_id.prodMk (continuous_const (y := (b l : E))))).subtype_mk _
    have h : Continuous (fun k : K => b.coord i (S.toRepresentation k (b l))) :=
      (b.coord i).continuous_of_finiteDimensional.comp hOrbit
    simpa only [τ, KFiniteDual.subMatrix_apply, ← Module.Basis.coord_apply, b] using h
  let T : gkIntertwiners (linearRepresentation π) d τ :=
    ⟨S.toSubmodule.subtype.comp b.equivFun.symm.toLinearMap, fun k v => by
      have h := KFiniteDual.subMatrix_mulVec S k (b.equivFun.symm v)
      change τ k *ᵥ (b.equivFun (b.equivFun.symm v)) =
        b.equivFun (S.toRepresentation k (b.equivFun.symm v)) at h
      rw [LinearEquiv.apply_symm_apply] at h
      change (b.equivFun.symm (τ k *ᵥ v) : E) = π k (b.equivFun.symm v : E)
      rw [h, LinearEquiv.symm_apply_apply]
      rfl⟩
  obtain ⟨L, hL⟩ :=
    (compactIntertwinerMap_bijective π hπ τ hτ κ j hj hinj hd hfin hadm hnorm).2 T
  let y : S.toSubmodule := ⟨x, FiniteVectors.self_mem_orbitSpan (linearRepresentation π) x⟩
  refine ⟨L.val (b.equivFun y), ?_⟩
  have h := congrArg (fun M : gkIntertwiners (linearRepresentation π) d τ =>
    M.val (b.equivFun y)) hL
  change j (L.val (b.equivFun y)) = (b.equivFun.symm (b.equivFun y) : E) at h
  rwa [LinearEquiv.symm_apply_apply] at h

end Recovery

/-- A continuous isometric completion of a compact-finite admissible carrier is
admissible, and its compact-finite vectors are exactly the original image. -/
def CompactHilbertAdmissibilityStatement : Prop :=
  ∀ {K : Type uK} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (κ : Representation ℂ K V) (π : K →* (E →L[ℂ] E)) (j : V →ₗ[ℂ] E),
    (∀ k x, j (κ k x) = π k (j x)) → Function.Injective j → DenseRange j →
    (∀ x, FiniteVectors.IsFiniteVector κ x) → IsAdmissibleGKModule κ →
    IsContinuousRepresentation π → (∀ k x, ‖π k x‖ = ‖x‖) →
    IsAdmissibleGKModule (linearRepresentation π) ∧
    ∀ x, x ∈ LinearMap.range j ↔ FiniteVectors.IsFiniteVector (linearRepresentation π) x

theorem compactHilbertAdmissibility : CompactHilbertAdmissibilityStatement.{uK, uV, uE} := by
  intro K _ _ _ _ _ _ _ E _ _ _ V _ _ κ π j hj hinj hd hfin hadm hπ hnorm
  refine ⟨compactCompletion_admissible κ π j hj hinj hd hfin hadm hπ hnorm, fun x => ?_⟩
  refine ⟨?_, compactCompletion_recover κ π j hj hinj hd hfin hadm hπ hnorm x⟩
  rintro ⟨v, rfl⟩
  let J : κ.IntertwiningMap (linearRepresentation π) :=
    ⟨j, fun k => LinearMap.ext (hj k)⟩
  exact (hfin v).map J

end Langlands.Archimedean
