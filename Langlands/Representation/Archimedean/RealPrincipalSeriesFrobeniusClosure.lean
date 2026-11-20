import Langlands.Representation.Archimedean.RealPrincipalSeriesFrobeniusHilbert
import Mathlib.Analysis.Analytic.Order

/-! # The invariant Hilbert closure of the real Frobenius image -/

noncomputable section

open Filter
open scoped Matrix Matrix.Norms.Operator TensorProduct Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealPrincipalSeriesHilbert

attribute [local instance 100] LieRing.ofAssociativeRing

universe uV

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "GL" => Langlands.GeneralLinear n ℝ
local notation "K" => unitaryCompact ℝ n

variable {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V}
  {ℓ : V →ₗ[ℂ] ℂ} {a : Fin n → ℂ} {e : Fin n → Fin 2}
  (hgk : IsRealGKModule n ρ π) (hℓ : IsRealJacquetFunctional n ρ π ℓ a e)

/-- The closure of the algebraic Frobenius image inside the compact Hilbert principal series. -/
def frobeniusClosure : Submodule ℂ (Hilbert a e) :=
  (LinearMap.range (frobeniusHilbert hgk hℓ)).topologicalClosure

/-- The Frobenius map with codomain its Hilbert closure. -/
def frobeniusClosureMap : V →ₗ[ℂ] frobeniusClosure hgk hℓ :=
  (Submodule.inclusion (LinearMap.range (frobeniusHilbert hgk hℓ)).le_topologicalClosure).comp
    (frobeniusHilbert hgk hℓ).rangeRestrict

@[simp]
theorem coe_frobeniusClosureMap (v : V) :
    (frobeniusClosureMap hgk hℓ v : Hilbert a e) = frobeniusHilbert hgk hℓ v := rfl

theorem isClosed_frobeniusClosure : IsClosed (frobeniusClosure hgk hℓ : Set (Hilbert a e)) :=
  (LinearMap.range (frobeniusHilbert hgk hℓ)).isClosed_topologicalClosure

instance : CompleteSpace (frobeniusClosure hgk hℓ) :=
  (isClosed_frobeniusClosure hgk hℓ).isComplete.completeSpace_coe

theorem denseRange_frobeniusClosureMap : DenseRange (frobeniusClosureMap hgk hℓ) := by
  have hrange : Subtype.val '' Set.range (frobeniusClosureMap hgk hℓ) =
      Set.range (frobeniusHilbert hgk hℓ) := by
    rw [← Set.range_comp]
    rfl
  intro x
  rw [closure_subtype, hrange]
  exact x.2

private theorem hasDerivAt_exponential_frobeniusHilbert (X : Mat) (v : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => representation a e (matrixExpUnit n (s • X))
      (frobeniusHilbert hgk hℓ v))
      (representation a e (matrixExpUnit n (t • X)) (frobeniusHilbert hgk hℓ (π (1 ⊗ₜ X) v))) t := by
  let A := (representation a e (matrixExpUnit n (t • X))).restrictScalars ℝ
  have h0 : HasDerivAt (fun s : ℝ => representation a e (matrixExpUnit n (s • X))
      (frobeniusHilbert hgk hℓ v)) (frobeniusHilbert hgk hℓ (π (1 ⊗ₜ X) v)) (t - t) := by
    rw [sub_self]
    exact hasDerivAt_exponential_frobeniusHilbert_zero hgk hℓ X v
  have h := HasDerivAt.comp_sub_const t t (A.hasFDerivAt.comp_hasDerivAt (t - t) h0)
  apply h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  change representation a e (matrixExpUnit n (s • X)) (frobeniusHilbert hgk hℓ v) =
    representation a e (matrixExpUnit n (t • X)) (representation a e
      (matrixExpUnit n ((s - t) • X)) (frobeniusHilbert hgk hℓ v))
  rw [← mul_apply_eq_comp, ← map_mul, ← matrixExpUnit_add_smul, show t + (s - t) = s by ring]

private theorem exponential_frobeniusHilbert_mem (X : Mat) (v : V) (t : ℝ) :
    representation a e (matrixExpUnit n (t • X)) (frobeniusHilbert hgk hℓ v) ∈
      frobeniusClosure hgk hℓ := by
  let W := frobeniusClosure hgk hℓ
  let L : Hilbert a e →L[ℝ] Hilbert a e :=
    (ContinuousLinearMap.id ℂ (Hilbert a e) - W.starProjection).restrictScalars ℝ
  let j := frobeniusHilbert hgk hℓ
  let F : V → ℝ → Hilbert a e := fun w s =>
    L (representation a e (matrixExpUnit n (s • X)) (j w))
  let D : Module.End ℂ V := π (1 ⊗ₜ X)
  have hF (w : V) (s : ℝ) : AnalyticAt ℝ (F w) s :=
    (L.analyticAt _).comp (analyticAt_exponential_frobeniusHilbert hgk hℓ X w s)
  have hD (w : V) (s : ℝ) : HasDerivAt (F w) (F (D w) s) s :=
    L.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_exponential_frobeniusHilbert hgk hℓ X w s)
  have hiter (m : ℕ) (w : V) : iteratedDeriv m (F w) = F ((D ^ m) w) := by
    induction m with
    | zero => rw [iteratedDeriv_zero, pow_zero, Module.End.one_apply]
    | succ m ih =>
      rw [iteratedDeriv_succ, ih, pow_succ', Module.End.mul_apply]
      exact funext fun s => (hD ((D ^ m) w) s).deriv
  have hzero (w : V) : F w 0 = 0 := by
    have hw : j w ∈ W := (LinearMap.range j).le_topologicalClosure ⟨w, rfl⟩
    simp only [F, zero_smul, matrixExpUnit_zero, map_one, one_apply_eq_self]
    change j w - W.starProjection (j w) = 0
    exact sub_eq_zero.mpr (W.starProjection_mem_subspace_eq_self ⟨j w, hw⟩).symm
  have htop : analyticOrderAt (F v) 0 = ⊤ := by
    apply ENat.eq_top_iff_forall_ge.mpr
    intro m
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hF v 0)).mpr
    intro k _
    rw [hiter, hzero]
  have hEq := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero 0 (hF v)).mp htop
  have ht := congrFun hEq t
  change representation a e (matrixExpUnit n (t • X)) (j v) - W.starProjection
    (representation a e (matrixExpUnit n (t • X)) (j v)) = 0 at ht
  rw [sub_eq_zero] at ht
  rw [ht]
  exact W.starProjection_apply_mem _

private theorem mapsTo_frobeniusClosure_of_range (g : GL)
    (h : ∀ v : V, representation a e g (frobeniusHilbert hgk hℓ v) ∈ frobeniusClosure hgk hℓ) :
    ∀ x ∈ frobeniusClosure hgk hℓ, representation a e g x ∈ frobeniusClosure hgk hℓ := by
  have hclosed := (isClosed_frobeniusClosure hgk hℓ).preimage (representation a e g).continuous
  have hle : Set.range (frobeniusHilbert hgk hℓ) ⊆
      (representation a e g) ⁻¹' (frobeniusClosure hgk hℓ : Set (Hilbert a e)) := by
    rintro _ ⟨v, rfl⟩
    exact h v
  exact fun x hx => closure_minimal hle hclosed hx

/-- The closure of the Frobenius image is stable under the actual general linear group. -/
theorem mapsTo_frobeniusClosure (g : GL) :
    ∀ x ∈ frobeniusClosure hgk hℓ, representation a e g x ∈ frobeniusClosure hgk hℓ := by
  have hK (k : K) : ∀ x ∈ frobeniusClosure hgk hℓ,
      representation a e (k : GL) x ∈ frobeniusClosure hgk hℓ := by
    apply mapsTo_frobeniusClosure_of_range hgk hℓ
    intro v
    rw [representation_frobeniusHilbert_compact]
    exact (frobeniusClosureMap hgk hℓ _).2
  obtain ⟨k₁, hk₁, k₂, hk₂, h, rfl⟩ := MatrixCoefficientAnalytic.exists_kak g
  rw [KIntegralInvariance.expDiagonal_one_eq]
  intro x hx
  simp only [map_mul, mul_apply_eq_comp]
  exact hK ⟨k₁, hk₁⟩ _ (mapsTo_frobeniusClosure_of_range hgk hℓ _
    (fun v => exponential_frobeniusHilbert_mem hgk hℓ (Matrix.diagonal h) v 1) _
    (hK ⟨k₂, hk₂⟩ x hx))

/-- The continuous-operator action on the Frobenius Hilbert closure. -/
def frobeniusClosureRepresentation : GL →* (frobeniusClosure hgk hℓ →L[ℂ] frobeniusClosure hgk hℓ) where
  toFun g := (representation a e g).restrict (mapsTo_frobeniusClosure hgk hℓ g)
  map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change representation a e 1 (x : Hilbert a e) = x.1
    rw [map_one, one_apply_eq_self]
  map_mul' g h := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change representation a e (g * h) (x : Hilbert a e) =
      representation a e g (representation a e h (x : Hilbert a e))
    rw [map_mul, mul_apply_eq_comp]

@[simp]
theorem coe_frobeniusClosureRepresentation (g : GL) (x : frobeniusClosure hgk hℓ) :
    (frobeniusClosureRepresentation hgk hℓ g x : Hilbert a e) = representation a e g x := rfl

theorem isContinuousRepresentation_frobeniusClosureRepresentation :
    IsContinuousRepresentation (E := ↥(frobeniusClosure hgk hℓ))
      (frobeniusClosureRepresentation hgk hℓ) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p : GL × frobeniusClosure hgk hℓ => representation a e p.1 p.2.1)
  have hAct : Continuous (fun p : GL × Hilbert a e => representation a e p.1 p.2) :=
    isContinuousRepresentation a e
  have hIncl : Continuous (fun p : GL × frobeniusClosure hgk hℓ =>
      (p.1, (p.2 : Hilbert a e))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have h := hAct.comp hIncl
  simpa only [Function.comp_def] using h

end Langlands.Archimedean.RealPrincipalSeriesHilbert
