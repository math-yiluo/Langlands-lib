import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TemperedPairing
import Langlands.HarmonicAnalysis.SmoothWeakIntegral
import Langlands.Representation.MatrixCoefficient.LawsProof
import Langlands.Representation.Smooth.Contragredient.LawsProof
import Langlands.LinearAlgebra.FiniteRankTrace
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TestFunctions
import Langlands.Representation.Hecke.IntegratedAction

/-! # The operators `π(f)`, `f ∈ C(G)`, of an admissible tempered representation (III.7)

For an admissible representation `ρ` whose coefficients `g ↦ ℓ(ρ(g) v)` have tempered growth
and `f` in the Harish-Chandra Schwartz space `C(G)`, the vector `π(f) v` is the weak integral
`∫_G f(g) ρ(g) v dμ(g)`: the unique vector with `ℓ(π(f) v) = ∫_G f(g) ℓ(ρ(g) v) dμ(g)` for
every smooth functional `ℓ`. The operator `π(f)` has image in the fixed vectors of every
compact open subgroup under which `f` is left invariant, hence has finite rank, and its trace
is a continuous linear form on `C(G)`.
-/

noncomputable section

universe u v

open MeasureTheory Filter Topology
open Langlands.HarmonicAnalysis

namespace Langlands.HarishChandraSchwartz

section Coefficients

variable {G : Type u} [Group G] [TopologicalSpace G] {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- Waldspurger III.2: all coefficients `g ↦ ℓ(ρ(g) v)`, `v ∈ V`, `ℓ` a smooth functional,
have tempered growth `|ℓ(ρ(g) v)| ≤ c Ξ(g) (1 + σ(g))^r`. -/
def HasTemperedCoefficients (Ξ σ : G → ℝ) (ρ : Representation ℂ G V) : Prop :=
  ∀ (v : V) (ℓ : SmoothDual ρ), HasTemperedGrowth Ξ σ (fun g => ℓ.val (ρ g v))

end Coefficients

section Action

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [OpensMeasurableSpace G] [Nonempty (CompactOpenSubgroup G)]
  {μ : Measure G} {Ξ σ : G → ℝ}
  {V : Type v} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

omit [MeasurableSpace G] [OpensMeasurableSpace G] [Nonempty (CompactOpenSubgroup G)] in
/-- Coefficients of smooth vectors are continuous (locally constant). -/
theorem continuous_coefficient (hρ : IsSmooth ρ) (v : V) (ℓ : SmoothDual ρ) :
    Continuous (fun g => ℓ.val (ρ g v)) :=
  (matrixCoefficient_isLocallyConstant ρ ℓ.val v (hρ v)).continuous

omit [IsTopologicalGroup G] [OpensMeasurableSpace G] [Nonempty (CompactOpenSubgroup G)] in
/-- A tempered coefficient has a finite seminorm `ν_{-r}`. -/
theorem exists_nu_coefficient_ne_top (hw : L2Weights μ Ξ σ) (hT : HasTemperedCoefficients Ξ σ ρ)
    (v : V) (ℓ : SmoothDual ρ) : ∃ r : ℝ, nu Ξ σ (-r) (fun g => ℓ.val (ρ g v)) ≠ ⊤ := by
  obtain ⟨s, hs⟩ := (hasTemperedGrowth_iff hw.pos hw.nonneg _).mp (hT v ℓ)
  exact ⟨-s, by rwa [neg_neg]⟩

/-- The continuous linear form `f ↦ ∫_G f(g) ℓ(ρ(g) v) dμ(g)` on `C(G)` (III.7). -/
def coefficientPairing (hw : L2Weights μ Ξ σ) (hρ : IsSmooth ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) (v : V) (ℓ : SmoothDual ρ) : Space Ξ σ →L[ℂ] ℂ :=
  Space.temperedPairing hw (continuous_coefficient hρ v ℓ)
    (exists_nu_coefficient_ne_top hw hT v ℓ).choose_spec

@[simp] theorem coefficientPairing_apply (hw : L2Weights μ Ξ σ) (hρ : IsSmooth ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) (v : V) (ℓ : SmoothDual ρ) (f : Space Ξ σ) :
    coefficientPairing hw hρ hT v ℓ f = ∫ g, f g * ℓ.val (ρ g v) ∂μ :=
  rfl

theorem integrable_coefficient (hw : L2Weights μ Ξ σ) (hρ : IsSmooth ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) (f : Space Ξ σ) (v : V) (ℓ : SmoothDual ρ) :
    Integrable (fun g => f g * ℓ.val (ρ g v)) μ :=
  Space.integrable_mul hw (continuous_coefficient hρ v ℓ)
    (exists_nu_coefficient_ne_top hw hT v ℓ).choose_spec f

/-- The linear form `ℓ ↦ ∫_G f(g) ℓ(ρ(g) v) dμ(g)` on the smooth dual. -/
def dualIntegral (hw : L2Weights μ Ξ σ) (hρ : IsSmooth ρ) (hT : HasTemperedCoefficients Ξ σ ρ)
    (f : Space Ξ σ) (v : V) : Module.Dual ℂ (SmoothDual ρ) where
  toFun ℓ := ∫ g, f g * ℓ.val (ρ g v) ∂μ
  map_add' ℓ₁ ℓ₂ := by
    rw [← integral_add (integrable_coefficient hw hρ hT f v ℓ₁)
      (integrable_coefficient hw hρ hT f v ℓ₂)]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    change f g * (ℓ₁.val (ρ g v) + ℓ₂.val (ρ g v)) = _
    rw [mul_add]
  map_smul' c ℓ := by
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    change f g * (c * ℓ.val (ρ g v)) = c * (f g * ℓ.val (ρ g v))
    ring

@[simp] theorem dualIntegral_apply (hw : L2Weights μ Ξ σ) (hρ : IsSmooth ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) (f : Space Ξ σ) (v : V) (ℓ : SmoothDual ρ) :
    dualIntegral hw hρ hT f v ℓ = ∫ g, f g * ℓ.val (ρ g v) ∂μ :=
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [OpensMeasurableSpace G]
  [Nonempty (CompactOpenSubgroup G)] in
/-- Left translation of the coefficient by `k ∈ H` does not change the integral against a
function `f` left invariant under `H`, for a left invariant measure. -/
theorem integral_mul_coefficient_mul_left [MeasurableMul G] [μ.IsMulLeftInvariant]
    {H : Subgroup G} {f : G → ℂ} (hf : ∀ h ∈ H, ∀ g, f (h * g) = f g) (v : V)
    (ℓ : Module.Dual ℂ V) {k : G} (hk : k ∈ H) :
    ∫ g, f g * ℓ (ρ (k * g) v) ∂μ = ∫ g, f g * ℓ (ρ g v) ∂μ := by
  have h := integral_mul_left_eq_self (μ := μ) (fun x => f (k⁻¹ * x) * ℓ (ρ x v)) k
  simp only [inv_mul_cancel_left] at h
  rw [h]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hf k⁻¹ (H.inv_mem hk) x]

/-- For `f` left invariant under `H` and `k ∈ H`, `dualIntegral f v` is invariant under the
contragredient action of `k⁻¹` on its argument. -/
theorem dualIntegral_smoothContragredient [MeasurableMul G] [μ.IsMulLeftInvariant] (hw : L2Weights μ Ξ σ)
    (hρ : IsSmooth ρ) (hT : HasTemperedCoefficients Ξ σ ρ) {H : Subgroup G} {f : Space Ξ σ}
    (hf : ∀ h ∈ H, ∀ g, f (h * g) = f g) (v : V) (ℓ : SmoothDual ρ) {k : G} (hk : k ∈ H) :
    dualIntegral hw hρ hT f v (smoothContragredient ρ k⁻¹ ℓ) = dualIntegral hw hρ hT f v ℓ := by
  rw [dualIntegral_apply, dualIntegral_apply]
  have h : ∀ g, (smoothContragredient ρ k⁻¹ ℓ).val (ρ g v) = ℓ.val (ρ (k * g) v) := fun g => by
    change ℓ.val (ρ k⁻¹⁻¹ (ρ g v)) = _
    rw [inv_inv, map_mul, Module.End.mul_apply]
  simp_rw [h]
  exact integral_mul_coefficient_mul_left hf v ℓ.val hk

end Action

section Operator

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
  [Nonempty (CompactOpenSubgroup G)]
  {μ : Measure G} [μ.IsMulLeftInvariant] {Ξ σ : G → ℝ}
  {V : Type v} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

omit [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G] in
/-- If `G` has a compact open subgroup, every open subgroup contains a compact open one. -/
theorem CompactOpenSubgroup.cofinal :
    ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K := by
  intro K
  obtain ⟨K₀⟩ := ‹Nonempty (CompactOpenSubgroup G)›
  refine ⟨K ⊓ K₀.1, ?_, _root_.inf_le_left⟩
  rw [OpenSubgroup.coe_inf]
  exact K₀.2.inter_left K.isClosed

omit [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G] in
/-- Smooth functionals separate the vectors of a smooth representation. -/
theorem ext_smoothDual (hρ : IsSmooth ρ) {v w : V}
    (h : ∀ ℓ : SmoothDual ρ, ℓ.val v = ℓ.val w) : v = w :=
  smoothBidual_injective_of_compact_cofinal CompactOpenSubgroup.cofinal ρ hρ
    (Subtype.ext (LinearMap.ext h))

omit [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G] in
/-- Every `f ∈ C(G)` is left invariant under some compact open subgroup. -/
theorem Space.exists_leftInvariant (f : Space Ξ σ) :
    ∃ K : CompactOpenSubgroup G, ∀ h ∈ K.toSubgroup, ∀ g, f (h * g) = f g := by
  obtain ⟨K, hK⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (Space.coe_mem f)
  refine ⟨K, fun h hh g => ?_⟩
  have h₁ := hK.1 h hh 1 (one_mem _) g
  rw [mul_one] at h₁
  exact h₁

omit [IsTopologicalGroup G] [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
  [Nonempty (CompactOpenSubgroup G)] in
/-- An element of the level `C_K` is left invariant under `K`. -/
theorem Level.leftInvariant {K : CompactOpenSubgroup G} (f : Level Ξ σ K) :
    ∀ h ∈ K.toSubgroup, ∀ g, Space.ofLevel K f (h * g) = Space.ofLevel K f g := by
  intro h hh g
  have h₁ := Level.isBiInvariant f h hh 1 (one_mem _) g
  rw [mul_one] at h₁
  exact h₁

/-- The linear form `ℓ ↦ ∫_G f(g) ℓ(ρ(g) v) dμ(g)` is a smooth functional on the smooth dual:
it is fixed by every compact open subgroup under which `f` is left invariant. -/
def dualIntegralSmooth (hw : L2Weights μ Ξ σ) (hρ : IsSmooth ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) (f : Space Ξ σ) (v : V) :
    SmoothDual (smoothContragredient ρ) :=
  ⟨dualIntegral hw hρ hT f v, by
    obtain ⟨K, hK⟩ := Space.exists_leftInvariant f
    refine ⟨K.1, fun k => ?_⟩
    apply LinearMap.ext
    intro ℓ
    exact dualIntegral_smoothContragredient hw hρ hT hK v ℓ k.2⟩

/-- Waldspurger III.7: there is a vector `w` with `ℓ(w) = ∫_G f(g) ℓ(ρ(g) v) dμ(g)` for every
smooth functional `ℓ`, i.e. a weak integral of `g ↦ f(g) ρ(g) v`. -/
theorem exists_hasIntegral (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) (f : Space Ξ σ) (v : V) :
    ∃ w : V, SmoothWeakIntegral.HasIntegral ρ μ (fun g => f g • ρ g v) w := by
  obtain ⟨w, hw'⟩ := smoothBidual_surjective_of_compact_cofinal CompactOpenSubgroup.cofinal ρ hρ
    (dualIntegralSmooth hw hρ.1 hT f v)
  refine ⟨w, fun ℓ => ⟨?_, ?_⟩⟩
  · simp only [map_smul, smul_eq_mul]
    exact integrable_coefficient hw hρ.1 hT f v ℓ
  · have h := congrArg (fun Λ : SmoothDual (smoothContragredient ρ) => Λ.val ℓ) hw'
    change ℓ.val w = ∫ g, f g * ℓ.val (ρ g v) ∂μ at h
    simp only [map_smul, smul_eq_mul]
    exact h.symm

/-- The weakly integrable functions `g ↦ f(g) ρ(g) v`, linear in `v`. -/
def integrand (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ) (hT : HasTemperedCoefficients Ξ σ ρ)
    (f : Space Ξ σ) : V →ₗ[ℂ] SmoothWeakIntegral.integrableSubmodule ρ μ where
  toFun v := ⟨fun g => f g • ρ g v, exists_hasIntegral hw hρ hT f v⟩
  map_add' v₁ v₂ := by
    apply Subtype.ext
    funext g
    change f g • ρ g (v₁ + v₂) = f g • ρ g v₁ + f g • ρ g v₂
    rw [map_add, smul_add]
  map_smul' c v := by
    apply Subtype.ext
    funext g
    change f g • ρ g (c • v) = c • (f g • ρ g v)
    rw [map_smul, smul_comm]

/-- The operator `v ↦ ∫_G f(g) ρ(g) v dμ(g)` for a single `f ∈ C(G)`. -/
def actionEnd (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ) (hT : HasTemperedCoefficients Ξ σ ρ)
    (f : Space Ξ σ) : Module.End ℂ V :=
  (SmoothWeakIntegral.integralLinear CompactOpenSubgroup.cofinal hρ.1).comp
    (integrand hw hρ hT f)

theorem actionEnd_eval (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) (f : Space Ξ σ) (v : V) (ℓ : SmoothDual ρ) :
    ℓ.val (actionEnd hw hρ hT f v) = ∫ g, f g * ℓ.val (ρ g v) ∂μ := by
  rw [actionEnd, LinearMap.comp_apply, SmoothWeakIntegral.integralLinear_eval]
  change ∫ g, ℓ.val (f g • ρ g v) ∂μ = _
  simp only [map_smul, smul_eq_mul]

/-- Waldspurger III.7: the operators `π(f) v = ∫_G f(g) ρ(g) v dμ(g)`, `f ∈ C(G)`, of an
admissible representation with tempered coefficients, as a linear map in `f`. -/
def schwartzAction (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) : Space Ξ σ →ₗ[ℂ] Module.End ℂ V where
  toFun := actionEnd hw hρ hT
  map_add' f₁ f₂ := LinearMap.ext fun v => ext_smoothDual hρ.1 fun ℓ => by
    rw [LinearMap.add_apply, map_add, actionEnd_eval, actionEnd_eval, actionEnd_eval]
    exact (coefficientPairing hw hρ.1 hT v ℓ).map_add f₁ f₂
  map_smul' c f := LinearMap.ext fun v => ext_smoothDual hρ.1 fun ℓ => by
    rw [LinearMap.smul_apply, map_smul, actionEnd_eval, actionEnd_eval, RingHom.id_apply,
      smul_eq_mul]
    exact (coefficientPairing hw hρ.1 hT v ℓ).map_smul c f

/-- The defining property of `π(f) v`: `ℓ(π(f) v) = ∫_G f(g) ℓ(ρ(g) v) dμ(g)`. -/
theorem schwartzAction_eval (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) (f : Space Ξ σ) (v : V) (ℓ : SmoothDual ρ) :
    ℓ.val (schwartzAction hw hρ hT f v) = ∫ g, f g * ℓ.val (ρ g v) ∂μ :=
  actionEnd_eval hw hρ hT f v ℓ

theorem schwartzAction_eval_eq_coefficientPairing (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) (f : Space Ξ σ) (v : V) (ℓ : SmoothDual ρ) :
    ℓ.val (schwartzAction hw hρ hT f v) = coefficientPairing hw hρ.1 hT v ℓ f :=
  schwartzAction_eval hw hρ hT f v ℓ

/-- `π(f) v` is the weak integral of `g ↦ f(g) ρ(g) v` tested by the smooth dual. -/
theorem hasIntegral_schwartzAction (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) (f : Space Ξ σ) (v : V) :
    SmoothWeakIntegral.HasIntegral ρ μ (fun g => f g • ρ g v) (schwartzAction hw hρ hT f v) :=
  SmoothWeakIntegral.integralLinear_spec CompactOpenSubgroup.cofinal hρ.1 (integrand hw hρ hT f v)

/-- Uniqueness in III.7: any weak integral of `g ↦ f(g) ρ(g) v` is `π(f) v`. -/
theorem schwartzAction_eq_of_hasIntegral (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) {f : Space Ξ σ} {v w : V}
    (h : SmoothWeakIntegral.HasIntegral ρ μ (fun g => f g • ρ g v) w) :
    schwartzAction hw hρ hT f v = w :=
  SmoothWeakIntegral.integralLinear_eq CompactOpenSubgroup.cofinal hρ.1 (integrand hw hρ hT f v) h

/-- Continuity in `f`: each matrix coefficient `f ↦ ℓ(π(f) v)` is continuous on `C(G)`. -/
theorem continuous_schwartzAction_eval (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) (v : V) (ℓ : SmoothDual ρ) :
    Continuous fun f : Space Ξ σ => ℓ.val (schwartzAction hw hρ hT f v) := by
  simp_rw [schwartzAction_eval_eq_coefficientPairing]
  exact (coefficientPairing hw hρ.1 hT v ℓ).continuous

/-- If `f` is left invariant under `H`, then `π(f)` takes values in the `H`-fixed vectors. -/
theorem schwartzAction_mem_fixedVectors (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) {H : Subgroup G} {f : Space Ξ σ}
    (hf : ∀ h ∈ H, ∀ g, f (h * g) = f g) (v : V) :
    schwartzAction hw hρ hT f v ∈ fixedVectors ρ H := by
  intro k
  change ρ (k : G) (schwartzAction hw hρ hT f v) = schwartzAction hw hρ hT f v
  refine ext_smoothDual hρ.1 fun ℓ => ?_
  have h₁ : ℓ.val (ρ (k : G) (schwartzAction hw hρ hT f v)) =
      (smoothContragredient ρ (k : G)⁻¹ ℓ).val (schwartzAction hw hρ hT f v) := by
    change _ = ℓ.val (ρ (k : G)⁻¹⁻¹ _)
    rw [inv_inv]
  rw [h₁, schwartzAction_eval, schwartzAction_eval]
  exact dualIntegral_smoothContragredient hw hρ.1 hT hf v ℓ k.2

/-- For `f ∈ C_K`, the image of `π(f)` lies in `V^K`. -/
theorem range_schwartzAction_le (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) {K : CompactOpenSubgroup G} (f : Level Ξ σ K) :
    LinearMap.range (schwartzAction hw hρ hT (Space.ofLevel K f)) ≤ fixedVectors ρ K.toSubgroup := by
  rintro _ ⟨v, rfl⟩
  exact schwartzAction_mem_fixedVectors hw hρ hT (Level.leftInvariant f) v

/-- Waldspurger III.7: since `ρ` is admissible, `π(f)` has finite rank. -/
theorem schwartzAction_mem_finiteRankEnd (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) (f : Space Ξ σ) :
    schwartzAction hw hρ hT f ∈ finiteRankEnd V := by
  obtain ⟨K, hK⟩ := Space.exists_leftInvariant f
  rw [mem_finiteRankEnd_iff]
  have : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup) := hρ.2 K.1
  have hle : LinearMap.range (schwartzAction hw hρ hT f) ≤ fixedVectors ρ K.toSubgroup := by
    rintro _ ⟨v, rfl⟩
    exact schwartzAction_mem_fixedVectors hw hρ hT hK v
  exact Submodule.finiteDimensional_of_le hle

/-- `f ↦ π(f)` as a linear map into the finite-rank endomorphisms. -/
def finiteRankSchwartzAction (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) : Space Ξ σ →ₗ[ℂ] finiteRankEnd V :=
  (schwartzAction hw hρ hT).codRestrict (finiteRankEnd V)
    (schwartzAction_mem_finiteRankEnd hw hρ hT)

@[simp] theorem finiteRankSchwartzAction_val (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) (f : Space Ξ σ) :
    (finiteRankSchwartzAction hw hρ hT f).val = schwartzAction hw hρ hT f :=
  rfl

/-- The realization of `π(f)`, `f ∈ C_K`, on the finite-dimensional space `V^K`. -/
def levelAction (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ) (hT : HasTemperedCoefficients Ξ σ ρ)
    (K : CompactOpenSubgroup G) (f : Level Ξ σ K) : Module.End ℂ (fixedVectors ρ K.toSubgroup) :=
  FiniteRankEnd.onSubspace (schwartzAction hw hρ hT (Space.ofLevel K f)) _
    (range_schwartzAction_le hw hρ hT f)

@[simp] theorem levelAction_apply (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) (K : CompactOpenSubgroup G) (f : Level Ξ σ K)
    (v : fixedVectors ρ K.toSubgroup) :
    (levelAction hw hρ hT K f v : V) = schwartzAction hw hρ hT (Space.ofLevel K f) v :=
  rfl

/-- On a level `C_K` the trace of `π(f)` is a finite sum of coefficient pairings: for a basis
`b` of `V^K` and smooth functionals `ℓ i` restricting to the dual basis on `V^K`,
`trace π(f) = Σ_i ∫_G f(g) ℓ_i(ρ(g) b_i) dμ(g)`. -/
theorem trace_levelAction_eq_sum (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) (K : CompactOpenSubgroup G)
    [FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup)] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ (fixedVectors ρ K.toSubgroup))
    (ℓ : ι → fixedVectors (V := SmoothDual ρ) (smoothContragredient ρ) K.toSubgroup)
    (hℓ : ∀ i, smoothDualFixedRestriction ρ K.toSubgroup (ℓ i) = b.coord i) (f : Level Ξ σ K) :
    LinearMap.trace ℂ _ (levelAction hw hρ hT K f) =
      ∑ i, coefficientPairing hw hρ.1 hT (b i) (ℓ i).val (Space.ofLevel K f) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, ← Module.Basis.coord_apply, ← hℓ i,
    ← schwartzAction_eval_eq_coefficientPairing]
  rfl

/-- Waldspurger III.7: the character `θ_π(f) = trace π(f)`, a continuous linear form on
`C(G)`. -/
def schwartzCharacter (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) : Space Ξ σ →L[ℂ] ℂ :=
  Space.mkCLM (FiniteRankEnd.trace ∘ₗ finiteRankSchwartzAction hw hρ hT) fun K => by
    have : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup) := hρ.2 K.1
    let b := Module.finBasis ℂ (fixedVectors ρ K.toSubgroup)
    choose ℓ hℓ using fun i => (smoothDualFixedRestriction_bijective ρ hρ.1 K.1 K.2).2 (b.coord i)
    have heq : (FiniteRankEnd.trace ∘ₗ finiteRankSchwartzAction hw hρ hT) ∘ Space.ofLevel K =
        fun f => ∑ i, coefficientPairing hw hρ.1 hT (b i) (ℓ i).val (Space.ofLevel K f) := by
      funext f
      rw [← trace_levelAction_eq_sum hw hρ hT K b ℓ hℓ f]
      exact FiniteRankEnd.trace_eq_subspace _ _ (range_schwartzAction_le hw hρ hT f)
    rw [heq]
    exact continuous_finsetSum _ fun i _ =>
      (coefficientPairing hw hρ.1 hT (b i) (ℓ i).val).continuous.comp (Space.continuous_ofLevel K)

theorem schwartzCharacter_apply (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) (f : Space Ξ σ) :
    schwartzCharacter hw hρ hT f = FiniteRankEnd.trace (finiteRankSchwartzAction hw hρ hT f) :=
  rfl

/-- On a level `C_K`, `θ_π(f)` is the trace of the realization of `π(f)` on `V^K`. -/
theorem schwartzCharacter_ofLevel (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) (K : CompactOpenSubgroup G) (f : Level Ξ σ K) :
    haveI : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup) := hρ.2 K.1
    schwartzCharacter hw hρ hT (Space.ofLevel K f) =
      LinearMap.trace ℂ _ (levelAction hw hρ hT K f) := by
  have : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup) := hρ.2 K.1
  exact FiniteRankEnd.trace_eq_subspace _ _ (range_schwartzAction_le hw hρ hT f)

end Operator

section TestFunctions

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
  [Nonempty (CompactOpenSubgroup G)]
  {μ : Measure G} [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] {Ξ σ : G → ℝ}
  {V : Type v} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

/-- On test functions `f ∈ C_c^∞(G) ⊆ C(G)`, `π(f)` is the integrated action of the Hecke
algebra. -/
theorem schwartzAction_ofSchwartzBruhat (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) (hΞc : Continuous Ξ) (hσc : Continuous σ)
    (f : HarmonicAnalysis.SchwartzBruhat G) :
    schwartzAction hw hρ hT (ofSchwartzBruhat hΞc hw.pos hσc hw.nonneg f) =
      Hecke.integratedAction μ ρ hρ.1 f := by
  refine LinearMap.ext fun v => ext_smoothDual hρ.1 fun ℓ => ?_
  rw [schwartzAction_eval, Hecke.integratedAction_dual]
  rfl

end TestFunctions

end Langlands.HarishChandraSchwartz
