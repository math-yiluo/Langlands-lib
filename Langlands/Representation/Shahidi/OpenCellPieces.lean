import Langlands.Representation.Shahidi.OpenCellJacquetConvergence

/-! # Degree pieces of Jacquet functions

The degree of `m₁ ∈ GL_(r+1)(K)` is `v(det m₁) = ∑ λ_i` for its Iwasawa exponent `λ`. Restricting
a Levi function to first-block degree `e` gives the degree piece `Φ_e`; the pieces of the
two-block section are homogeneous of degree `e` in the first parameter tuple (for `ψ` of
conductor `𝒪`), and, for Levi-invariant functions, at every torus point where the Jacquet
integrand is integrable the Jacquet function is the sum of the Jacquet functions of its pieces
(at every point, if the function is moreover Levi-equivariant and the integrands are integrable
at all torus points). -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open Langlands.GeneralLinear Langlands.Conductor Langlands.GeneralLinear.Spherical
open Langlands.GeneralLinear.Iwasawa MeasureTheory
open scoped ENNReal NNReal

section Generic

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Sums over a partition by an integer label.** -/
theorem hasSum_integral_ite {F : α → ℂ} (d : α → ℤ) (hF : Integrable F μ)
    (hmeas : ∀ e : ℤ, AEStronglyMeasurable (fun x => if d x = e then F x else 0) μ) :
    HasSum (fun e : ℤ => ∫ x, (if d x = e then F x else 0) ∂μ) (∫ x, F x ∂μ) := by
  refine hasSum_integral_of_dominated_convergence (fun e x => ‖if d x = e then F x else 0‖)
    hmeas (fun e => Filter.Eventually.of_forall fun x => le_refl _) ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun x => ?_
    apply summable_of_ne_finset_zero (s := {d x})
    intro e he
    rw [Finset.mem_singleton] at he
    simp [Ne.symm he]
  · have h : (fun x => ∑' e : ℤ, ‖if d x = e then F x else 0‖) = fun x => ‖F x‖ := by
      funext x
      rw [tsum_eq_single (d x)]
      · simp
      · intro e he
        simp [Ne.symm he]
    rw [h]
    exact hF.norm
  · refine Filter.Eventually.of_forall fun x => ?_
    have := hasSum_ite_eq (d x) (F x)
    simpa [eq_comm] using this

end Generic

universe u

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}

local instance ocPiecesTopologicalSpace : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology
local instance ocPiecesValuativeRel : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel
local instance ocPiecesLocalField : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField
local instance ocPiecesT2Space : T2Space K.Carrier := K.canonicalTopologicalData.fieldT2
local instance ocPiecesSecondCountableTopology : SecondCountableTopology K.Carrier :=
  K.canonicalTopologicalData.secondCountableTopology
local instance ocPiecesMeasurableSpace : MeasurableSpace K.Carrier := borel K.Carrier
local instance ocPiecesBorelSpace : BorelSpace K.Carrier := ⟨rfl⟩

variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _
  K.canonicalTopologicalData.topology)
variable {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
    (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)
variable {r t : ℕ}

section Degree

/-- The degree `v(det m) = ∑ λ_i` of `m`, for the Iwasawa exponent `λ` of `m`. -/
def detExponent {n : ℕ} (m : Langlands.GeneralLinear (n + 1) K.Carrier) : ℤ :=
  ∑ i, Iwasawa.exponent hϖ m i

theorem detExponent_mul_integral {n : ℕ} (m : Langlands.GeneralLinear (n + 1) K.Carrier)
    {k : Langlands.GeneralLinear (n + 1) K.Carrier}
    (hk : k ∈ integralSubgroup K.canonicalTopologicalData.Integers n) :
    detExponent hϖ (m * k) = detExponent hϖ m := by
  rw [detExponent, detExponent, Iwasawa.exponent_mul_integral hϖ m hk]

theorem detExponent_unipotent_mul {n : ℕ} {u : Langlands.GeneralLinear (n + 1) K.Carrier}
    (hu : u ∈ upperUnipotent (n + 1) K.Carrier) (m : Langlands.GeneralLinear (n + 1) K.Carrier) :
    detExponent hϖ (u * m) = detExponent hϖ m := by
  obtain ⟨u', hu', k', hk', h'⟩ := Iwasawa.exists_eq_exponent hϖ m
  have h := Iwasawa.exponent_eq hϖ (mul_mem hu hu') hk'
    (show u * m = (u * u') * Iwasawa.torus ϖ (Iwasawa.exponent hϖ m) * k' by
      conv_lhs => rw [h']
      group)
  rw [detExponent, detExponent, h]

theorem detExponent_unipotent_mul_torus {n : ℕ} {u : Langlands.GeneralLinear (n + 1) K.Carrier}
    (hu : u ∈ upperUnipotent (n + 1) K.Carrier) (ρ : Fin (n + 1) → ℤ) :
    detExponent hϖ (u * Iwasawa.torus ϖ ρ) = ∑ i, ρ i := by
  rw [detExponent, Iwasawa.exponent_eq hϖ hu (one_mem _) (mul_one _).symm]

/-- The degree piece of a Levi function: its restriction to first-block degree `e`. -/
def degreePiece (e : ℤ) (Φ : Langlands.GeneralLinear (r + 1) K.Carrier →
      Langlands.GeneralLinear (t + 1) K.Carrier → ℂ)
    (m₁ : Langlands.GeneralLinear (r + 1) K.Carrier) (m₂ : Langlands.GeneralLinear (t + 1) K.Carrier) :
    ℂ :=
  if detExponent hϖ m₁ = e then Φ m₁ m₂ else 0

variable {Φ : Langlands.GeneralLinear (r + 1) K.Carrier →
    Langlands.GeneralLinear (t + 1) K.Carrier → ℂ}

theorem isLeviInvariant_degreePiece (e : ℤ) (hΦ : IsLeviInvariant Φ) :
    IsLeviInvariant (degreePiece hϖ e Φ) := by
  intro m₁ μ₁ m₂ μ₂ h₁ h₂
  simp only [degreePiece, detExponent_mul_integral hϖ m₁ h₁, hΦ _ _ _ _ h₁ h₂]

theorem isLeviEquivariant_degreePiece (e : ℤ) {θ₁ : upperUnipotent (r + 1) K.Carrier →* ℂˣ}
    {θ₂ : upperUnipotent (t + 1) K.Carrier →* ℂˣ} (hθ : IsLeviEquivariant θ₁ θ₂ Φ) :
    IsLeviEquivariant θ₁ θ₂ (degreePiece hϖ e Φ) := by
  intro u₁ u₂ m₁ m₂
  simp only [degreePiece, detExponent_unipotent_mul hϖ u₁.2, hθ u₁ u₂ m₁ m₂]
  split_ifs <;> simp

/-- The first-block degree of a point, read off the lift's chosen decomposition. -/
def liftDegree (x : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) : ℤ :=
  detExponent hϖ (liftFirst K r t ⟨(exists_liftShape_parabolic_mul r t hϖ x).choose,
    (exists_liftShape_parabolic_mul r t hϖ x).choose_spec.1⟩)

theorem liftFunction_degreePiece (e : ℤ) (x : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    liftFunction hϖ (degreePiece hϖ e Φ) x =
      if liftDegree hϖ x = e then liftFunction hϖ Φ x else 0 := rfl

theorem liftFunction_const_mul (z : ℂ) (x : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    liftFunction hϖ (fun m₁ m₂ => z * Φ m₁ m₂) x = z * liftFunction hϖ Φ x := rfl

end Degree

section Homogeneity

include hϖ in
/-- `W°(m; X a) = X^(v(det m)) W°(m; a)`, for `ψ` of conductor `𝒪`. -/
theorem sphericalWhittaker_smul_eq {n : ℕ}
    (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0) (X : ℂˣ) (a : Fin (n + 1) → ℂˣ)
    (m : Langlands.GeneralLinear (n + 1) K.Carrier) :
    GeneralLinear.Spherical.sphericalWhittaker hϖ
        (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ n)
        K.canonicalTopologicalData.residueCardinality (fun i => X * a i) m =
      (X : ℂ) ^ detExponent hϖ m *
        GeneralLinear.Spherical.sphericalWhittaker hϖ
          (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ n)
          K.canonicalTopologicalData.residueCardinality a m := by
  have hθ := isIntegrallyTrivial_of_additiveConductor K hψ n
  obtain ⟨u, hu, k, hk, h⟩ := Iwasawa.exists_eq_exponent hϖ m
  have hd : detExponent hϖ m = ∑ i, Iwasawa.exponent hϖ m i := rfl
  rw [hd, h, GeneralLinear.Spherical.sphericalWhittaker_mul_integral hϖ _ _ hθ _ hk,
    GeneralLinear.Spherical.sphericalWhittaker_mul_integral hϖ _ _ hθ _ hk,
    sphericalWhittaker_smul_unipotent_mul_torus hϖ hθ _ X a hu]
  congr 3
  rw [← h]

include hϖ in
/-- For `ψ` of conductor `𝒪`, the section with first parameters `X a` is `X^(v(det m₁))` times
the section with `a`. -/
theorem fullΦ_smul (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0) (X : ℂˣ)
    (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ)
    (m₁ : Langlands.GeneralLinear (r + 1) K.Carrier) (m₂ : Langlands.GeneralLinear (t + 1) K.Carrier) :
    Base.fullΦ ψ hϖ (fun i => X * a i) c s m₁ m₂ =
      (X : ℂ) ^ detExponent hϖ m₁ * Base.fullΦ ψ hϖ a c s m₁ m₂ := by
  simp only [Base.fullΦ, sphericalWhittaker_smul_eq ψ hϖ hψ X a m₁]
  ring

include hϖ in
theorem degreePiece_fullΦ_smul (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (e : ℤ) (X : ℂˣ) (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ) :
    degreePiece hϖ e (Base.fullΦ ψ hϖ (fun i => X * a i) c s) =
      fun m₁ m₂ => (X : ℂ) ^ e * degreePiece hϖ e (Base.fullΦ ψ hϖ a c s) m₁ m₂ := by
  funext m₁ m₂
  simp only [degreePiece]
  split_ifs with h
  · rw [fullΦ_smul ψ hϖ hψ, h]
  · rw [mul_zero]

include hϖ in
/-- For `ψ` of conductor `𝒪`, the Jacquet function of the degree-`e` piece is homogeneous of
degree `e` in `X`. -/
theorem jacquetFunction_degreePiece_smul (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (e : ℤ) (X : ℂˣ) (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ)
    (g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    jacquetFunction ψ hϖ (degreePiece hϖ e (Base.fullΦ ψ hϖ (fun i => X * a i) c s)) g =
      (X : ℂ) ^ e * jacquetFunction ψ hϖ (degreePiece hϖ e (Base.fullΦ ψ hϖ a c s)) g := by
  rw [degreePiece_fullΦ_smul ψ hϖ hψ, jacquetFunction, jacquetFunction, ← integral_const_mul]
  congr 1
  funext Y
  simp only [jacquetIntegrandAt_apply, liftFunction_const_mul]
  ring

end Homogeneity

section Decomposition

variable {Φ : Langlands.GeneralLinear (r + 1) K.Carrier →
    Langlands.GeneralLinear (t + 1) K.Carrier → ℂ}

theorem continuous_intertwiningJacquetKernel :
    Continuous (intertwiningJacquetKernel r t ψ) := by
  have e : intertwiningJacquetKernel r t ψ =
      fun Y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier => ψ.complex (-(Y (Fin.last t) 0)) :=
    funext (intertwiningJacquetKernel_eq_neg_corner ψ r t)
  rw [e]
  exact ψ.continuous_complex.comp (continuous_neg.comp
    ((continuous_apply 0).comp (continuous_apply (Fin.last t))))

/-- The Jacquet integrand of a degree piece of a Levi-invariant `Φ` at an exchanged block point. -/
theorem jacquetIntegrandAt_degreePiece_swap (hΦ : IsLeviInvariant Φ) (e : ℤ)
    (h₂ : Langlands.GeneralLinear (t + 1) K.Carrier) (h₁ : Langlands.GeneralLinear (r + 1) K.Carrier) :
    jacquetIntegrandAt ψ hϖ (degreePiece hϖ e Φ) (swapRank (r + 1) (t + 1) K.Carrier (blockSum (h₂, h₁))) =
      fun Y => if liftDegree hϖ (blockSum (h₁, h₂) *
          lower (r + 1) (t + 1) K.Carrier (rectangularConj h₂ h₁ Y)) = e then
        jacquetIntegrandAt ψ hϖ Φ (swapRank (r + 1) (t + 1) K.Carrier (blockSum (h₂, h₁))) Y
      else 0 := by
  rw [jacquetIntegrandAt_swap ψ hϖ (isLeviInvariant_degreePiece hϖ e hΦ),
    jacquetIntegrandAt_swap ψ hϖ hΦ]
  funext Y
  simp only [translatedLower, liftFunction_degreePiece]
  split_ifs <;> simp

/-- **The piece decomposition at a torus point**, for a Levi-invariant `Φ` whose Jacquet
integrand is integrable there. -/
theorem hasSum_jacquetFunction_degreePiece_torus (hΦ : IsLeviInvariant Φ)
    (μ : Fin ((r + 1) + (t + 1)) → ℤ)
    (hi : Integrable (jacquetIntegrandAt ψ hϖ Φ (Iwasawa.torus ϖ μ)) (matrixHaar K (t + 1) (r + 1))) :
    HasSum (fun e : ℤ => jacquetFunction ψ hϖ (degreePiece hϖ e Φ) (Iwasawa.torus ϖ μ))
      (jacquetFunction ψ hϖ Φ (Iwasawa.torus ϖ μ)) := by
  unfold jacquetFunction
  rw [torus_eq_swapRank_blockSum] at hi ⊢
  simp_rw [jacquetIntegrandAt_degreePiece_swap ψ hϖ hΦ]
  apply hasSum_integral_ite _ hi
  intro e
  set h₁ : Langlands.GeneralLinear (r + 1) K.Carrier := Iwasawa.torus ϖ fun i : Fin (r + 1) =>
    μ (Fin.cast (Nat.add_comm (t + 1) (r + 1)) (i.natAdd (t + 1))) with hh₁
  set h₂ : Langlands.GeneralLinear (t + 1) K.Carrier := Iwasawa.torus ϖ fun j : Fin (t + 1) =>
    μ (Fin.cast (Nat.add_comm (t + 1) (r + 1)) (j.castAdd (r + 1))) with hh₂
  have hcont := continuous_of_isLatticePeriodic K
    (isLatticePeriodic_translatedLower hϖ (isLeviInvariant_degreePiece hϖ e hΦ) h₁ h₂)
  have hm := (hcont.measurable.comp (rectangularConj h₂ h₁).measurable).aestronglyMeasurable
    (μ := matrixHaar K (t + 1) (r + 1))
  have hk := (continuous_intertwiningJacquetKernel ψ).aestronglyMeasurable
    (μ := matrixHaar K (t + 1) (r + 1))
  have h := hk.mul hm
  convert h using 1
  rw [← jacquetIntegrandAt_degreePiece_swap ψ hϖ hΦ e h₂ h₁,
    jacquetIntegrandAt_swap ψ hϖ (isLeviInvariant_degreePiece hϖ e hΦ)]
  rfl

/-- The piece decomposition at every point, for a Levi-invariant `Φ` that is Levi-equivariant for
the standard characters and whose Jacquet integrands are integrable at every torus point. -/
theorem hasSum_jacquetFunction_degreePiece (hΦ : IsLeviInvariant Φ)
    (hθ : IsLeviEquivariant (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ r)
      (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t) Φ)
    (hint : ∀ μ : Fin ((r + 1) + (t + 1)) → ℤ,
      Integrable (jacquetIntegrandAt ψ hϖ Φ (Iwasawa.torus ϖ μ)) (matrixHaar K (t + 1) (r + 1)))
    (g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    HasSum (fun e : ℤ => jacquetFunction ψ hϖ (degreePiece hϖ e Φ) g)
      (jacquetFunction ψ hϖ Φ g) := by
  obtain ⟨u, hu, μ, k, hk, rfl⟩ := Iwasawa.exists_iwasawa (n := r + 1 + t) hϖ g
  have h := (hasSum_jacquetFunction_degreePiece_torus ψ hϖ hΦ μ (hint μ)).mul_left
    (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ (r + 1 + t) ⟨u, hu⟩ : ℂ)
  rw [jacquetFunction_mul_integral ψ hϖ hΦ _ k hk,
    jacquetFunction_unipotent_mul ψ hϖ hΦ hθ ⟨u, hu⟩]
  convert h using 2 with e
  rw [jacquetFunction_mul_integral ψ hϖ (isLeviInvariant_degreePiece hϖ e hΦ) _ k hk,
    jacquetFunction_unipotent_mul ψ hϖ (isLeviInvariant_degreePiece hϖ e hΦ)
      (isLeviEquivariant_degreePiece hϖ e hθ) ⟨u, hu⟩]

end Decomposition

section Graded

include hϖ in
/-- **The graded Shintani identity, numerically.** For `ψ` of conductor `𝒪` and fixed `(a, c, s)`
there is `r₀ > 0` such
that for `‖X‖ < r₀` and every `g`,
`∑_e X^e J_e(g) = J_(X a)(1) · W°(g; χ(X a, c, s))`, where `J_e` is the Jacquet function of the
degree-`e` piece of the section with parameters `(a, c, s)`. -/
theorem exists_hasSum_degreePiece (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ X : ℂˣ, ‖(X : ℂ)‖ < r₀ →
      ∀ g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier,
        HasSum (fun e : ℤ => (X : ℂ) ^ e *
            jacquetFunction ψ hϖ (degreePiece hϖ e (Base.fullΦ ψ hϖ a c s)) g)
          (jacquetFunction ψ hϖ (Base.fullΦ ψ hϖ (fun i => X * a i) c s) 1 *
            GeneralLinear.Spherical.sphericalWhittaker (n := r + 1 + t) hϖ
              (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ (r + 1 + t))
              K.canonicalTopologicalData.residueCardinality
              (sectionParameter K (fun i => X * a i) c s) g) := by
  obtain ⟨r₀, hr₀, hint⟩ := exists_integrable_jacquetIntegrandAt_fullΦ ψ hϖ hψ a c s
  refine ⟨r₀, hr₀, fun X hX g => ?_⟩
  have hΦ := Base.isLeviInvariant_fullΦ hϖ hψ (fun i => X * a i) c s
  have hθ := isLeviEquivariant_fullΦ hϖ hψ (fun i => X * a i) c s
  have hsh := jacquetFunction_fullΦ_eq_smul ψ hϖ hψ (fun i => X * a i) c s (hint X hX)
  have hg := congrFun hsh g
  rw [Pi.smul_apply, smul_eq_mul] at hg
  rw [← hg]
  have h := hasSum_jacquetFunction_degreePiece ψ hϖ hΦ hθ (hint X hX) g
  convert h using 2 with e
  rw [jacquetFunction_degreePiece_smul ψ hϖ hψ]

end Graded

end Langlands.Shahidi.OpenCell
