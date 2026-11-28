import Langlands.Representation.Shahidi.OpenCellBaseLift
import Langlands.Representation.Shahidi.OpenCellColumn
import Langlands.Representation.RankinSelberg.UnramifiedWhittakerCells

/-! # The open-cell integral for the `(1, n)` parabolic: setup

For an integral matrix `Z`, `lower(Y + Z) = lower(Y) lower(Z)` with `lower(Z)` integral, so the
depth and the lift of a Levi-invariant function at `lower(Y)` are unchanged by integral
translations of `Y`. Further: the shell functions
`Φ_(d, Ψ)(m₁, m₂) = [|m₁| = q^(-d)] Ψ(m₂)`, the integrands `Y ↦ F(lower Y) conj ψ(Y_last)` of
their lifts `F`, the support of these lifts on one depth shell, and (for `ψ` of conductor `𝒪`)
the vanishing of Whittaker-type functions at torus points that are not antitone. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open Langlands.GeneralLinear Langlands.Conductor MeasureTheory
open scoped NNReal

universe u

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}

local instance ocBaseStepTopologicalSpace : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
local instance ocBaseStepValuativeRel : ValuativeRel K.Carrier := K.canonicalTopologicalData.valuativeRel
local instance ocBaseStepIsNonarchimedeanLocalField : IsNonarchimedeanLocalField K.Carrier := K.canonicalTopologicalData.localField
local instance ocBaseStepTSpace : T2Space K.Carrier := K.canonicalTopologicalData.fieldT2
local instance ocBaseStepSecondCountableTopology : SecondCountableTopology K.Carrier :=
  K.canonicalTopologicalData.secondCountableTopology
local instance ocBaseStepMeasurableSpace : MeasurableSpace K.Carrier := borel K.Carrier
local instance ocBaseStepBorelSpace : BorelSpace K.Carrier := ⟨rfl⟩

section General

variable {r t : ℕ}

theorem lower_mem_integralSubgroup (Z : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier)
    (hZ : Z ∈ integralMatrices K (t + 1) (r + 1)) :
    lower (r + 1) (t + 1) K.Carrier Z ∈
      integralSubgroup K.canonicalTopologicalData.Integers (r + 1 + t) := by
  have hZ' := (mem_integralMatrices_iff K _ _ Z).1 hZ
  have key : ∀ W : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier,
      (∀ i j, W i j ∈ K.canonicalTopologicalData.Integers) →
      ∀ i j, lower (r + 1) (t + 1) K.Carrier W i j ∈ K.canonicalTopologicalData.Integers := by
    intro W hW i j
    refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i <;>
      refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
    · rw [lower_first_first]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · rw [lower_first_second]
      exact zero_mem _
    · rw [lower_second_first]
      exact hW _ _
    · rw [lower_second_second]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
  refine (mem_integralSubgroup _ _ _).2 ⟨key Z hZ', ?_⟩
  rw [lower_inv]
  exact key (-Z) fun i j => neg_mem (hZ' i j)

variable {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
    (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)

theorem openCellDepth_add_integral (Y Z : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier)
    (hZ : Z ∈ integralMatrices K (t + 1) (r + 1)) :
    openCellDepth hϖ (Y + Z) = openCellDepth hϖ Y := by
  unfold openCellDepth openCellExponent
  rw [lower_add, Iwasawa.exponent_mul_integral hϖ _ (lower_mem_integralSubgroup Z hZ)]

theorem liftFunction_lower_add_integral
    {Φ : Langlands.GeneralLinear (r + 1) K.Carrier → Langlands.GeneralLinear (t + 1) K.Carrier → ℂ}
    (hΦ : IsLeviInvariant Φ) (Y Z : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier)
    (hZ : Z ∈ integralMatrices K (t + 1) (r + 1)) :
    liftFunction hϖ Φ (lower (r + 1) (t + 1) K.Carrier (Y + Z)) =
      liftFunction hϖ Φ (lower (r + 1) (t + 1) K.Carrier Y) := by
  rw [lower_add, liftFunction_mul_integral hϖ hΦ _ _ (lower_mem_integralSubgroup Z hZ)]

end General

namespace Base

variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _
  K.canonicalTopologicalData.topology)

/-- A function on `GL_(t+1)(K)` of Whittaker type for the standard character of `ψ`: left
`(N, θ_ψ)`-equivariant and right invariant under `GL_(t+1)(𝒪)`. -/
def IsWhittakerType {t : ℕ} (Ψ : Langlands.GeneralLinear (t + 1) K.Carrier → ℂ) : Prop :=
  (∀ (u : upperUnipotent (t + 1) K.Carrier) g,
      Ψ (u.val * g) = (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t u : ℂ) *
        Ψ g) ∧
    ∀ g, ∀ k ∈ integralSubgroup K.canonicalTopologicalData.Integers t, Ψ (g * k) = Ψ g

variable {t : ℕ}

/-- The shell Levi function `Φ_(d, Ψ)(m₁, m₂) = [|det m₁| = q^(-d)] Ψ(m₂)`. -/
def shellΦ (d : ℤ) (Ψ : Langlands.GeneralLinear (t + 1) K.Carrier → ℂ)
    (m₁ : Langlands.GeneralLinear (0 + 1) K.Carrier) (m₂ : Langlands.GeneralLinear (t + 1) K.Carrier) :
    ℂ :=
  if ((K.canonicalTopologicalData.determinantNorm (0 + 1) m₁ : ℝ≥0) : ℝ) =
      (K.canonicalTopologicalData.residueCardinality : ℝ) ^ (-d) then Ψ m₂ else 0

theorem determinantNorm_mul_integral' {n : ℕ} (m μ : Langlands.GeneralLinear (n + 1) K.Carrier)
    (hμ : μ ∈ integralSubgroup K.canonicalTopologicalData.Integers n) :
    K.canonicalTopologicalData.determinantNorm (n + 1) (m * μ) =
      K.canonicalTopologicalData.determinantNorm (n + 1) m := by
  obtain ⟨h1, h2⟩ := (mem_integralSubgroup _ _ _).1 hμ
  rw [map_mul, Langlands.Unramified.SphericalExistence.determinantNorm_eq_one_of_integral K
    K.canonicalTopologicalData μ h1 h2, mul_one]

theorem isLeviInvariant_shellΦ (d : ℤ) {Ψ : Langlands.GeneralLinear (t + 1) K.Carrier → ℂ}
    (hΨ : ∀ g, ∀ k ∈ integralSubgroup K.canonicalTopologicalData.Integers t, Ψ (g * k) = Ψ g) :
    IsLeviInvariant (shellΦ (K := K) d Ψ) := by
  intro m₁ μ₁ m₂ μ₂ hμ₁ hμ₂
  simp only [shellΦ, determinantNorm_mul_integral' m₁ μ₁ hμ₁, hΨ m₂ μ₂ hμ₂]

variable {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
    (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)

/-- The integrand `Y ↦ F(lower Y) conj ψ(Y_last)` for the lift `F` of `Φ_(d, Ψ)`. -/
def baseIntegrand (d : ℤ) (Ψ : Langlands.GeneralLinear (t + 1) K.Carrier → ℂ)
    (Y : Matrix (Fin (t + 1)) (Fin 1) K.Carrier) : ℂ :=
  liftFunction hϖ (shellΦ d Ψ) (lower (0 + 1) (t + 1) K.Carrier Y) *
    starRingEnd ℂ (ψ (Y (Fin.last t) 0) : ℂ)

theorem zpow_residue_injective {a b : ℤ}
    (h : (K.canonicalTopologicalData.residueCardinality : ℝ) ^ a =
      (K.canonicalTopologicalData.residueCardinality : ℝ) ^ b) : a = b := by
  have hq : (1 : ℝ) < K.canonicalTopologicalData.residueCardinality := by
    exact_mod_cast K.canonicalTopologicalData.residueCardinality_gt_one
  exact zpow_right_injective₀ (by linarith) hq.ne' h

/-- For `Ψ` right invariant under `GL_(t+1)(𝒪)`, the lift of `Φ_(d, Ψ)` vanishes on `lower Y`
unless `Y` has depth `d`. -/
theorem liftFunction_shellΦ_eq_zero (d : ℤ) {Ψ : Langlands.GeneralLinear (t + 1) K.Carrier → ℂ}
    (hΨ : ∀ g, ∀ k ∈ integralSubgroup K.canonicalTopologicalData.Integers t, Ψ (g * k) = Ψ g)
    (Y : Matrix (Fin (t + 1)) (Fin 1) K.Carrier) (hY : openCellDepth hϖ Y ≠ d) :
    liftFunction hϖ (shellΦ d Ψ) (lower (0 + 1) (t + 1) K.Carrier Y) = 0 := by
  obtain ⟨u₁, hu₁, u₂, hu₂, h⟩ := liftFunction_lower hϖ (isLeviInvariant_shellΦ d hΨ) Y
  rw [h, shellΦ, determinantNorm_unipotent_mul_torus K hϖ hu₁]
  split_ifs with heq
  · exfalso
    apply hY
    have := zpow_residue_injective heq
    rw [openCellDepth]
    linarith
  · rfl

variable {ψ}

include hϖ in
theorem standardCharacter_nondegenerate' (hψ : HasIntegerConductor ψ) (i : Fin t) :
    ∃ x : K.Carrier, @ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel x *
        @ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel (ϖ : K.Carrier) ≤ 1 ∧
      @Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t
        (Whittaker.UpperUnipotentCharacter.adjacentUnit i x) ≠ 1 := by
  obtain ⟨x, hx, hne⟩ := RankinSelberg.UnramifiedWhittaker.standardCharacter_nondegenerate K ψ hψ i
  refine ⟨x, ?_, hne⟩
  have h0 : Iwasawa.IsUniformizingElement (ValuativeRel.valuation K.Carrier)
      (LocalFactor.PadicAbelian.uniformizerUnit K.canonicalTopologicalData) :=
    Langlands.Unramified.uniformizerUnit_isUniformizingElement K
  have hv := RankinSelberg.UnramifiedPairTorus.valuation_eq_of_isUniformizingElement
    (ValuativeRel.valuation K.Carrier) h0 hϖ
  rw [hv]
  exact hx

include hϖ in
/-- For `ψ` of conductor `𝒪`, a function of Whittaker type vanishes at non-antitone torus
points. -/
theorem whittaker_torus_eq_zero (hψ : HasIntegerConductor ψ)
    {Ψ : Langlands.GeneralLinear (t + 1) K.Carrier → ℂ} (hΨ : IsWhittakerType ψ Ψ)
    {ν : Fin (t + 1) → ℤ} (hν : ¬ Antitone ν) : Ψ (Iwasawa.torus ϖ ν) = 0 :=
  RankinSelberg.UnramifiedWhittaker.eval_torus_eq_zero_of_not_antitone hϖ hΨ.1 hΨ.2
    (fun i => standardCharacter_nondegenerate' hϖ hψ i) hν

end Base

end Langlands.Shahidi.OpenCell
