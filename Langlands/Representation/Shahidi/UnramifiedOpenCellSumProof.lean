import Langlands.Representation.Shahidi.OpenCellInduction

/-! # Proof of the unramified value of the two-block open-cell sum

The twist `δ_P^(s/N)` of the two-block section is absorbed into the parameters: the section
with parameters `(a, c, s)` equals the section with parameters
`(q^(-s(t+1)/N) a, q^(s(r+1)/N) c, 0)`, `N = r + t + 2`, and the pair parameters agree. The shell
identities at `s = 0` therefore give the shell identities for every `s`, and these give
`Langlands.Shahidi.UnramifiedOpenCellSumStatement`. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open Langlands.GeneralLinear Langlands.Conductor Langlands.GeneralLinear.Spherical
open Langlands.GeneralLinear.Iwasawa MeasureTheory
open scoped ENNReal NNReal

universe u

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}

local instance ocProofTopologicalSpace : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology
local instance ocProofValuativeRel : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel
local instance ocProofLocalField : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField
local instance ocProofT2Space : T2Space K.Carrier := K.canonicalTopologicalData.fieldT2
local instance ocProofSecondCountableTopology : SecondCountableTopology K.Carrier :=
  K.canonicalTopologicalData.secondCountableTopology
local instance ocProofMeasurableSpace : MeasurableSpace K.Carrier := borel K.Carrier
local instance ocProofBorelSpace : BorelSpace K.Carrier := ⟨rfl⟩

variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _
  K.canonicalTopologicalData.topology)
variable {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
    (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)

section Twist

variable {r t : ℕ}

/-- The first twisted parameters `q^(-s(t+1)/N) a`. -/
def twistFirst (a : Fin (r + 1) → ℂˣ) (s : ℂ) : Fin (r + 1) → ℂˣ :=
  fun i => residuePowUnit K (-(s * ((t + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ))) * a i

/-- The second twisted parameters `q^(s(r+1)/N) c`. -/
def twistSecond (c : Fin (t + 1) → ℂˣ) (s : ℂ) : Fin (t + 1) → ℂˣ :=
  fun j => residuePowUnit K (s * ((r + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ)) * c j

include hϖ in
/-- **The twist is absorbed into the parameters**, for `ψ` of conductor `𝒪`. -/
theorem fullΦ_twist (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ) :
    Base.fullΦ ψ hϖ a c s =
      Base.fullΦ ψ hϖ (twistFirst (K := K) (t := t) a s) (twistSecond (K := K) (r := r) c s) 0 := by
  funext m₁ m₂
  set q := K.canonicalTopologicalData.residueCardinality with hq
  have hq0 : 0 < q := residueCardinality_pos K
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
  unfold twistFirst twistSecond
  simp only [Base.fullΦ]
  rw [sphericalWhittaker_smul_eq ψ hϖ hψ, sphericalWhittaker_smul_eq ψ hϖ hψ]
  set v₁ := detExponent hϖ m₁
  set v₂ := detExponent hϖ m₂
  have hδ : twoBlockModulus K m₁ m₂ = (q : ℝ) ^ (((r + 1 : ℕ) : ℤ) * v₂ - ((t + 1 : ℕ) : ℤ) * v₁) := by
    rw [twoBlockModulus, determinantNorm_eq_zpow hϖ m₁, determinantNorm_eq_zpow hϖ m₂,
      ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_sub₀ hqR]
    congr 1
    push_cast
    ring
  have hE : (((q : ℝ) ^ (((r + 1 : ℕ) : ℤ) * v₂ - ((t + 1 : ℕ) : ℤ) * v₁) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (zpow_ne_zero _ hqR)
  rw [hδ, zero_div, add_zero, Complex.cpow_add _ _ hE,
    Base.natCast_cpow_eq q hq0 _ (s / ((r + t + 2 : ℕ) : ℂ)), residuePowUnit_val, residuePowUnit_val,
    ← Complex.cpow_int_mul, ← Complex.cpow_int_mul]
  have hsum : (q : ℂ) ^ (((((r + 1 : ℕ) : ℤ) * v₂ - ((t + 1 : ℕ) : ℤ) * v₁ : ℤ) : ℂ) *
      (s / ((r + t + 2 : ℕ) : ℂ))) =
      (q : ℂ) ^ ((v₁ : ℂ) * -(s * ((t + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ))) *
        (q : ℂ) ^ ((v₂ : ℂ) * (s * ((r + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ))) := by
    rw [← Complex.cpow_add _ _ hqC]
    congr 1
    push_cast
    ring
  rw [hsum]
  ring

theorem pairParameter_twist (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ) :
    pairParameter K.canonicalTopologicalData.residueCardinality a c s =
      pairParameter K.canonicalTopologicalData.residueCardinality
        (twistFirst (K := K) (t := t) a s) (twistSecond (K := K) (r := r) c s) 0 := by
  funext x
  set q := K.canonicalTopologicalData.residueCardinality with hq
  have hq0 : 0 < q := residueCardinality_pos K
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  simp only [pairParameter, twistFirst, twistSecond, Units.val_mul, residuePowUnit_val]
  have hN : ((r + t + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : r + t + 2 ≠ 0)
  have h : (q : ℂ) ^ (-(1 + s)) = (q : ℂ) ^ (-(s * ((t + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ))) *
      ((q : ℂ) ^ (s * ((r + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ)))⁻¹ * (q : ℂ) ^ (-(1 + (0 : ℂ))) := by
    rw [← Complex.cpow_neg, ← Complex.cpow_add _ _ hqC, ← Complex.cpow_add _ _ hqC]
    congr 1
    field_simp
    push_cast
    ring
  rw [h]
  ring

end Twist

/-- **The shell identities for all ranks and all `s`.** -/
theorem openCellShellIdentity : OpenCellShellIdentityStatement.{u} := by
  intro r t p _ K ψ hψ ϖ hϖ a c s f hf
  rw [shellIdentity_iff ψ hϖ hψ hf]
  intro D
  rw [fullΦ_twist ψ hϖ hψ a c s, pairParameter_twist a c s]
  exact coreAt_all ψ hϖ hψ r t _ _ D

end Langlands.Shahidi.OpenCell

namespace Langlands.Shahidi

universe u

/-- **The unramified two-block open-cell sum.** The open-cell sum of the unramified two-block
section is `∏_(i,j) (1 - a_i c_j⁻¹ q^(-(1+s)))`, the product over the roots crossing the two
blocks: Shahidi's two-block Jacquet value (Shahidi 1981, proof of Theorem 5.1, p. 352) for
inducing Whittaker functions normalized to `1` at the identity. This normalization removes the
factors of the roots inside the two blocks from the full split `GL_N` product
`∏_(α > 0) (1 - q⁻¹ χ(a_α))` of Casselman–Shalika (1980), Theorem 5.4. -/
theorem unramifiedOpenCellSum : UnramifiedOpenCellSumStatement.{u} :=
  OpenCell.unramifiedOpenCellSum_of_shellIdentity OpenCell.openCellShellIdentity

end Langlands.Shahidi
