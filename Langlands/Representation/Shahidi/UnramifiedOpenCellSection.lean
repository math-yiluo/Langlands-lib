import Langlands.Representation.Shahidi.UnramifiedOpenCellSumStatement
import Langlands.Representation.Unramified.TwoBlockSphericalIntegration
import Langlands.Representation.RankinSelberg.HighlyRamified.EssentialInput

/-! # The normalized spherical section of the two-block induced representation

Over a `p`-adic field `K`, every element of `GL_((r+1)+(t+1))(K)` is the product of an element
of the upper two-block parabolic and an integral matrix, and the Levi part of the parabolic
factor is determined up to right multiplication by integral Levi matrices. This module
defines the function `sectionFunction` with the transformation law of
`Shahidi.UnramifiedOpenCellSumStatement`. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.Shahidi.UnramifiedSection

open Langlands.GeneralLinear

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p) (r t : ℕ)

/-- The upper two-block shape with blocks of sizes `r + 1` and `t + 1`. -/
abbrev shape : BlockShape ((r + 1) + (t + 1)) :=
  twoBlocks (r + 1) (t + 1) (Nat.succ_pos r) (Nat.succ_pos t)

/-- The integral matrices `GL_((r+1)+(t+1))(𝒪)` of the canonical valuation. -/
abbrev integralGroup : Subgroup (Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :=
  Langlands.Conductor.integralSubgroup K.canonicalTopologicalData.Integers (r + 1 + t)

/-- An upper triangular matrix lies in the upper two-block parabolic. -/
theorem mem_parabolic_of_upperTriangular (g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier)
    (hg : ∀ i j, j < i → g i j = 0) : g ∈ (shape r t).parabolic K.Carrier := by
  rw [twoBlocks_mem_parabolic_iff]
  intro i j
  apply hg
  rw [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
  omega

/-- The integral matrices with integral inverse, as entry conditions. -/
theorem mem_integralGroup_iff (k : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    k ∈ integralGroup K r t ↔
      (∀ i j, k i j ∈ K.canonicalTopologicalData.Integers) ∧
        (∀ i j, k⁻¹ i j ∈ K.canonicalTopologicalData.Integers) :=
  Langlands.Conductor.mem_integralSubgroup _ _ _

/-- Every element of `GL_((r+1)+(t+1))(K)` is a parabolic element times an integral matrix. -/
theorem exists_parabolic_mul {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
      (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)
    (x : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    ∃ g ∈ (shape r t).parabolic K.Carrier, ∃ k ∈ integralGroup K r t, x = g * k := by
  obtain ⟨u, hu, lam, k, hk, hx⟩ := Iwasawa.exists_iwasawa (n := r + 1 + t) hϖ x
  refine ⟨u * Iwasawa.torus ϖ lam, mem_parabolic_of_upperTriangular K r t _ ?_, k, hk, hx⟩
  intro i j hij
  change (u.val * (Iwasawa.torus ϖ lam).val) i j = 0
  rw [Iwasawa.torus, Iwasawa.diagonalUnits_val, Matrix.mul_diagonal, hu.1 hij, zero_mul]

/-- The first diagonal block of a parabolic element. -/
def leviFirst (g : (shape r t).parabolic K.Carrier) : Langlands.GeneralLinear (r + 1) K.Carrier :=
  (twoBlockLeviEquiv (Nat.succ_pos r) (Nat.succ_pos t) K.Carrier
    ((shape r t).leviProjection K.Carrier g)).1

/-- The second diagonal block of a parabolic element. -/
def leviSecond (g : (shape r t).parabolic K.Carrier) : Langlands.GeneralLinear (t + 1) K.Carrier :=
  (twoBlockLeviEquiv (Nat.succ_pos r) (Nat.succ_pos t) K.Carrier
    ((shape r t).leviProjection K.Carrier g)).2

theorem leviFirst_apply (g : (shape r t).parabolic K.Carrier) (a b : Fin (r + 1)) :
    leviFirst K r t g a b = g.val (a.castAdd (t + 1)) (b.castAdd (t + 1)) :=
  twoBlocks_leviProjection_first _ _ K.Carrier g a b

theorem leviSecond_apply (g : (shape r t).parabolic K.Carrier) (a b : Fin (t + 1)) :
    leviSecond K r t g a b = g.val (a.natAdd (r + 1)) (b.natAdd (r + 1)) :=
  twoBlocks_leviProjection_second _ _ K.Carrier g a b

theorem leviFirst_mul (g h : (shape r t).parabolic K.Carrier) :
    leviFirst K r t (g * h) = leviFirst K r t g * leviFirst K r t h := by
  simp [leviFirst, map_mul]

theorem leviSecond_mul (g h : (shape r t).parabolic K.Carrier) :
    leviSecond K r t (g * h) = leviSecond K r t g * leviSecond K r t h := by
  simp [leviSecond, map_mul]

theorem leviFirst_inv (g : (shape r t).parabolic K.Carrier) :
    leviFirst K r t g⁻¹ = (leviFirst K r t g)⁻¹ := by
  simp [leviFirst, map_inv]

theorem leviSecond_inv (g : (shape r t).parabolic K.Carrier) :
    leviSecond K r t g⁻¹ = (leviSecond K r t g)⁻¹ := by
  simp [leviSecond, map_inv]

/-- The diagonal blocks of an integral parabolic element are integral. -/
theorem levi_mem_integral (g : (shape r t).parabolic K.Carrier)
    (hg : (g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) ∈ integralGroup K r t) :
    leviFirst K r t g ∈
        Langlands.Conductor.integralSubgroup K.canonicalTopologicalData.Integers r ∧
      leviSecond K r t g ∈
        Langlands.Conductor.integralSubgroup K.canonicalTopologicalData.Integers t := by
  obtain ⟨h1, h2⟩ := (mem_integralGroup_iff K r t _).1 hg
  constructor
  · refine (Langlands.Conductor.mem_integralSubgroup _ _ _).2 ⟨fun a b => ?_, fun a b => ?_⟩
    · rw [leviFirst_apply]
      exact h1 _ _
    · rw [← leviFirst_inv, leviFirst_apply]
      exact h2 _ _
  · refine (Langlands.Conductor.mem_integralSubgroup _ _ _).2 ⟨fun a b => ?_, fun a b => ?_⟩
    · rw [leviSecond_apply]
      exact h1 _ _
    · rw [← leviSecond_inv, leviSecond_apply]
      exact h2 _ _

/-- The upper radical matrix `u(X)` as an element of the parabolic. -/
def upperP (X : Matrix (Fin (r + 1)) (Fin (t + 1)) K.Carrier) : (shape r t).parabolic K.Carrier :=
  ⟨upper (r + 1) (t + 1) K.Carrier X, by
    rw [twoBlocks_mem_parabolic_iff]
    intro i j
    exact upper_second_first _ _ _ X i j⟩

/-- The block-diagonal matrix `diag(m₁, m₂)` as an element of the parabolic. -/
def leviP (m₁ : Langlands.GeneralLinear (r + 1) K.Carrier)
    (m₂ : Langlands.GeneralLinear (t + 1) K.Carrier) : (shape r t).parabolic K.Carrier :=
  (shape r t).leviInParabolic K.Carrier
    ((twoBlockLeviEquiv (Nat.succ_pos r) (Nat.succ_pos t) K.Carrier).symm (m₁, m₂))

theorem leviP_val (m₁ : Langlands.GeneralLinear (r + 1) K.Carrier)
    (m₂ : Langlands.GeneralLinear (t + 1) K.Carrier) :
    (leviP K r t m₁ m₂ : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) =
      GeneralLinear.blockSum (m₁, m₂) := by
  rw [leviP, BlockShape.leviInParabolic_val, twoBlocks_leviEmbedding]
  rfl

theorem leviFirst_leviP (m₁ : Langlands.GeneralLinear (r + 1) K.Carrier)
    (m₂ : Langlands.GeneralLinear (t + 1) K.Carrier) : leviFirst K r t (leviP K r t m₁ m₂) = m₁ := by
  simp [leviFirst, leviP, BlockShape.leviProjection_section]

theorem leviSecond_leviP (m₁ : Langlands.GeneralLinear (r + 1) K.Carrier)
    (m₂ : Langlands.GeneralLinear (t + 1) K.Carrier) : leviSecond K r t (leviP K r t m₁ m₂) = m₂ := by
  simp [leviSecond, leviP, BlockShape.leviProjection_section]

theorem leviFirst_upperP (X : Matrix (Fin (r + 1)) (Fin (t + 1)) K.Carrier) :
    leviFirst K r t (upperP K r t X) = 1 := by
  apply Units.ext
  funext a b
  rw [leviFirst_apply]
  simp only [upperP, upper_first_first, Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply]

theorem leviSecond_upperP (X : Matrix (Fin (r + 1)) (Fin (t + 1)) K.Carrier) :
    leviSecond K r t (upperP K r t X) = 1 := by
  apply Units.ext
  funext a b
  rw [leviSecond_apply]
  simp only [upperP, upper_second_second, Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply]

section Values

variable {K r t}
variable {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
    (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _ K.canonicalTopologicalData.topology)
  (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ)

/-- The value `δ_P(m₁, m₂)^(1/2 + s/(r+t+2)) W°(m₁; a) W°(m₂; c)` of the normalized
spherical section on the Levi element `diag(m₁, m₂)`. -/
def leviValue (m₁ : Langlands.GeneralLinear (r + 1) K.Carrier)
    (m₂ : Langlands.GeneralLinear (t + 1) K.Carrier) : ℂ :=
  ((twoBlockModulus K m₁ m₂ : ℝ) : ℂ) ^ ((1 : ℂ) / 2 + s / ((r + t + 2 : ℕ) : ℂ)) *
    GeneralLinear.Spherical.sphericalWhittaker (n := r) hϖ
      (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ r)
      K.canonicalTopologicalData.residueCardinality a m₁ *
    GeneralLinear.Spherical.sphericalWhittaker (n := t) hϖ
      (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t)
      K.canonicalTopologicalData.residueCardinality c m₂

theorem determinantNorm_mul_integral {n : ℕ} (m μ : Langlands.GeneralLinear (n + 1) K.Carrier)
    (hμ : μ ∈ Langlands.Conductor.integralSubgroup K.canonicalTopologicalData.Integers n) :
    K.canonicalTopologicalData.determinantNorm (n + 1) (m * μ) =
      K.canonicalTopologicalData.determinantNorm (n + 1) m := by
  obtain ⟨h1, h2⟩ := (Langlands.Conductor.mem_integralSubgroup _ _ _).1 hμ
  rw [map_mul, Langlands.Unramified.SphericalExistence.determinantNorm_eq_one_of_integral K
    K.canonicalTopologicalData μ h1 h2, mul_one]

theorem twoBlockModulus_mul_integral (m₁ μ₁ : Langlands.GeneralLinear (r + 1) K.Carrier)
    (m₂ μ₂ : Langlands.GeneralLinear (t + 1) K.Carrier)
    (hμ₁ : μ₁ ∈ Langlands.Conductor.integralSubgroup K.canonicalTopologicalData.Integers r)
    (hμ₂ : μ₂ ∈ Langlands.Conductor.integralSubgroup K.canonicalTopologicalData.Integers t) :
    twoBlockModulus K (m₁ * μ₁) (m₂ * μ₂) = twoBlockModulus K m₁ m₂ := by
  rw [twoBlockModulus, twoBlockModulus, determinantNorm_mul_integral m₁ μ₁ hμ₁,
    determinantNorm_mul_integral m₂ μ₂ hμ₂]

variable {ψ} in
theorem isIntegrallyTrivial_of_conductor (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (n : ℕ) :
    Iwasawa.IsIntegrallyTrivial
      (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel)
      (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ n) := by
  let := K.canonicalTopologicalData.topology
  let := K.canonicalTopologicalData.valuativeRel
  exact GeneralLinear.Iwasawa.isIntegrallyTrivial_standardCharacter
    (RankinSelberg.HighlyRamified.hasIntegerConductor_of_additiveConductor_eq_zero K ψ hψ).1 n

variable {ψ} in
theorem leviValue_mul_integral (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (m₁ μ₁ : Langlands.GeneralLinear (r + 1) K.Carrier)
    (m₂ μ₂ : Langlands.GeneralLinear (t + 1) K.Carrier)
    (hμ₁ : μ₁ ∈ Langlands.Conductor.integralSubgroup K.canonicalTopologicalData.Integers r)
    (hμ₂ : μ₂ ∈ Langlands.Conductor.integralSubgroup K.canonicalTopologicalData.Integers t) :
    leviValue hϖ ψ a c s (m₁ * μ₁) (m₂ * μ₂) = leviValue hϖ ψ a c s m₁ m₂ := by
  rw [leviValue, leviValue, twoBlockModulus_mul_integral m₁ μ₁ m₂ μ₂ hμ₁ hμ₂,
    GeneralLinear.Spherical.sphericalWhittaker_mul_integral hϖ _ _
      (isIntegrallyTrivial_of_conductor hψ r) m₁ hμ₁,
    GeneralLinear.Spherical.sphericalWhittaker_mul_integral hϖ _ _
      (isIntegrallyTrivial_of_conductor hψ t) m₂ hμ₂]

end Values

section Section

variable {K r t}
variable {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
    (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _ K.canonicalTopologicalData.topology)
  (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ)

/-- The normalized spherical section: its value at `x = g k`, with `g` in the upper two-block
parabolic and `k` integral, is `leviValue` of the diagonal blocks of `g`. -/
def sectionFunction (x : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) : ℂ :=
  leviValue hϖ ψ a c s
    (leviFirst K r t ⟨(exists_parabolic_mul K r t hϖ x).choose,
      (exists_parabolic_mul K r t hϖ x).choose_spec.1⟩)
    (leviSecond K r t ⟨(exists_parabolic_mul K r t hϖ x).choose,
      (exists_parabolic_mul K r t hϖ x).choose_spec.1⟩)

variable {ψ} in
theorem sectionFunction_parabolic_mul (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (g : (shape r t).parabolic K.Carrier) (k : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier)
    (hk : k ∈ integralGroup K r t) :
    sectionFunction hϖ ψ a c s (g.val * k) =
      leviValue hϖ ψ a c s (leviFirst K r t g) (leviSecond K r t g) := by
  obtain ⟨hg₀, k₀, hk₀, hx⟩ := (exists_parabolic_mul K r t hϖ (g.val * k)).choose_spec
  set g₀ : (shape r t).parabolic K.Carrier :=
    ⟨(exists_parabolic_mul K r t hϖ (g.val * k)).choose, hg₀⟩ with hg₀def
  have hx' : g.val * k = g₀.val * k₀ := hx
  have hd : ((g⁻¹ * g₀ : (shape r t).parabolic K.Carrier) :
      Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) ∈ integralGroup K r t := by
    have e : ((g⁻¹ * g₀ : (shape r t).parabolic K.Carrier) :
        Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) = k * k₀⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      calc g.val⁻¹ * g₀.val = g.val⁻¹ * (g₀.val * k₀) * k₀⁻¹ := by group
        _ = g.val⁻¹ * (g.val * k) * k₀⁻¹ := by rw [hx']
        _ = k * k₀⁻¹ := by group
    rw [e]
    exact mul_mem hk (inv_mem hk₀)
  obtain ⟨h1, h2⟩ := levi_mem_integral K r t _ hd
  have e1 : leviFirst K r t g₀ = leviFirst K r t g * leviFirst K r t (g⁻¹ * g₀) := by
    rw [← leviFirst_mul, mul_inv_cancel_left]
  have e2 : leviSecond K r t g₀ = leviSecond K r t g * leviSecond K r t (g⁻¹ * g₀) := by
    rw [← leviSecond_mul, mul_inv_cancel_left]
  change leviValue hϖ ψ a c s (leviFirst K r t g₀) (leviSecond K r t g₀) = _
  rw [e1, e2, leviValue_mul_integral hϖ a c s hψ _ _ _ _ h1 h2]

variable {ψ} in
/-- The transformation law of `Shahidi.UnramifiedOpenCellSumStatement`. -/
theorem sectionFunction_law (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (X : Matrix (Fin (r + 1)) (Fin (t + 1)) K.Carrier)
    (m₁ : Langlands.GeneralLinear (r + 1) K.Carrier) (m₂ : Langlands.GeneralLinear (t + 1) K.Carrier)
    (k : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) (hk : k ∈ integralGroup K r t) :
    sectionFunction hϖ ψ a c s (upper (r + 1) (t + 1) K.Carrier X * GeneralLinear.blockSum (m₁, m₂) * k) =
      leviValue hϖ ψ a c s m₁ m₂ := by
  have e : upper (r + 1) (t + 1) K.Carrier X * GeneralLinear.blockSum (m₁, m₂) =
      ((upperP K r t X * leviP K r t m₁ m₂ : (shape r t).parabolic K.Carrier) :
        Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) := by
    rw [Subgroup.coe_mul, leviP_val]
    rfl
  rw [e, sectionFunction_parabolic_mul hϖ a c s hψ _ k hk, leviFirst_mul, leviSecond_mul,
    leviFirst_upperP, leviSecond_upperP, leviFirst_leviP, leviSecond_leviP, one_mul, one_mul]

variable {ψ} in
theorem leviValue_one (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0) :
    leviValue hϖ ψ a c s 1 1 = 1 := by
  rw [leviValue, GeneralLinear.Spherical.sphericalWhittaker_one hϖ _ _
      (isIntegrallyTrivial_of_conductor hψ r),
    GeneralLinear.Spherical.sphericalWhittaker_one hϖ _ _
      (isIntegrallyTrivial_of_conductor hψ t)]
  simp [twoBlockModulus]

variable {ψ} in
/-- The section is right invariant under the integral matrices. -/
theorem sectionFunction_mul_integral (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (x k : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) (hk : k ∈ integralGroup K r t) :
    sectionFunction hϖ ψ a c s (x * k) = sectionFunction hϖ ψ a c s x := by
  obtain ⟨hg₀, k₀, hk₀, hx⟩ := (exists_parabolic_mul K r t hϖ x).choose_spec
  set g₀ : (shape r t).parabolic K.Carrier :=
    ⟨(exists_parabolic_mul K r t hϖ x).choose, hg₀⟩ with hg₀def
  have hx' : x = g₀.val * k₀ := hx
  have e : x * k = g₀.val * (k₀ * k) := by rw [hx', mul_assoc]
  rw [e, sectionFunction_parabolic_mul hϖ a c s hψ g₀ _ (mul_mem hk₀ hk)]
  rfl

variable {ψ} in
theorem sectionFunction_integral (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (k : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) (hk : k ∈ integralGroup K r t) :
    sectionFunction hϖ ψ a c s k = 1 := by
  have e : k = ((1 : (shape r t).parabolic K.Carrier) :
      Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) * k := by
    rw [OneMemClass.coe_one, one_mul]
  rw [e, sectionFunction_parabolic_mul hϖ a c s hψ 1 k hk]
  simp only [leviFirst, leviSecond, map_one]
  exact leviValue_one hϖ a c s hψ

end Section

end Langlands.Shahidi.UnramifiedSection
