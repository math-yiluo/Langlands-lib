import Langlands.Representation.Shahidi.OpenCellValue
import Langlands.Representation.Shahidi.IntertwiningCovariance

/-! # Functions on `GL_((r+1)+(t+1))` lifted from the Levi of the upper two-block parabolic

Every element of `GL_((r+1)+(t+1))(K)` is a product `g k` with `g` in the upper two-block
parabolic `P` and `k` integral, and the Levi part of `g` is determined up to right
multiplication by integral Levi elements. A function `Φ(m₁, m₂)` on the Levi that is right
invariant under integral elements therefore lifts to the function `x ↦ Φ(g₁, g₂)`. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open Langlands.GeneralLinear Langlands.Conductor

universe u

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p) (r t : ℕ)

local instance ocLiftTopologicalSpace : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
local instance ocLiftValuativeRel : ValuativeRel K.Carrier := K.canonicalTopologicalData.valuativeRel
local instance ocLiftIsNonarchimedeanLocalField : IsNonarchimedeanLocalField K.Carrier := K.canonicalTopologicalData.localField

/-- The upper two-block shape with blocks of sizes `r + 1` and `t + 1`. -/
abbrev liftShape : BlockShape ((r + 1) + (t + 1)) :=
  twoBlocks (r + 1) (t + 1) (Nat.succ_pos r) (Nat.succ_pos t)

/-- An upper triangular matrix lies in the upper two-block parabolic. -/
theorem mem_liftShape_parabolic_of_upperTriangular
    (g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier)
    (hg : ∀ i j, j < i → g i j = 0) : g ∈ (liftShape r t).parabolic K.Carrier := by
  rw [twoBlocks_mem_parabolic_iff]
  intro i j
  apply hg
  rw [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
  omega

variable {K} in
/-- Every element of `GL_((r+1)+(t+1))(K)` is a parabolic element times an integral matrix. -/
theorem exists_liftShape_parabolic_mul {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
      (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)
    (x : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    ∃ g ∈ (liftShape r t).parabolic K.Carrier,
      ∃ k ∈ integralSubgroup K.canonicalTopologicalData.Integers (r + 1 + t), x = g * k := by
  obtain ⟨u, hu, lam, k, hk, hx⟩ := Iwasawa.exists_iwasawa (n := r + 1 + t) hϖ x
  refine ⟨u * Iwasawa.torus ϖ lam, mem_liftShape_parabolic_of_upperTriangular K r t _ ?_, k, hk,
    hx⟩
  intro i j hij
  change (u.val * (Iwasawa.torus ϖ lam).val) i j = 0
  rw [Iwasawa.torus, Iwasawa.diagonalUnits_val, Matrix.mul_diagonal, hu.1 hij, zero_mul]

/-- The first diagonal block of a parabolic element. -/
def liftFirst (g : (liftShape r t).parabolic K.Carrier) : Langlands.GeneralLinear (r + 1) K.Carrier :=
  (twoBlockLeviEquiv (Nat.succ_pos r) (Nat.succ_pos t) K.Carrier
    ((liftShape r t).leviProjection K.Carrier g)).1

/-- The second diagonal block of a parabolic element. -/
def liftSecond (g : (liftShape r t).parabolic K.Carrier) :
    Langlands.GeneralLinear (t + 1) K.Carrier :=
  (twoBlockLeviEquiv (Nat.succ_pos r) (Nat.succ_pos t) K.Carrier
    ((liftShape r t).leviProjection K.Carrier g)).2

theorem liftFirst_apply (g : (liftShape r t).parabolic K.Carrier) (a b : Fin (r + 1)) :
    liftFirst K r t g a b = g.val (a.castAdd (t + 1)) (b.castAdd (t + 1)) :=
  twoBlocks_leviProjection_first _ _ K.Carrier g a b

theorem liftSecond_apply (g : (liftShape r t).parabolic K.Carrier) (a b : Fin (t + 1)) :
    liftSecond K r t g a b = g.val (a.natAdd (r + 1)) (b.natAdd (r + 1)) :=
  twoBlocks_leviProjection_second _ _ K.Carrier g a b

theorem liftFirst_mul (g h : (liftShape r t).parabolic K.Carrier) :
    liftFirst K r t (g * h) = liftFirst K r t g * liftFirst K r t h := by
  simp [liftFirst, map_mul]

theorem liftSecond_mul (g h : (liftShape r t).parabolic K.Carrier) :
    liftSecond K r t (g * h) = liftSecond K r t g * liftSecond K r t h := by
  simp [liftSecond, map_mul]

theorem liftFirst_inv (g : (liftShape r t).parabolic K.Carrier) :
    liftFirst K r t g⁻¹ = (liftFirst K r t g)⁻¹ := by
  simp [liftFirst, map_inv]

theorem liftSecond_inv (g : (liftShape r t).parabolic K.Carrier) :
    liftSecond K r t g⁻¹ = (liftSecond K r t g)⁻¹ := by
  simp [liftSecond, map_inv]

theorem liftFirst_one : liftFirst K r t 1 = 1 := by
  rw [liftFirst, map_one, map_one]
  rfl

theorem liftSecond_one : liftSecond K r t 1 = 1 := by
  rw [liftSecond, map_one, map_one]
  rfl

/-- The diagonal blocks of an integral parabolic element are integral. -/
theorem lift_mem_integral (g : (liftShape r t).parabolic K.Carrier)
    (hg : (g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) ∈
      integralSubgroup K.canonicalTopologicalData.Integers (r + 1 + t)) :
    liftFirst K r t g ∈ integralSubgroup K.canonicalTopologicalData.Integers r ∧
      liftSecond K r t g ∈ integralSubgroup K.canonicalTopologicalData.Integers t := by
  obtain ⟨h1, h2⟩ := (mem_integralSubgroup _ _ _).1 hg
  constructor
  · refine (mem_integralSubgroup _ _ _).2 ⟨fun a b => ?_, fun a b => ?_⟩
    · rw [liftFirst_apply]
      exact h1 _ _
    · rw [← liftFirst_inv, liftFirst_apply]
      exact h2 _ _
  · refine (mem_integralSubgroup _ _ _).2 ⟨fun a b => ?_, fun a b => ?_⟩
    · rw [liftSecond_apply]
      exact h1 _ _
    · rw [← liftSecond_inv, liftSecond_apply]
      exact h2 _ _

/-- The upper radical matrix `u(X)` as an element of the parabolic. -/
def liftUpper (X : Matrix (Fin (r + 1)) (Fin (t + 1)) K.Carrier) :
    (liftShape r t).parabolic K.Carrier :=
  ⟨upper (r + 1) (t + 1) K.Carrier X, by
    rw [twoBlocks_mem_parabolic_iff]
    intro i j
    exact upper_second_first _ _ _ X i j⟩

/-- The block-diagonal matrix `diag(m₁, m₂)` as an element of the parabolic. -/
def liftLevi (m₁ : Langlands.GeneralLinear (r + 1) K.Carrier)
    (m₂ : Langlands.GeneralLinear (t + 1) K.Carrier) : (liftShape r t).parabolic K.Carrier :=
  (liftShape r t).leviInParabolic K.Carrier
    ((twoBlockLeviEquiv (Nat.succ_pos r) (Nat.succ_pos t) K.Carrier).symm (m₁, m₂))

theorem liftLevi_val (m₁ : Langlands.GeneralLinear (r + 1) K.Carrier)
    (m₂ : Langlands.GeneralLinear (t + 1) K.Carrier) :
    (liftLevi K r t m₁ m₂ : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) =
      GeneralLinear.blockSum (m₁, m₂) := by
  rw [liftLevi, BlockShape.leviInParabolic_val, twoBlocks_leviEmbedding]
  rfl

theorem liftFirst_liftLevi (m₁ : Langlands.GeneralLinear (r + 1) K.Carrier)
    (m₂ : Langlands.GeneralLinear (t + 1) K.Carrier) :
    liftFirst K r t (liftLevi K r t m₁ m₂) = m₁ := by
  simp [liftFirst, liftLevi, BlockShape.leviProjection_section]

theorem liftSecond_liftLevi (m₁ : Langlands.GeneralLinear (r + 1) K.Carrier)
    (m₂ : Langlands.GeneralLinear (t + 1) K.Carrier) :
    liftSecond K r t (liftLevi K r t m₁ m₂) = m₂ := by
  simp [liftSecond, liftLevi, BlockShape.leviProjection_section]

theorem liftFirst_liftUpper (X : Matrix (Fin (r + 1)) (Fin (t + 1)) K.Carrier) :
    liftFirst K r t (liftUpper K r t X) = 1 := by
  apply Units.ext
  funext a b
  rw [liftFirst_apply]
  simp only [liftUpper, upper_first_first, Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply]

theorem liftSecond_liftUpper (X : Matrix (Fin (r + 1)) (Fin (t + 1)) K.Carrier) :
    liftSecond K r t (liftUpper K r t X) = 1 := by
  apply Units.ext
  funext a b
  rw [liftSecond_apply]
  simp only [liftUpper, upper_second_second, Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply]

theorem upper_mul_blockSum_eq (X : Matrix (Fin (r + 1)) (Fin (t + 1)) K.Carrier)
    (m₁ : Langlands.GeneralLinear (r + 1) K.Carrier) (m₂ : Langlands.GeneralLinear (t + 1) K.Carrier) :
    upper (r + 1) (t + 1) K.Carrier X * GeneralLinear.blockSum (m₁, m₂) =
      ((liftUpper K r t X * liftLevi K r t m₁ m₂ : (liftShape r t).parabolic K.Carrier) :
        Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) := by
  rw [Subgroup.coe_mul, liftLevi_val]
  rfl

/-- Every parabolic element is `u(X) diag(m₁, m₂)` with its own diagonal blocks. -/
theorem exists_eq_upper_mul_blockSum (g : (liftShape r t).parabolic K.Carrier) :
    ∃ X : Matrix (Fin (r + 1)) (Fin (t + 1)) K.Carrier,
      (g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) =
        upper (r + 1) (t + 1) K.Carrier X *
          GeneralLinear.blockSum (liftFirst K r t g, liftSecond K r t g) := by
  obtain ⟨X, hX⟩ := exists_upper_mul_blockSum (Nat.succ_pos r) (Nat.succ_pos t) K.Carrier g
  exact ⟨X, hX⟩

section Lift

variable {K r t}
variable {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
    (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)

/-- A function on the Levi that is right invariant under integral Levi elements. -/
def IsLeviInvariant (Φ : Langlands.GeneralLinear (r + 1) K.Carrier →
    Langlands.GeneralLinear (t + 1) K.Carrier → ℂ) : Prop :=
  ∀ (m₁ μ₁ : Langlands.GeneralLinear (r + 1) K.Carrier)
    (m₂ μ₂ : Langlands.GeneralLinear (t + 1) K.Carrier),
    μ₁ ∈ integralSubgroup K.canonicalTopologicalData.Integers r →
    μ₂ ∈ integralSubgroup K.canonicalTopologicalData.Integers t →
    Φ (m₁ * μ₁) (m₂ * μ₂) = Φ m₁ m₂

/-- The lift of a Levi function: its value at `x` is `Φ` of the diagonal blocks of `g` for one
chosen decomposition `x = g k`, with `g` in the upper two-block parabolic and `k` integral. For a
Levi-invariant `Φ` the value is the same for every such decomposition
(`liftFunction_parabolic_mul`); in general it depends on the choice. -/
def liftFunction (Φ : Langlands.GeneralLinear (r + 1) K.Carrier →
    Langlands.GeneralLinear (t + 1) K.Carrier → ℂ)
    (x : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) : ℂ :=
  Φ (liftFirst K r t ⟨(exists_liftShape_parabolic_mul r t hϖ x).choose,
      (exists_liftShape_parabolic_mul r t hϖ x).choose_spec.1⟩)
    (liftSecond K r t ⟨(exists_liftShape_parabolic_mul r t hϖ x).choose,
      (exists_liftShape_parabolic_mul r t hϖ x).choose_spec.1⟩)

variable {Φ : Langlands.GeneralLinear (r + 1) K.Carrier →
    Langlands.GeneralLinear (t + 1) K.Carrier → ℂ}

theorem liftFunction_parabolic_mul (hΦ : IsLeviInvariant Φ)
    (g : (liftShape r t).parabolic K.Carrier) (k : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier)
    (hk : k ∈ integralSubgroup K.canonicalTopologicalData.Integers (r + 1 + t)) :
    liftFunction hϖ Φ (g.val * k) = Φ (liftFirst K r t g) (liftSecond K r t g) := by
  obtain ⟨hg₀, k₀, hk₀, hx⟩ := (exists_liftShape_parabolic_mul r t hϖ (g.val * k)).choose_spec
  set g₀ : (liftShape r t).parabolic K.Carrier :=
    ⟨(exists_liftShape_parabolic_mul r t hϖ (g.val * k)).choose, hg₀⟩ with hg₀def
  have hx' : g.val * k = g₀.val * k₀ := hx
  have hd : ((g⁻¹ * g₀ : (liftShape r t).parabolic K.Carrier) :
      Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) ∈
        integralSubgroup K.canonicalTopologicalData.Integers (r + 1 + t) := by
    have e : ((g⁻¹ * g₀ : (liftShape r t).parabolic K.Carrier) :
        Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) = k * k₀⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      calc g.val⁻¹ * g₀.val = g.val⁻¹ * (g₀.val * k₀) * k₀⁻¹ := by group
        _ = g.val⁻¹ * (g.val * k) * k₀⁻¹ := by rw [hx']
        _ = k * k₀⁻¹ := by group
    rw [e]
    exact mul_mem hk (inv_mem hk₀)
  obtain ⟨h1, h2⟩ := lift_mem_integral K r t _ hd
  have e1 : liftFirst K r t g₀ = liftFirst K r t g * liftFirst K r t (g⁻¹ * g₀) := by
    rw [← liftFirst_mul, mul_inv_cancel_left]
  have e2 : liftSecond K r t g₀ = liftSecond K r t g * liftSecond K r t (g⁻¹ * g₀) := by
    rw [← liftSecond_mul, mul_inv_cancel_left]
  change Φ (liftFirst K r t g₀) (liftSecond K r t g₀) = _
  rw [e1, e2, hΦ _ _ _ _ h1 h2]

/-- The transformation law of the lift of a Levi-invariant function, on every decomposition
`u(X) diag(m₁, m₂) k`. -/
theorem liftFunction_law (hΦ : IsLeviInvariant Φ)
    (X : Matrix (Fin (r + 1)) (Fin (t + 1)) K.Carrier)
    (m₁ : Langlands.GeneralLinear (r + 1) K.Carrier) (m₂ : Langlands.GeneralLinear (t + 1) K.Carrier)
    (k : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier)
    (hk : k ∈ integralSubgroup K.canonicalTopologicalData.Integers (r + 1 + t)) :
    liftFunction hϖ Φ (upper (r + 1) (t + 1) K.Carrier X * GeneralLinear.blockSum (m₁, m₂) * k) =
      Φ m₁ m₂ := by
  rw [upper_mul_blockSum_eq, liftFunction_parabolic_mul hϖ hΦ _ k hk, liftFirst_mul, liftSecond_mul,
    liftFirst_liftUpper, liftSecond_liftUpper, liftFirst_liftLevi, liftSecond_liftLevi, one_mul,
    one_mul]

/-- The lift of a Levi-invariant function is right invariant under the integral matrices. -/
theorem liftFunction_mul_integral (hΦ : IsLeviInvariant Φ)
    (x k : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier)
    (hk : k ∈ integralSubgroup K.canonicalTopologicalData.Integers (r + 1 + t)) :
    liftFunction hϖ Φ (x * k) = liftFunction hϖ Φ x := by
  obtain ⟨hg₀, k₀, hk₀, hx⟩ := (exists_liftShape_parabolic_mul r t hϖ x).choose_spec
  set g₀ : (liftShape r t).parabolic K.Carrier :=
    ⟨(exists_liftShape_parabolic_mul r t hϖ x).choose, hg₀⟩ with hg₀def
  have hx' : x = g₀.val * k₀ := hx
  have e : x * k = g₀.val * (k₀ * k) := by rw [hx', mul_assoc]
  rw [e, liftFunction_parabolic_mul hϖ hΦ g₀ _ (mul_mem hk₀ hk)]
  rfl

/-- For a Levi-invariant `Φ`, left multiplication by a parabolic element multiplies the Levi
arguments on the left by its diagonal blocks. -/
theorem liftFunction_parabolic_mul_left (hΦ : IsLeviInvariant Φ)
    (g : (liftShape r t).parabolic K.Carrier)
    (x : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    ∃ m₁ : Langlands.GeneralLinear (r + 1) K.Carrier, ∃ m₂ : Langlands.GeneralLinear (t + 1) K.Carrier,
      liftFunction hϖ Φ x = Φ m₁ m₂ ∧
      liftFunction hϖ Φ (g.val * x) = Φ (liftFirst K r t g * m₁) (liftSecond K r t g * m₂) := by
  obtain ⟨hg₀, k₀, hk₀, hx⟩ := (exists_liftShape_parabolic_mul r t hϖ x).choose_spec
  set g₀ : (liftShape r t).parabolic K.Carrier :=
    ⟨(exists_liftShape_parabolic_mul r t hϖ x).choose, hg₀⟩ with hg₀def
  have hx' : x = g₀.val * k₀ := hx
  refine ⟨liftFirst K r t g₀, liftSecond K r t g₀, ?_, ?_⟩
  · rw [hx', liftFunction_parabolic_mul hϖ hΦ g₀ k₀ hk₀]
  · have e : g.val * x = (g * g₀).val * k₀ := by rw [hx', Subgroup.coe_mul, mul_assoc]
    rw [e, liftFunction_parabolic_mul hϖ hΦ _ k₀ hk₀, liftFirst_mul, liftSecond_mul]

/-- For a Levi-invariant `Φ`, a function with the transformation law of `Φ` is the lift of `Φ`. -/
theorem eq_liftFunction (hΦ : IsLeviInvariant Φ)
    {f : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier → ℂ}
    (hf : ∀ (X : Matrix (Fin (r + 1)) (Fin (t + 1)) K.Carrier)
        (m₁ : Langlands.GeneralLinear (r + 1) K.Carrier)
        (m₂ : Langlands.GeneralLinear (t + 1) K.Carrier)
        (k : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier),
        k ∈ integralSubgroup K.canonicalTopologicalData.Integers (r + 1 + t) →
        f (upper (r + 1) (t + 1) K.Carrier X * GeneralLinear.blockSum (m₁, m₂) * k) = Φ m₁ m₂) :
    f = liftFunction hϖ Φ := by
  funext x
  obtain ⟨g, hg, k, hk, rfl⟩ := exists_liftShape_parabolic_mul r t hϖ x
  obtain ⟨X, hX⟩ := exists_eq_upper_mul_blockSum K r t ⟨g, hg⟩
  have hX' : g = upper (r + 1) (t + 1) K.Carrier X *
      GeneralLinear.blockSum (liftFirst K r t ⟨g, hg⟩, liftSecond K r t ⟨g, hg⟩) := hX
  rw [hX', hf _ _ _ k hk, liftFunction_law hϖ hΦ _ _ _ k hk]

/-- **The lift on the open cell.** For a Levi-invariant `Φ` there are upper unipotent `u₁`, `u₂`
with `F(lower(Y)) = Φ(u₁ ϖ^λ, u₂ ϖ^μ)`, where `λ`, `μ` are the two blocks of the Iwasawa
exponent of `lower(Y)` (writing `lower(Y) = u ϖ^ν k`, these are the diagonal blocks of
`u ϖ^ν`). -/
theorem liftFunction_lower (hΦ : IsLeviInvariant Φ) (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier) :
    ∃ u₁ ∈ upperUnipotent (r + 1) K.Carrier, ∃ u₂ ∈ upperUnipotent (t + 1) K.Carrier,
      liftFunction hϖ Φ (lower (r + 1) (t + 1) K.Carrier Y) =
        Φ (u₁ * Iwasawa.torus ϖ fun i => openCellExponent hϖ Y (i.castAdd (t + 1)))
          (u₂ * Iwasawa.torus ϖ fun j => openCellExponent hϖ Y (j.natAdd (r + 1))) := by
  obtain ⟨u, hu, k, hk, h⟩ := exists_eq_openCellExponent hϖ Y
  have hb := isUpperTriangular_mul_torus hu ϖ (openCellExponent hϖ Y)
  have hb' := eq_upper_mul_blockSum (u * Iwasawa.torus ϖ (openCellExponent hϖ Y)) hb
  rw [topLeft_mul_torus hu, botRight_mul_torus hu] at hb'
  refine ⟨topLeft u hu.1, topLeft_mem_upperUnipotent hu, botRight u hu.1,
    botRight_mem_upperUnipotent hu, ?_⟩
  rw [h, hb', liftFunction_law hϖ hΦ _ _ _ k hk]

end Lift

end Langlands.Shahidi.OpenCell
