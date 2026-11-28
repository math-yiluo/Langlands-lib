import Langlands.GroupTheory.CocycleExtension
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Basic.Complex.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Coprime.Basic

/-! # The quadratic first twist for a split cover -/

namespace Langlands.Covering.Dual

universe u v

/-- The lattice divisibility and pairing data for the first twist of Gan–Gao, §5.2. -/
structure FirstTwistData (A : Type u) [CommGroup A] (L : Type v)
    [AddCommGroup L] [Module ℤ L] where
  n : ℕ
  n_pos : 0 < n
  Q : QuadraticForm ℤ L
  M : Submodule ℤ L
  polar_dvd : ∀ x y, (n : ℤ) ∣ Q.polarBilin x y
  value_dvd : ∀ y ∈ M, (n : ℤ) ∣ Q y
  pairing : A →* A →* ℂˣ
  pairing_pow : ∀ a b, pairing a b ^ n = 1

namespace FirstTwistData

variable {A : Type u} [CommGroup A] {L : Type v} [AddCommGroup L] [Module ℤ L]
  (D : FirstTwistData A L)

/-- The complex character group of `L ⧸ D.M`, with pointwise multiplication. -/
abbrev Character := Multiplicative (L ⧸ D.M) →* ℂˣ

private theorem zpow_eq_one_of_dvd {z : ℂˣ} {n : ℕ} {m : ℤ}
    (hz : z ^ n = 1) (hm : (n : ℤ) ∣ m) : z ^ m = 1 := by
  obtain ⟨k, rfl⟩ := hm
  rw [zpow_mul, zpow_natCast, hz, one_zpow]

private def latticeCharacter (a b : A) : L →+ Additive ℂˣ where
  toFun y := Additive.ofMul (D.pairing a b ^ D.Q y)
  map_zero' := by
    change D.pairing a b ^ D.Q 0 = 1
    rw [map_zero, zpow_zero]
  map_add' x y := by
    change D.pairing a b ^ D.Q (x + y) = D.pairing a b ^ D.Q x * D.pairing a b ^ D.Q y
    have h := zpow_eq_one_of_dvd (D.pairing_pow a b) (D.polar_dvd x y)
    simp only [QuadraticMap.polarBilin_apply_apply] at h
    rw [QuadraticMap.map_add (⇑D.Q), zpow_add, h, mul_one, zpow_add]

private def character (a b : A) : D.Character :=
  (QuotientAddGroup.lift D.M.toAddSubgroup (D.latticeCharacter a b) (by
    intro y hy
    change D.pairing a b ^ D.Q y = 1
    exact zpow_eq_one_of_dvd (D.pairing_pow a b) (D.value_dvd y hy))).toMultiplicativeLeft

private theorem character_apply_mk (a b : A) (y : L) :
    D.character a b (Multiplicative.ofAdd (Submodule.Quotient.mk y)) = D.pairing a b ^ D.Q y := rfl

private theorem character_ext {χ ψ : D.Character}
    (h : ∀ y : L, χ (Multiplicative.ofAdd (Submodule.Quotient.mk y)) =
      ψ (Multiplicative.ofAdd (Submodule.Quotient.mk y))) : χ = ψ := by
  apply MonoidHom.ext
  intro z
  exact Submodule.Quotient.induction_on (p := D.M)
    (C := fun q => χ (Multiplicative.ofAdd q) = ψ (Multiplicative.ofAdd q))
    (Multiplicative.toAdd z) h

/-- The first twist as a bimultiplicative pairing with values in quotient characters. -/
def c₁ : A →* A →* D.Character where
  toFun a :=
    { toFun := D.character a
      map_one' := D.character_ext fun y => by simp [character_apply_mk]
      map_mul' b b' := D.character_ext fun y => by simp [character_apply_mk, mul_zpow] }
  map_one' := MonoidHom.ext fun b => D.character_ext fun y => by simp [character_apply_mk]
  map_mul' a a' := MonoidHom.ext fun b => D.character_ext fun y => by
    simp [character_apply_mk, mul_zpow]

/-- Evaluation of the first twist on the class of a lattice element. -/
@[simp] theorem c₁_apply_mk (a b : A) (y : L) :
    D.c₁ a b (Multiplicative.ofAdd (Submodule.Quotient.mk y)) = D.pairing a b ^ D.Q y := rfl

/-- A trivial pairing value gives the trivial character. -/
theorem c₁_eq_one_of_pairing_eq_one (a b : A) (h : D.pairing a b = 1) : D.c₁ a b = 1 := by
  apply D.character_ext
  intro y
  simp [h]

private theorem dvd_quad_mul_two (y : L) : (D.n : ℤ) ∣ D.Q y * 2 := by
  rw [mul_comm (D.Q y) 2, two_mul]
  simpa only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul]
    using D.polar_dvd y y

/-- Every first-twist character lies in the two-torsion subgroup. -/
theorem c₁_sq (a b : A) : D.c₁ a b ^ 2 = 1 := by
  apply D.character_ext
  intro y
  rw [MonoidHom.pow_apply, D.c₁_apply_mk, MonoidHom.one_apply]
  simpa only [zpow_mul, zpow_ofNat] using
    zpow_eq_one_of_dvd (D.pairing_pow a b) (D.dvd_quad_mul_two y)

/-- At odd degree the first twist is trivial. -/
theorem c₁_eq_one_of_odd (hn : Odd D.n) (a b : A) : D.c₁ a b = 1 := by
  apply D.character_ext
  intro y
  rw [D.c₁_apply_mk, MonoidHom.one_apply]
  exact zpow_eq_one_of_dvd (D.pairing_pow a b)
    ((hn.natCast (R := ℤ)).isCoprime_two.dvd_of_dvd_mul_right (D.dvd_quad_mul_two y))

/-- The trivial action of the base group on the character group. -/
abbrev trivialAction : MulDistribMulAction A D.Character where
  smul _ χ := χ
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

attribute [local instance] trivialAction

/-- The normalized first-twist cocycle for the trivial action. -/
def cocycle : @NormalizedTwoCocycle A D.Character _ _ D.trivialAction where
  toFun p := D.c₁ p.1 p.2
  cocycle := by
    intro a b c
    change D.c₁ (a * b) c * D.c₁ a b = D.c₁ b c * D.c₁ a (b * c)
    simp only [map_mul, MonoidHom.mul_apply]
    calc
      D.c₁ a c * D.c₁ b c * D.c₁ a b = D.c₁ a c * (D.c₁ b c * D.c₁ a b) :=
        mul_assoc (D.c₁ a c) (D.c₁ b c) (D.c₁ a b)
      _ = D.c₁ b c * (D.c₁ a c * D.c₁ a b) :=
        mul_left_comm (D.c₁ a c) (D.c₁ b c) (D.c₁ a b)
      _ = D.c₁ b c * (D.c₁ a b * D.c₁ a c) :=
        congrArg (D.c₁ b c * ·) (mul_comm (D.c₁ a c) (D.c₁ a b))
  normalized := by
    change D.c₁ 1 1 = 1
    simp

/-- The normalized cocycle has the first-twist evaluation on each quotient class. -/
@[simp] theorem cocycle_apply_mk (a b : A) (y : L) :
    D.cocycle (a, b) (Multiplicative.ofAdd (Submodule.Quotient.mk y)) =
      D.pairing a b ^ D.Q y := rfl

/-- The skew pairing gives a symmetric cocycle because its characters square to one. -/
theorem cocycle_symm (skew : ∀ a b, D.pairing b a = (D.pairing a b)⁻¹) (a b : A) :
    D.cocycle (a, b) = D.cocycle (b, a) := by
  have h : D.c₁ b a = (D.c₁ a b)⁻¹ := by
    apply D.character_ext
    intro y
    simp only [D.c₁_apply_mk, skew a b, MonoidHom.inv_apply, inv_zpow]
  change D.c₁ a b = D.c₁ b a
  rw [h]
  exact eq_inv_iff_mul_eq_one.mpr ((pow_two (D.c₁ a b)).symm.trans (D.c₁_sq a b))

/-- The central extension constructed from the first-twist cocycle. -/
abbrev Extension := D.cocycle.Extension

/-- Include the character group via `χ ↦ (χ, 1)`. -/
def inclusion : D.Character →* D.Extension := NormalizedTwoCocycle.Extension.inl D.cocycle

/-- Project to the second coordinate. -/
def projection : D.Extension →* A := NormalizedTwoCocycle.Extension.projection D.cocycle

/-- The coordinate section `a ↦ (1, a)`. -/
def sectionMap : A → D.Extension := NormalizedTwoCocycle.Extension.sectionMap D.cocycle

@[simp] theorem projection_inclusion (χ : D.Character) : D.projection (D.inclusion χ) = 1 := rfl

@[simp] theorem projection_sectionMap (a : A) : D.projection (D.sectionMap a) = a := rfl

theorem inclusion_injective : Function.Injective D.inclusion :=
  NormalizedTwoCocycle.Extension.inl_injective D.cocycle

theorem projection_surjective : Function.Surjective D.projection :=
  NormalizedTwoCocycle.Extension.projection_surjective D.cocycle

theorem range_inclusion_eq_ker_projection : D.inclusion.range = D.projection.ker :=
  NormalizedTwoCocycle.Extension.range_inl_eq_ker_projection D.cocycle

theorem mul_inclusion (x : D.Extension) (χ : D.Character) :
    x * D.inclusion χ = D.inclusion χ * x :=
  NormalizedTwoCocycle.Extension.mul_inl D.cocycle x χ

theorem sectionMap_mul (a b : A) :
    D.sectionMap a * D.sectionMap b = D.inclusion (D.c₁ a b) * D.sectionMap (a * b) :=
  NormalizedTwoCocycle.Extension.sectionMap_mul D.cocycle a b

/-- Commutativity of the extension for a skew pairing. -/
@[instance_reducible] def extensionCommGroup (skew : ∀ a b, D.pairing b a = (D.pairing a b)⁻¹) :
    CommGroup D.Extension where
  __ := (inferInstance : Group D.Extension)
  mul_comm x y := by
    apply NormalizedTwoCocycle.Extension.ext
    · change x.left * y.left * D.cocycle (x.right, y.right) =
        y.left * x.left * D.cocycle (y.right, x.right)
      rw [mul_comm x.left y.left, D.cocycle_symm skew x.right y.right]
    · exact mul_comm x.right y.right

end FirstTwistData
end Langlands.Covering.Dual
