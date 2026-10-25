import Langlands.Representation.Archimedean.SmoothVectors
import Langlands.Representation.Whittaker.GeneralLinear
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra

/-!
# Generic Banach representations of real and complex general linear groups

For `F = ℝ` or `ℂ`, the group `GL_n(F)` is the real Lie group of units of the
real Banach algebra of `n × n` matrices over `F`, with the operator norm. The
compact subgroup is the unitary group: `O(n)` over `ℝ` and `U(n)` over `ℂ`.
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.HarmonicAnalysis

-- The operator norm and the product topology on matrices agree definitionally, but
-- resolving the charts on units needs reduction through the normed-ring instances.
set_option backward.isDefEq.respectTransparency false

universe uF uE

variable (F : Type uF) [RCLike F]

/-- The model of `GL_n(F)`: the real normed space of `n × n` matrices over `F`. -/
abbrev matrixModel (n : ℕ) :
    ModelWithCorners ℝ (Matrix (Fin n) (Fin n) F) (Matrix (Fin n) (Fin n) F) :=
  𝓘(ℝ, Matrix (Fin n) (Fin n) F)

/-- `GL_n(F)` is a real Lie group for its matrix model. -/
example (n : ℕ) : LieGroup (matrixModel F n) ∞ (Langlands.GeneralLinear n F) :=
  inferInstance

/-- The unitary subgroup of `GL_n(F)`: `O(n)` over `ℝ`, `U(n)` over `ℂ`. -/
def unitaryCompact (n : ℕ) : Subgroup (Langlands.GeneralLinear n F) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) F) ∈ Matrix.unitaryGroup (Fin n) F}
  one_mem' := (Matrix.unitaryGroup (Fin n) F).one_mem
  mul_mem' {g h} hg hh := (Matrix.unitaryGroup (Fin n) F).mul_mem hg hh
  inv_mem' {g} hg := by
    have h : ((g⁻¹ : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F) =
        star (g : Matrix (Fin n) (Fin n) F) := by
      calc ((g⁻¹ : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F)
          = (star (g : Matrix (Fin n) (Fin n) F) * g) *
              ((g⁻¹ : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F) := by
            rw [Unitary.star_mul_self_of_mem hg, one_mul]
        _ = star (g : Matrix (Fin n) (Fin n) F) := by
            rw [mul_assoc, Units.mul_inv, mul_one]
    change ((g⁻¹ : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F) ∈
      Matrix.unitaryGroup (Fin n) F
    rw [h]
    exact Unitary.star_mem hg

theorem mem_unitaryCompact_iff (n : ℕ) (g : Langlands.GeneralLinear n F) :
    g ∈ unitaryCompact F n ↔
      star (g : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F) = 1 := by
  change (g : Matrix (Fin n) (Fin n) F) ∈ Matrix.unitaryGroup (Fin n) F ↔ _
  exact (Units.isUnit g).mem_unitary_iff_star_mul_self

/-- The model of the Levi subgroup `GL_n(F) × GL_m(F)`. -/
abbrev pairModel (n m : ℕ) :=
  (matrixModel F n).prod (matrixModel F m)

/-- `GL_n(F) × GL_m(F)` is a real Lie group for the product model. -/
example (n m : ℕ) : LieGroup (pairModel F n m) ∞
    (Langlands.GeneralLinear n F × Langlands.GeneralLinear m F) :=
  inferInstance

/-- The compact subgroup `K_n × K_m` of the Levi subgroup. -/
def pairCompact (n m : ℕ) :
    Subgroup (Langlands.GeneralLinear n F × Langlands.GeneralLinear m F) :=
  (unitaryCompact F n).prod (unitaryCompact F m)

/-- The upper unipotent subgroup `N_n × N_m` of the Levi subgroup. -/
def pairUnipotent (n m : ℕ) :
    Subgroup (Langlands.GeneralLinear n F × Langlands.GeneralLinear m F) :=
  (upperUnipotent n F).prod (upperUnipotent m F)

/-- The product of the standard characters, `(u, u') ↦ ψ(∑ uᵢ,ᵢ₊₁) ψ(∑ u'ⱼ,ⱼ₊₁)`. -/
def pairCharacter (ψ : UnitaryAdditiveCharacter F) (n m : ℕ) :
    pairUnipotent F (n + 1) (m + 1) →* ℂˣ :=
  (MonoidHom.coprod (Whittaker.standardCharacter ψ n) (Whittaker.standardCharacter ψ m)).comp
    (Subgroup.prodEquiv (upperUnipotent (n + 1) F) (upperUnipotent (m + 1) F)).toMonoidHom

@[simp]
theorem pairCharacter_apply (ψ : UnitaryAdditiveCharacter F) (n m : ℕ)
    (u : pairUnipotent F (n + 1) (m + 1)) :
    (pairCharacter F ψ n m u : ℂ) =
      ψ.complex (∑ i : Fin n, u.val.1 i.castSucc i.succ) *
        ψ.complex (∑ j : Fin m, u.val.2 j.castSucc j.succ) :=
  rfl

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- An irreducible admissible generic Banach representation of `GL_{n+1}(F)` for the
standard character of `ψ`. -/
def IsGenericBanachRepresentation (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (σ : Langlands.GeneralLinear (n + 1) F →* (E →L[ℂ] E)) : Prop :=
  IsIrreducibleAdmissibleGeneric (matrixModel F (n + 1)) σ (unitaryCompact F (n + 1))
    (upperUnipotent (n + 1) F) (Whittaker.standardCharacter ψ n)

/-- An irreducible admissible generic Banach representation of
`GL_{n+1}(F) × GL_{m+1}(F)` for the product of the standard characters of `ψ`. -/
def IsGenericBanachPairRepresentation (ψ : UnitaryAdditiveCharacter F) (n m : ℕ)
    (σ : Langlands.GeneralLinear (n + 1) F × Langlands.GeneralLinear (m + 1) F →*
      (E →L[ℂ] E)) : Prop :=
  IsIrreducibleAdmissibleGeneric (pairModel F (n + 1) (m + 1)) σ
    (pairCompact F (n + 1) (m + 1)) (pairUnipotent F (n + 1) (m + 1)) (pairCharacter F ψ n m)

end Langlands.Archimedean
