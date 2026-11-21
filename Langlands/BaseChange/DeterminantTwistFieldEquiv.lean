import Langlands.Group.GL.Basic
import Langlands.Representation.Twist.PullbackProof
import Langlands.Representation.Twist.IntertwiningProof
import Mathlib.Basic.Complex.Basic

/-! # Pullback of determinant twists under field equivalence -/

noncomputable section

set_option autoImplicit false

namespace Langlands.BaseChange

open GeneralLinear

/-- Pull back a determinant twist along a field equivalence and use the
transported character of the original unit group. -/
def pullbackDeterminantTwistEquiv {F F' : Type*} [Field F] [Field F'] {n : ℕ}
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (a : F ≃+* F') {π : Representation ℂ (GeneralLinear n F) V}
    {R : Representation ℂ (GeneralLinear n F') W}
    (e : π.Equiv (R.comp (Matrix.GeneralLinearGroup.map a.toRingHom)))
    (χ : (F')ˣ →* ℂˣ) :
    (twist ((χ.comp (Units.mapEquiv a.toMulEquiv).toMonoidHom).comp determinant) π).Equiv
      ((twist (χ.comp determinant) R).comp (Matrix.GeneralLinearGroup.map a.toRingHom)) := by
  let δ := (χ.comp (Units.mapEquiv a.toMulEquiv).toMonoidHom).comp
    (determinant (n := n))
  let m := Matrix.GeneralLinearGroup.map (n := Fin n) a.toRingHom
  have hδ : (χ.comp determinant).comp m = δ := by
    apply MonoidHom.ext
    intro g
    change χ (determinant (m g)) = χ (Units.mapEquiv a.toMulEquiv (determinant g))
    rw [Matrix.GeneralLinearGroup.map_det]
    rfl
  have ht : (twist (χ.comp determinant) R).comp m = twist δ (R.comp m) := by
    rw [twist_comp, hδ]
  change (twist δ π).Equiv ((twist (χ.comp determinant) R).comp m)
  rw [ht]
  exact twistEquiv δ e

end Langlands.BaseChange
