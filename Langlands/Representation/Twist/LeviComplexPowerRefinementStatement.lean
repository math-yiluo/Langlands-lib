import Langlands.Representation.Twist.LeviComplexPower
import Langlands.Representation.Geometric.FlattenedLevi

/-! # Complex determinant characters through actual Levi refinements -/

noncomputable section

namespace Langlands

universe uF uV

open GeneralLinear Geometric

/-- Coarse complex determinant characters restrict through the actual refined
projection and flattened Levi, and add to an arbitrary existing fine twist.
This definition states the three laws without proving them. -/
def LeviComplexPowerRefinementStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (B : BlockShape n) (S : BlockRefinement B)
    (z : Fin B.length → ℂ),
    let C := B.flatten S
    let e := flattenedLeviEquiv F.Carrier B S
    let zFine : Fin C.length → ℂ :=
      fun k => z ((B.flattenBlockEquiv S).symm k).1
    (∀ q : refinedParabolic F.Carrier B S,
      T.leviComplexPowerCharacter B z q.val =
        T.leviComplexPowerCharacter C zFine
          (e.symm (refinedLeviProjection F.Carrier B S q))) ∧
    (T.leviComplexPowerCharacter B z).comp (refinedLevi F.Carrier B S).subtype =
      (T.leviComplexPowerCharacter C zFine).comp e.symm.toMonoidHom ∧
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (C.Levi F.Carrier) V) (a : Fin C.length → ℂ),
      twist ((T.leviComplexPowerCharacter B z).comp
          (refinedLevi F.Carrier B S).subtype)
        ((T.leviComplexPowerTwist C a ρ).comp e.symm.toMonoidHom) =
      (T.leviComplexPowerTwist C (a + zFine) ρ).comp e.symm.toMonoidHom

end Langlands
