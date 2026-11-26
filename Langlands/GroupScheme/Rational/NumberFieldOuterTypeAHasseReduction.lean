import Langlands.GroupScheme.Rational.NumberFieldUnitaryAlgebraHasse
import Langlands.GroupScheme.SimplyConnected.OuterTypeAUnitaryAlgebraPresentationStatement
import Langlands.GroupScheme.Rational.NumberFieldHasseKernelTypeReduction

/-! # The outer type A Hasse kernel from the unitary presentation and arithmetic -/

universe u

namespace Langlands.GroupScheme

/-- The presentation of outer type A groups as `SU(B, τ)`, Landherr's theorem and the
unitary norm theorem together imply the Hasse kernel for simply connected groups of outer
type `A` over number fields. -/
def NumberFieldOuterTypeAHasseReductionStatement : Prop :=
  OuterTypeAUnitaryAlgebraPresentationStatement.{u} →
    Langlands.CentralSimple.NumberFieldLandherrStatement.{u} →
      Langlands.CentralSimple.NumberFieldUnitaryNormStatement.{u} →
        NumberFieldOuterTypeAHasseStatement.{u}

/-- The presentation of outer type A groups as `SU(B, τ)`, Landherr's theorem and the
unitary norm theorem give the Hasse kernel for simply connected groups of outer type `A`
over number fields. -/
theorem numberFieldOuterTypeAHasse_of_unitaryPresentation
    (hP : OuterTypeAUnitaryAlgebraPresentationStatement.{u})
    (hL : Langlands.CentralSimple.NumberFieldLandherrStatement.{u})
    (hN : Langlands.CentralSimple.NumberFieldUnitaryNormStatement.{u}) :
    NumberFieldOuterTypeAHasseStatement.{u} := by
  intro F _ _ G _ _ d n e hsc habs hcart hstar L _ _ _ _ ξ hξ
  obtain ⟨E, _, _, _, _, B, _, _, _, _, _, _, _, τ, hτ, -, ⟨p⟩⟩ :=
    hP F G d n hsc habs ⟨e, hcart⟩ hstar
  have : FiniteDimensional F E :=
    .of_finrank_pos (by rw [Algebra.IsQuadraticExtension.finrank_eq_two F E]; decide)
  have : FiniteDimensional F B := Module.Finite.trans E B
  exact UnitaryAlgebra.isTrivial_of_landherr_unitaryNorm p hL hN hτ ξ hξ

/-- The reduction statement holds. -/
theorem numberFieldOuterTypeAHasseReduction :
    NumberFieldOuterTypeAHasseReductionStatement.{u} :=
  numberFieldOuterTypeAHasse_of_unitaryPresentation

end Langlands.GroupScheme
