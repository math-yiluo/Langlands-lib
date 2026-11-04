import Langlands.Global.FunctionFieldAdelesSecondCountableStatement
import Langlands.Global.CurvePlaceFinitePolesProof
import Langlands.Global.AdelesSecondCountable

/-! # Countable bases from actual function-field arithmetic -/

noncomputable section

universe u

open TopologicalSpace
open scoped Valued

namespace Langlands.Global

variable (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]

include k

omit [Algebra k F] [IsScalarTower k (RatFunc k) F] in
theorem functionField_countable : Countable F := by
  let : Countable (Polynomial k) :=
    (AddMonoidAlgebra.coeff_injective.comp Polynomial.toFinsupp_injective).countable
  let : Countable (RatFunc k) := Function.Surjective.countable
    (f := fun p : Polynomial k × Polynomial k =>
      algebraMap (Polynomial k) (RatFunc k) p.1 /
        algebraMap (Polynomial k) (RatFunc k) p.2)
    (fun x => ⟨(x.num, x.denom), x.num_div_denom⟩)
  exact Finsupp.Countable.of_moduleFinite (R := RatFunc k)

theorem curvePlace_countable : Countable (AlgebraicCurve.Place k F) := by
  let : Countable F := functionField_countable k F
  have hcover : (⋃ x : F, {v : AlgebraicCurve.Place k F |
      x ∉ v.toValuationSubring}) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    have hex : ∃ x : F, x ∉ v.toValuationSubring := by
      by_contra! h
      exact v.ne_top' (SetLike.ext fun x => ⟨fun _ => trivial, fun _ => h x⟩)
    obtain ⟨x, hx⟩ := hex
    exact Set.mem_iUnion.mpr ⟨x, hx⟩
  apply Set.countable_univ_iff.mp
  rw [← hcover]
  exact Set.countable_iUnion fun x => (curvePlaceFinitePoles k F x).countable

theorem realAbsoluteValuePlace_countable : Countable (RealAbsoluteValuePlace (F := F)) := by
  let : Countable (AlgebraicCurve.Place k F) := curvePlace_countable k F
  exact (realAbsoluteValuePlaceCurvePlaceEquiv k F).injective.countable

omit [IsScalarTower k (RatFunc k) F] in
theorem curvePlaceCompletion_separableSpace (v : AlgebraicCurve.Place k F) :
    SeparableSpace (curvePlaceCompletion v) := by
  let : Countable F := functionField_countable k F
  exact SeparableSpace.of_denseRange (algebraMap F (curvePlaceCompletion v))
    (v.heightOneSpectrum.denseRange_algebraMap F)

omit [IsScalarTower k (RatFunc k) F] in
theorem curvePlaceCompletion_secondCountableTopology (v : AlgebraicCurve.Place k F) :
    SecondCountableTopology (curvePlaceCompletion v) := by
  let : SeparableSpace (curvePlaceCompletion v) := curvePlaceCompletion_separableSpace k F v
  let : (Valued.v : Valuation (curvePlaceCompletion v)
      (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 by norm_num)
  let : NormedField (curvePlaceCompletion v) :=
    Valued.toNormedField (curvePlaceCompletion v) (WithZero (Multiplicative ℤ))
  infer_instance

theorem realAbsoluteValuePlaceCompletion_secondCountableTopology
    (q : RealAbsoluteValuePlace (F := F)) :
    SecondCountableTopology (realAbsoluteValuePlaceCompletion q) := by
  let : SecondCountableTopology
      (curvePlaceCompletion (realAbsoluteValuePlaceCurvePlaceEquiv k F q)) :=
    curvePlaceCompletion_secondCountableTopology k F _
  let e : realAbsoluteValuePlaceCompletion q ≃ₜ
      curvePlaceCompletion (realAbsoluteValuePlaceCurvePlaceEquiv k F q) :=
    { toEquiv := (functionFieldAbsoluteValuePlaceCompletionEquiv k F q).toEquiv
      continuous_toFun := continuous_functionFieldAbsoluteValuePlaceCompletionEquiv k F q
      continuous_invFun := continuous_functionFieldAbsoluteValuePlaceCompletionEquiv_symm k F q }
  exact e.secondCountableTopology

theorem curvePlaceAdeles_secondCountableTopology :
    SecondCountableTopology (CurvePlaceAdeleRing k F) := by
  let : Countable (AlgebraicCurve.Place k F) := curvePlace_countable k F
  let (v : AlgebraicCurve.Place k F) :=
    curvePlaceCompletion_secondCountableTopology k F v
  exact restrictedProduct_secondCountableTopology
    (fun v : AlgebraicCurve.Place k F => curvePlaceCompletion v)
    (fun v => (curvePlaceCompletionIntegers v : Set (curvePlaceCompletion v)))
    (fun _ => Valued.isOpen_valuationSubring _)

theorem realAbsoluteValueAdeles_secondCountableTopology :
    SecondCountableTopology (RealAbsoluteValueAdeleRing k F) := by
  let : SecondCountableTopology (CurvePlaceAdeleRing k F) :=
    curvePlaceAdeles_secondCountableTopology k F
  exact (functionFieldAbsoluteValueAdeleHomeomorph k F).secondCountableTopology

omit k in
theorem functionFieldAdelesSecondCountable :
    FunctionFieldAdelesSecondCountableStatement.{u} := by
  intro k F _ _ _ _ _ _ _
  let : SecondCountableTopology (CurvePlaceAdeleRing k F) :=
    curvePlaceAdeles_secondCountableTopology k F
  let : SecondCountableTopology (RealAbsoluteValueAdeleRing k F) :=
    realAbsoluteValueAdeles_secondCountableTopology k F
  exact ⟨functionField_countable k F, curvePlace_countable k F,
    realAbsoluteValuePlace_countable k F,
    curvePlaceCompletion_secondCountableTopology k F,
    realAbsoluteValuePlaceCompletion_secondCountableTopology k F,
    inferInstance,
    fun S => TopologicalSpace.Subtype.secondCountableTopology
      (curvePlaceAdeleLevel k F S : Set (CurvePlaceAdeleRing k F)),
    inferInstance,
    fun S => TopologicalSpace.Subtype.secondCountableTopology
      (realAbsoluteValueAdeleLevel k F S : Set (RealAbsoluteValueAdeleRing k F))⟩

end Langlands.Global
