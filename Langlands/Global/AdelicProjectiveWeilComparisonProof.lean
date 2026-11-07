import Langlands.Global.AdelicProjectiveWeilComparisonStatement

/-! # Proof of the canonical adelic Weil comparison -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry IntermediateField

namespace Langlands.Global

set_option backward.isDefEq.respectTransparency false

/-- Construct an arithmetic model internally and identify its homeomorphism with the counit. -/
theorem numberFieldAdelicProjectiveWeilComparison :
    NumberFieldAdelicProjectiveWeilComparisonStatement.{u} := by
  intro K L _ _ _ _ _ X _ n j _ U V P Q _ _ _ _ e f
  let := numberFieldSpreadAdelePointTopology K U P _ e
  let := numberFieldSpreadAdelePointTopology L V Q _ f
  let M := numberFieldExtensionProjectiveModel K L ∅ ∅ X n j
  let h := NumberFieldProjectiveWeilAdeleHomeomorph.adelicPointHomeomorphOfSpreads
    K L ∅ ∅ X n j M U V P Q e f
  have heq : (⇑h) = NumberFieldProjectiveWeilAdeleEvaluation.adelicEvaluation K L X n j := by
    funext p
    exact NumberFieldProjectiveWeilAdeleEvaluation.adelicPointHomeomorphOfSpreads_eq_evaluation
      K L X n j ∅ ∅ M U V P Q e f p
  rw [← heq]
  exact @Homeomorph.isHomeomorph _ _ _ _ h

/-- Use the given lower presentation to construct the curve model, without separability. -/
theorem curvePlaceAdelicProjectiveWeilComparison :
    CurvePlaceAdelicProjectiveWeilComparisonStatement.{u} := by
  intro k K L _ _ _ _ _ _ _ _ _ _ _ _
  let : Algebra (RatFunc k) L :=
    ((algebraMap K L).comp (algebraMap (RatFunc k) K)).toAlgebra
  let : IsScalarTower (RatFunc k) K L := .of_algebraMap_eq fun _ => rfl
  let : IsScalarTower k (RatFunc k) L :=
    .of_algebraMap_eq fun a => by
      change algebraMap k L a =
        algebraMap K L (algebraMap (RatFunc k) K (algebraMap k (RatFunc k) a))
      rw [← IsScalarTower.algebraMap_apply k (RatFunc k) K,
        ← IsScalarTower.algebraMap_apply k K L]
  let : FunctionField k L := Module.Finite.trans (R := RatFunc k) K L
  intro X _ n j _ U V P Q _ _ _ _ e f
  let := curvePlaceSpreadAdelePointTopology k K U P _ e
  let := curvePlaceSpreadAdelePointTopology k L V Q _ f
  let s := algebraMap (RatFunc k) K (RatFunc.X : RatFunc k)
  let : FiniteDimensional k⟮s⟯ K := FunctionField.FiniteDimensional.adjoin_algebraMap_X
  let M := curvePlaceFunctionFieldProjectiveModel k K L ∅ ∅ X n j
  let h := CurvePlaceProjectiveWeilAdeleHomeomorph.adelicPointHomeomorphOfSpreads
    k K L s ∅ ∅ X n j M U V P Q e f
  have heq : (⇑h) = CurvePlaceProjectiveWeilAdeleEvaluation.adelicEvaluation k K L X n j := by
    funext p
    exact CurvePlaceProjectiveWeilAdeleEvaluation.adelicPointHomeomorphOfSpreads_eq_evaluation
      k K L X n j s ∅ ∅ M U V P Q e f p
  rw [← heq]
  exact @Homeomorph.isHomeomorph _ _ _ _ h

/-- The original-field canonical adelic Weil map is a homeomorphism in both characteristics. -/
theorem adelicProjectiveWeilComparison : AdelicProjectiveWeilComparisonStatement.{u} :=
  ⟨curvePlaceAdelicProjectiveWeilComparison, numberFieldAdelicProjectiveWeilComparison⟩

end Langlands.Global
