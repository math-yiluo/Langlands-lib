import Langlands.GroupScheme.SimplyConnected.NormOneGaloisPointMatrix
import Langlands.GroupScheme.MatrixRepresentation.ComponentIntertwiners
import Langlands.GroupScheme.Rational.HighestWeightIntertwiners
import Langlands.GroupScheme.Reductive.TitsAlgebraTransport
import Langlands.GroupScheme.Reductive.TitsObstructionSimplyConnected

/-! # The signed Tits algebras on an actual norm-one presentation -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix TensorProduct

namespace Langlands.GroupScheme.CentralSimpleUnits.SplitRepresentation

open Langlands.CentralSimple Langlands.Brauer MatrixRepresentation TitsDescent

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
    (A : CSA.{u, u} k)
    (e : L ⊗[k] A ≃ₐ[L] Matrix (Fin (reducedDegree k A)) (Fin (reducedDegree k A)) L)

local notation "I" => Fin (reducedDegree k A)
local notation "b" => algebraBaseMap k L
local notation "N" => normOne k A
local notation "Nₗ" => Functor.obj (GroupScheme.baseChange b) (N)

local instance : IsAffineHom (N).X.hom := isAffineHom_of_isAffine _
local instance : IsAffineHom (Nₗ).X.hom := inferInstanceAs
  (IsAffineHom (Limits.pullback.snd (N).X.hom b))

/-- The chart matrices are actual intertwiners with the Galois twists of the column scheme representation. -/
theorem column_intertwines_galoisTwist (σ : L ≃ₐ[k] L) :
    (representation k A e).Intertwines (galoisTwist σ (representation k A e))
      (galoisConjugator e σ : Matrix I I L) := by
  apply (intertwines_iff_universal_pointMatrix _ _ _).mpr
  rw [pointMatrix_transport]
  exact galoisConjugator_representation_pointMatrix e σ _ _

/-- The inverse-transpose matrices intertwine the Galois twists of the actual dual. -/
theorem dual_intertwines_galoisTwist (σ : L ≃ₐ[k] L) :
    Intertwines (dual (representation k A e)) (galoisTwist σ (dual (representation k A e)))
      (dualConjugator e σ : Matrix I I L) := by
  apply (intertwines_iff_universal_pointMatrix _ _ _).mpr
  rw [pointMatrix_transport]
  exact dualConjugator_representation_pointMatrix e σ _ _

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The actual column representation pulled back along a norm-one presentation over the ground field. -/
def representationOn (model : G ≅ (N)) :
    MatrixRepresentation ((GroupScheme.baseChange b).obj G) I :=
  (representation k A e).restrict ((GroupScheme.baseChange b).map model.hom)

variable [LocallyOfFiniteType G.X.hom] [IsGalois k L]
    (d : GaloisPinningData k L G) (hG : IsSimplyConnected G)
    (w : d.starFixedWeights)

/-- On an actual norm-one presentation, the column Tits algebra is the original fixed matrix algebra. -/
theorem column_titsAlgebra_eq_fixed (model : G ≅ (N))
    (hw : d.toSplitPinning.IsHighestWeight (representationOn A e model) w.val) :
    titsAlgebra (representationOn A e model) = (matrixAction e).fixed := by
  let P (σ : L ≃ₐ[k] L) : Matrix I I L := (galoisConjugator e σ).val
  have hP : ∀ σ, (representationOn A e model).Intertwines
      (galoisTwist σ (representationOn A e model)) (P σ) :=
    fun σ => intertwines_restrict_galoisTwist σ (column_intertwines_galoisTwist A e σ) model.hom
  rw [titsAlgebra_eq_twistedFixed _ hw.1
    (SplitPinning.IsHighestWeight.intertwiner_eq_scalar d.toSplitPinning hw) P
    (fun σ => (galoisConjugator e σ).isUnit) hP]
  ext X
  exact (mem_fixed_iff_galoisConjugator e X).symm

/-- On the same presentation, the dual Tits algebra is the actual fixed algebra of the opposite chart. -/
theorem dual_titsAlgebra_eq_oppositeFixed (model : G ≅ (N))
    (hw : d.toSplitPinning.IsHighestWeight (dual (representationOn A e model)) w.val) :
    titsAlgebra (dual (representationOn A e model)) = (matrixAction (oppositeChart e)).fixed := by
  let P (σ : L ≃ₐ[k] L) : Matrix I I L := (dualConjugator e σ).val
  have hP : ∀ σ, Intertwines (dual (representationOn A e model))
      (galoisTwist σ (dual (representationOn A e model))) (P σ) := by
    intro σ
    rw [representationOn, dual_restrict]
    exact intertwines_restrict_galoisTwist σ (dual_intertwines_galoisTwist A e σ) model.hom
  rw [titsAlgebra_eq_twistedFixed _ hw.1
    (SplitPinning.IsHighestWeight.intertwiner_eq_scalar d.toSplitPinning hw) P
    (fun σ => (dualConjugator e σ).isUnit) hP]
  ext X
  exact (mem_oppositeFixed_iff_dualConjugator e X).symm

/-- The highest weight of the column chart has the positive class `[A]`. -/
theorem column_titsObstruction (model : G ≅ (N))
    (hw : d.toSplitPinning.IsHighestWeight (representationOn A e model) w.val) :
    d.titsObstruction hG w = classOf A := by
  rw [d.titsObstruction_eq_classOf hG w hw.isDominantWeight hw]
  apply classOf_eq_of_algEquiv
  change titsAlgebra (representationOn A e model) ≃ₐ[k] A
  exact (Subalgebra.equivOfEq _ _ (column_titsAlgebra_eq_fixed A e d w model hw)).trans
    (fixedEquivOfIsGalois e).symm

/-- The highest weight of the dual chart has the class of the actual opposite algebra. -/
theorem dual_titsObstruction (model : G ≅ (N))
    (hw : d.toSplitPinning.IsHighestWeight (dual (representationOn A e model)) w.val) :
    d.titsObstruction hG w = -classOf A := by
  rw [d.titsObstruction_eq_classOf hG w hw.isDominantWeight hw, ← classOf_opposite]
  apply classOf_eq_of_algEquiv
  change titsAlgebra (dual (representationOn A e model)) ≃ₐ[k] Aᵐᵒᵖ
  exact (Subalgebra.equivOfEq _ _ (dual_titsAlgebra_eq_oppositeFixed A e d w model hw)).trans
    (fixedEquivOfIsGalois (oppositeChart e)).symm

end Langlands.GroupScheme.CentralSimpleUnits.SplitRepresentation
