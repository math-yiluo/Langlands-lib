import Langlands.AlgebraicGeometry.Modules.RelativeAbelianSheafCohomologyPullbackStatement
import Langlands.AlgebraicGeometry.Picard.SquareZeroMorphismObstructionNaturality
import Langlands.AlgebraicGeometry.Picard.SquareZeroObstructionMorphismNaturalityStatement

/-! # Reduction of Picard obstruction naturality to relative cohomology comparison -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.Picard.SquareZeroMorphismRelativeComparison

open Langlands.AlgebraicGeometry.Modules
open Modules.AbelianSheafComparison Modules.DerivedSections
open SquareZeroUnitCohomology SquareZeroRelativeObstructionNaturality
open SquareZeroMorphismObstructionNaturality StructureKernelModule

variable {R : CommRingCat.{u}} {X X' : Over (Spec R)} (f : X' ⟶ X)
  {Y Y' : Scheme.{u}} (i : Y ⟶ X.left) (i' : Y' ⟶ X'.left)
  (k : kernelModule i ⟶ (Scheme.Modules.pushforward f.left).obj (kernelModule i'))

/-- The actual relative ideal-cohomology map: pullback followed by the adjoint
of the coefficient arrow. -/
def relativeIdealCohomologyMap (n : ℕ) :
    (relativeCohomology X.hom n).obj (kernelModule i) →+
      (relativeCohomology X'.hom n).obj (kernelModule i') :=
  (((relativeCohomology X'.hom n).map
      (((Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv _ _).symm k)).hom.toAddMonoidHom).comp
    (relativeCohomologyPullback f (kernelModule i) n).hom.toAddMonoidHom

/-- The general relative comparison specializes to the actual ideal modules. -/
lemma idealCohomologyMap_relative
    (h : RelativeAbelianSheafCohomologyPullbackStatement.{u})
    (n : ℕ) (x : idealCohomology i n) :
    relativeIdealCohomologyAddEquiv X'.hom i' n
        (idealCohomologyMap f.left i i' k n x) =
      relativeIdealCohomologyMap f i i' k n
        (relativeIdealCohomologyAddEquiv X.hom i n x) := by
  have hc := h R X X' f (kernelModule i) (kernelModule i') k n
    ((idealCohomologyAddEquiv i n).symm x)
  change relativeIdealCohomologyAddEquiv X'.hom i' n
      (idealCohomologyMap f.left i i' k n x) =
    relativeIdealCohomologyMap f i i' k n
      (relativeIdealCohomologyAddEquiv X.hom i n
        (idealCohomologyAddEquiv i n ((idealCohomologyAddEquiv i n).symm x))) at hc
  simpa only [AddEquiv.apply_symm_apply] using hc

/-- The full obstruction target follows from the general relative comparison. -/
theorem squareZeroObstructionMorphismNaturality_of_relativeComparison
    (h : RelativeAbelianSheafCohomologyPullbackStatement.{u}) :
    SquareZeroObstructionMorphismNaturalityStatement.{u} := by
  intro R X X' f Y Y' i i' g _ _ _ _ _ _ hi hi' w k hk y
  rw [SquareZeroMorphismObstructionNaturality.obstructionMap_naturality
    f.left i i' g w hi hi' k hk y]
  exact idealCohomologyMap_relative f i i' k h 2 _

end Langlands.AlgebraicGeometry.Picard.SquareZeroMorphismRelativeComparison
