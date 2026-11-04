import Langlands.GroupScheme.Rational.SemigroupFppfKernelTransport
import Langlands.GroupScheme.Rational.SemigroupComparisonFivePrerequisites

/-! # Semigroup comparison from four structural prerequisites -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- A fixed centre-containing split torus supplies full kernel containment,
so the actual adjoint semigroup image follows without smoothness of the centre. -/
theorem semigroupAdjointImage_of_fixedCenterContainingTorus
    (hFixed : FixedCenterContainingTorusStatement.{u}) :
    SemigroupAdjointImageStatement.{u} := by
  intro k _ _ G Q hAffG hAffQ S hS b c q hq heq A hzero
  let : IsAffineHom G.X.hom := hAffG
  let : IsAffineHom Q.X.hom := hAffQ
  let : Smooth G.X.hom := hq.isConnectedReductive.smooth
  let : Smooth Q.X.hom := hq.isAdjoint.isSemisimple.isConnectedReductive.smooth
  let : Flat q.hom.hom.left := hq.flat
  let : Surjective q.hom.hom.left := hq.surjective
  let : LocallyOfFinitePresentation q.hom.hom.left := hq.locallyOfFinitePresentation
  apply isFppfImage_semigroup_of_kernel_le b c q heq hS A
  rw [hq.kernel_range_eq_center]
  exact center_le_semigroupSubgroup_of_fixedCenterContainingTorus
    hFixed hq.isConnectedReductive hS b A hzero

/-- The four remaining structural inputs to the exact full semigroup comparison.
Full-centre containment, adjoint semigroup image and radical intersection all
follow from the fixed centre-containing torus component. -/
def SemigroupComparisonFourPrerequisites : Prop :=
  AdjointQuotientExistenceStatement.{u} ∧
    FixedCenterContainingTorusStatement.{u} ∧
    NormalAdjointEquivariantRetractionStatement.{u} ∧
    Torus.SolvableFixedContainmentConnectedStatement.{u}

/-- Recover the existing five-input interface from the four retained inputs. -/
theorem SemigroupComparisonFourPrerequisites.fivePrerequisites
    (h : SemigroupComparisonFourPrerequisites.{u}) :
    SemigroupComparisonPrerequisites.{u} :=
  ⟨h.1, h.2.1, semigroupAdjointImage_of_fixedCenterContainingTorus h.2.1,
    h.2.2.1, h.2.2.2⟩

/-- The four retained propositions imply the exact existing comparison, at
every universe and with all three intersection alternatives intact. -/
theorem semigroupComparison_of_fourPrerequisites
    (h : SemigroupComparisonFourPrerequisites.{u}) :
    SemigroupComparisonStatement.{u} :=
  semigroupComparison_of_fivePrerequisites h.fivePrerequisites

end Langlands.GroupScheme.RelativeRoot
