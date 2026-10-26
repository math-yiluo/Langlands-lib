import Langlands.AlgebraicGeometry.Picard.MumfordParameterAxes
import Langlands.AlgebraicGeometry.Picard.RelativeCubeDualComparison

/-! # Reduction of actual Mumford parameter additivity to ordinary cube triviality -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonoidalCategory CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- The ordinary three-face cube criterion on the self-product of an abelian scheme.
This proposition is an explicit geometric premise, not an established theorem. -/
def MumfordSelfCubeTriviality {S : Scheme.{u}} (A : AbelianScheme S) : Prop :=
  ∀ D : LineBundle (A.X ⨯ (A.X ⨯ A.X)).left,
    Nonempty ((Scheme.Modules.pullback
      (CubeFace.first A.X A.X A.X (1 : Over.mk (𝟙 S) ⟶ A.X)).left).obj D.obj ≅
        structureSheaf (A.X ⨯ A.X).left) →
    Nonempty ((Scheme.Modules.pullback
      (CubeFace.second A.X A.X A.X (1 : Over.mk (𝟙 S) ⟶ A.X)).left).obj D.obj ≅
        structureSheaf (A.X ⨯ A.X).left) →
    Nonempty ((Scheme.Modules.pullback
      (CubeFace.third A.X A.X A.X (1 : Over.mk (𝟙 S) ⟶ A.X)).left).obj D.obj ≅
        structureSheaf (A.X ⨯ A.X).left) →
    Nonempty (D.obj ≅ structureSheaf (A.X ⨯ (A.X ⨯ A.X)).left)

/-- Ordinary cube triviality on abelian self-products implies the exact full-family
parameter-additivity statement. The geometric cube premise remains explicit. -/
theorem mumfordBundleParameterAdditivity_of_ordinaryCubeTriviality
    (triviality : ∀ (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S),
      MumfordSelfCubeTriviality A) :
    MumfordBundleParameterAdditivityStatement.{u} := by
  intro preservation S _ A L M evaluation
  apply rigidifiedClasses_eq_of_ordinaryCubeTriviality preservation A A A (triviality S A)
  · exact mumfordBundleParameterAdditivity_firstAxis A preservation L M evaluation
  · exact mumfordBundleParameterAdditivity_secondAxis A preservation L M evaluation

end Langlands.AbelianScheme
