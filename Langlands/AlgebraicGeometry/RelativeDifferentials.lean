import Langlands.AlgebraicGeometry.PresheafRelativeDifferentials
import Langlands.AlgebraicGeometry.SheafifyRelativeDerivations

/-!
# Relative differential sheaves on schemes

The module sheaf of relative differentials is the sheafification of the
concrete presheaf of relative differentials.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace Langlands.Scheme

variable {X S : AlgebraicGeometry.Scheme.{u}}

/-- The sheaf of relative Kähler differentials of a scheme morphism. -/
def relativeDifferentials (f : X ⟶ S) : X.Modules :=
  (moduleSheafification X).obj
    (Langlands.PresheafDifferentials.relativeDifferentials (F := Opens.map f.base) f.c)

/-- The relative derivation into the constructed differential sheaf. -/
def relativeDifferentialsDerivation (f : X ⟶ S) :
    RelativeDerivation f (relativeDifferentials f) :=
  sheafifyRelativeDerivation (Langlands.PresheafDifferentials.derivation f.c)

end Langlands.Scheme
