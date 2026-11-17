import Langlands.GroupScheme.Reductive.RootComponentCentralizerFactors
import Langlands.LinearAlgebra.AdjointCartanComponents

/-! # Simple-root component coordinates on pinned charts with root-generated characters -/

noncomputable section

universe u

namespace Langlands.GroupScheme

open Langlands.LinearAlgebra.SimplyConnectedCartanComponents
open Langlands.LinearAlgebra.AdjointCartanComponents

namespace AffinePinnedModel

variable (M : AffinePinnedModel.{u}) (hspan : M.rootDatum.rootSpan ℤ = ⊤)

/-- When the roots of a pinned chart generate its full character lattice, the simple-root
coefficient coordinates are component coordinates for the Cartan components of the pinning
base: every root has simple-root coefficients only in one component. -/
def adjointRootComponentCoordinates : RootComponentCoordinates M :=
  letI : M.rootDatum.IsReduced := M.fibrewiseRootDatum.isReduced
  { characters := simpleRootCoordinates M.basis hspan
    rootComponent := rootComponent M.basis hspan
    root_support := simpleRootCoordinates_root_eq_zero M.basis hspan
    simple_component := rootComponent_simple M.basis hspan }

/-- The character coordinates are the simple-root coefficients. -/
theorem adjointRootComponentCoordinates_characters_apply (x : M.coordinates → ℤ)
    (i : M.basis.support) :
    (M.adjointRootComponentCoordinates hspan).characters x i =
      (simpleRootBasis M.basis hspan).repr x i :=
  rfl

/-- A simple root has coordinate `1` at its own simple index. -/
theorem adjointRootComponentCoordinates_root_self (i : M.basis.support) :
    (M.adjointRootComponentCoordinates hspan).characters (M.rootDatum.root i) i = 1 :=
  simpleRootCoordinates_root_self M.basis hspan i

/-- A simple root has coordinate `0` at every other simple index. -/
theorem adjointRootComponentCoordinates_root_of_ne {i j : M.basis.support} (h : j ≠ i) :
    (M.adjointRootComponentCoordinates hspan).characters (M.rootDatum.root i) j = 0 :=
  simpleRootCoordinates_root_of_ne M.basis hspan h

end AffinePinnedModel

end Langlands.GroupScheme
