import Langlands.Geometry.Building.LocalAnisotropicAffineDiagramReduction
import Langlands.Geometry.Building.QuasiSplitDerivativeAffineRootsProof
import Langlands.GroupScheme.Rational.RelativeRootSystemIrreducibleProof

/-! # The three remaining inputs for the local anisotropic affine diagram -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- The exact local anisotropic affine-diagram proposition follows from the
three remaining building inputs. Full ordinary derivatives and relative-root
irreducibility are supplied by their published proofs. -/
theorem localAnisotropicAffineDiagram_of_remaining_building_inputs
    (hSpecial : SpecialTorusExistenceStatement.{u})
    (hLift : QuasiSplitIndivisibleDerivativeLiftsStatement.{u})
    (hChamber : UnramifiedSpecialApartmentChamberStatement.{u}) :
    LocalAnisotropicAffineDiagramStatement.{u} :=
  localAnisotropicAffineDiagram_of_building_inputs hSpecial
    quasiSplitDerivativeAffineRoots hLift hChamber relativeRootSystemIrreducible

/-- The absolute affine Cartan matrix with only special-torus existence,
indivisible lifts and the supplied-apartment chamber retained as inputs. -/
def localAnisotropicAffineDiagramMatrixOfRemainingBuildingInputs
    (hSpecial : SpecialTorusExistenceStatement.{u})
    (hLift : QuasiSplitIndivisibleDerivativeLiftsStatement.{u})
    (hChamber : UnramifiedSpecialApartmentChamberStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)
    (habs : IsAbsolutelyAlmostSimple G) (haniso : IsAnisotropic G) :
    Matrix (Option d.Vertex) (Option d.Vertex) ℤ :=
  localAnisotropicAffineDiagramMatrixOfBuildingInputs hSpecial
    quasiSplitDerivativeAffineRoots hLift hChamber relativeRootSystemIrreducible
    F G d habs haniso

/-- The chosen matrix has the exact host's absolute block, generalized Cartan
conditions, positive integral left kernel and vertex transitivity. -/
theorem localAnisotropicAffineDiagramMatrixOfRemainingBuildingInputs_spec
    (hSpecial : SpecialTorusExistenceStatement.{u})
    (hLift : QuasiSplitIndivisibleDerivativeLiftsStatement.{u})
    (hChamber : UnramifiedSpecialApartmentChamberStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)
    (habs : IsAbsolutelyAlmostSimple G) (haniso : IsAnisotropic G) :
    let N := localAnisotropicAffineDiagramMatrixOfRemainingBuildingInputs
      hSpecial hLift hChamber F G d habs haniso
    (∀ a b, N (some a) (some b) = d.cartan a b) ∧
      (∀ a, N a a = 2) ∧
      (∀ a b, a ≠ b → N a b ≤ 0) ∧
      (∀ a b, N a b = 0 ↔ N b a = 0) ∧
      (∃ m : Option d.Vertex → ℤ,
        (∀ a, 0 < m a) ∧ Matrix.vecMul m N = 0) ∧
      AffineCartan.IsVertexTransitive N :=
  localAnisotropicAffineDiagramMatrixOfBuildingInputs_spec hSpecial
    quasiSplitDerivativeAffineRoots hLift hChamber relativeRootSystemIrreducible
    F G d habs haniso

end Langlands.Geometry.Building
