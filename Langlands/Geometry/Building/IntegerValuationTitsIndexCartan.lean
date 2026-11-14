import Langlands.Geometry.Building.TitsIndexAffineCartanExtension
import Langlands.Geometry.Building.ReducedRelativeApartmentRoots
import Langlands.Geometry.Building.IntegerValuationAffineWeylProof

/-! # Actual integer-valuation apartments and absolute affine Cartan extensions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AffineRootSystem
open GalleryGeometry

section Apartment

variable {L : Type u} [Field L]
  {H : GroupScheme (Spec (CommRingCat.of L))}
  [IsAffineHom H.X.hom]
  {v : Valuation L (WithZero (Multiplicative ℤ))}
  (B : IntegerValuationBuildingData v H)
  (hi : IsMaximalTorus B.i)

include hi

/-- When the apartment's maximal split torus is a maximal torus, its actual
ordinary affine roots have the full relative derivative set. -/
theorem IntegerValuationBuildingData.derivativeRoots_affineRoots_of_maximalTorus :
    derivativeRoots B.affineRoots = Set.range (rootForm B.i) := by
  have hS := B.isMaximalSplitTorus.isSplitSubtorus.1
  obtain ⟨J, hJ, P, hP, hred⟩ :=
    rootDatumExistence L _ B.isConnectedReductive B.S hS B.i hi
  let := hred
  exact B.apartment.derivativeRoots_affineRoots_of_no_double
    (fun _ ha => hP.two_nsmul_not_mem_relativeRoots hS ha)

/-- In the same situation every full derivative has an indivisible actual
ordinary affine lift. -/
theorem IntegerValuationBuildingData.hasIndivisibleDerivativeLifts_of_maximalTorus :
    HasIndivisibleDerivativeLifts B.affineRoots := by
  have hS := B.isMaximalSplitTorus.isSplitSubtorus.1
  obtain ⟨J, hJ, P, hP, hred⟩ :=
    rootDatumExistence L _ B.isConnectedReductive B.S hS B.i hi
  let := hred
  exact B.apartment.hasIndivisibleDerivativeLifts_of_no_double
    (fun _ ha => hP.two_nsmul_not_mem_relativeRoots hS ha) hS

end Apartment

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  [Algebra L (SeparableClosure k)] [IsScalarTower k L (SeparableClosure k)]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)
  {v : Valuation L (WithZero (Multiplicative ℤ))}
  (B : IntegerValuationBuildingData v
    ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))
  (hunit : ∃ t : Lˣ, IntegerValuation.order v t = 1)
  (hi : IsMaximalTorus B.i)

include hunit hi

/-- An actual integer-valuation apartment supplies the affine-system,
full-derivative and indivisible-lift inputs of the absolute Cartan construction. -/
theorem exists_transitive_titsIndexCartanExtension_of_integerValuation
    {c : B.Apartment} (hc : IsRegular B.affineRoots c)
    (hne : B.affineRoots.Nonempty) (hirr : IsIrreducibleRoots B.affineRoots)
    (hmat : AffineCartan.IsVertexTransitive
      (chamberCartanMatrix B.affineRoots (facet B.affineRoots c)))
    (htrans : HasTransitiveSimpleRoots B.affineRoots (facet B.affineRoots c)) :
    ∃ N : Matrix (Option d.Vertex) (Option d.Vertex) ℤ,
      (∀ a b, N (some a) (some b) = d.cartan a b) ∧
      (∀ a, N a a = 2) ∧
      (∀ a b, a ≠ b → N a b ≤ 0) ∧
      (∀ a b, N a b = 0 ↔ N b a = 0) ∧
      (∃ m : Option d.Vertex → ℤ,
        (∀ a, 0 < m a) ∧ Matrix.vecMul m N = 0) ∧
      AffineCartan.IsVertexTransitive N := by
  exact exists_transitive_titsIndexCartanExtension
    d B.isMaximalSplitTorus.isSplitSubtorus.1 hi
    (B.isAffineRootSystemWithRankZero_affineRoots hunit)
    (B.derivativeRoots_affineRoots_of_maximalTorus hi)
    hc hne hirr hmat
    (B.hasIndivisibleDerivativeLifts_of_maximalTorus hi) htrans

/-- The absolute affine Cartan extension chosen from the actual
integer-valuation apartment and its chamber inputs. -/
def integerValuationTitsIndexCartanExtension
    {c : B.Apartment} (hc : IsRegular B.affineRoots c)
    (hne : B.affineRoots.Nonempty) (hirr : IsIrreducibleRoots B.affineRoots)
    (hmat : AffineCartan.IsVertexTransitive
      (chamberCartanMatrix B.affineRoots (facet B.affineRoots c)))
    (htrans : HasTransitiveSimpleRoots B.affineRoots (facet B.affineRoots c)) :
    Matrix (Option d.Vertex) (Option d.Vertex) ℤ :=
  Classical.choose
    (exists_transitive_titsIndexCartanExtension_of_integerValuation
      d B hunit hi hc hne hirr hmat htrans)

/-- The chosen matrix has the exact absolute Cartan block and all six
properties required by the local anisotropic affine-diagram target. -/
theorem integerValuationTitsIndexCartanExtension_spec
    {c : B.Apartment} (hc : IsRegular B.affineRoots c)
    (hne : B.affineRoots.Nonempty) (hirr : IsIrreducibleRoots B.affineRoots)
    (hmat : AffineCartan.IsVertexTransitive
      (chamberCartanMatrix B.affineRoots (facet B.affineRoots c)))
    (htrans : HasTransitiveSimpleRoots B.affineRoots (facet B.affineRoots c)) :
    let N := integerValuationTitsIndexCartanExtension
      d B hunit hi hc hne hirr hmat htrans
    (∀ a b, N (some a) (some b) = d.cartan a b) ∧
      (∀ a, N a a = 2) ∧
      (∀ a b, a ≠ b → N a b ≤ 0) ∧
      (∀ a b, N a b = 0 ↔ N b a = 0) ∧
      (∃ m : Option d.Vertex → ℤ,
        (∀ a, 0 < m a) ∧ Matrix.vecMul m N = 0) ∧
      AffineCartan.IsVertexTransitive N :=
  Classical.choose_spec
    (exists_transitive_titsIndexCartanExtension_of_integerValuation
      d B hunit hi hc hne hirr hmat htrans)

end Langlands.Geometry.Building
