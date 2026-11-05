import Langlands.Geometry.Building.SharpFixerBoundednessStatement
import Langlands.Geometry.Building.KPRootFixerTopology

/-!
# Boundedness from a finite root-product cover

This conditional adapter isolates the finite-cover and sharp-normalizer
boundedness inputs. It does not establish either structural input.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

local instance sharpFixerBoundednessReductionInst1 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance sharpFixerBoundednessReductionInst2 : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

/-- A finite product of actual zero-depth root blocks and an algebraically
bounded sharp normalizer bounds the singleton sharp fixer it covers. -/
theorem isAlgebraicallyBounded_sharpFixer_of_finiteProductCover
    (hB : B.apartment.IsTopologyCompatible) (x : B.Apartment)
    {n m : ℕ} (a : Fin n → relativeRoots B.i) (b : Fin m → relativeRoots B.i)
    (hN : IsAlgebraicallyBounded F G.X
      (B.apartment.sharpNormalizer {x} : Set (rationalPoints G)))
    (hcover : (B.sharpFixer {x} : Set (rationalPoints G)) ⊆
      Set.range (B.apartment.orderedFiltrationBlockProduct x (fun _ => 0)
        (fun j => (a j : characterLattice B.S))) *
      Set.range (B.apartment.orderedFiltrationBlockProduct x (fun _ => 0)
        (fun j => (b j : characterLattice B.S))) *
      (B.apartment.sharpNormalizer {x} : Set (rationalPoints G))) :
    IsAlgebraicallyBounded F G.X (B.sharpFixer {x} : Set (rationalPoints G)) := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  let : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  have hcompact := ((B.isCompact_range_orderedFiltrationBlockProduct hB x
    (fun _ => 0) a).mul (B.isCompact_range_orderedFiltrationBlockProduct hB x
      (fun _ => 0) b)).mul (hN.isCompact_closure G.X)
  have hbound := (localFieldAffineBoundedCompactness_proof F G.X _
    hcompact.isClosed).2 hcompact
  intro f
  obtain ⟨c, hc, hf⟩ := hbound f
  exact ⟨c, hc, fun g hg =>
    hf g ((Set.mul_subset_mul_left subset_closure) (hcover hg))⟩

/-- The conditional finite-product criterion, with both structural obligations
explicit and without changing the exact boundedness target. -/
def SharpFixerFiniteProductBoundednessStatement : Prop :=
  B.apartment.IsTopologyCompatible →
    ∀ (x : B.Apartment) (n m : ℕ)
      (a : Fin n → relativeRoots B.i) (b : Fin m → relativeRoots B.i),
      IsAlgebraicallyBounded F G.X
        (B.apartment.sharpNormalizer {x} : Set (rationalPoints G)) →
      (B.sharpFixer {x} : Set (rationalPoints G)) ⊆
        Set.range (B.apartment.orderedFiltrationBlockProduct x (fun _ => 0)
          (fun j => (a j : characterLattice B.S))) *
        Set.range (B.apartment.orderedFiltrationBlockProduct x (fun _ => 0)
          (fun j => (b j : characterLattice B.S))) *
        (B.apartment.sharpNormalizer {x} : Set (rationalPoints G)) →
      IsAlgebraicallyBounded F G.X (B.sharpFixer {x} : Set (rationalPoints G))

/-- The finite-product criterion follows from compact actual block ranges and
compact closure of the actual sharp normalizer. -/
theorem sharpFixerFiniteProductBoundedness :
    B.SharpFixerFiniteProductBoundednessStatement := by
  intro hB x n m a b hN hcover
  exact B.isAlgebraicallyBounded_sharpFixer_of_finiteProductCover hB x a b hN hcover

end Langlands.Geometry.Building.ValuationBuildingData
