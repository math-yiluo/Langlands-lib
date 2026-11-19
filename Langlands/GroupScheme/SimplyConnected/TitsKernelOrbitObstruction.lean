import Langlands.GroupScheme.Reductive.SplitLeviTitsComparison
import Langlands.GroupScheme.SimplyConnected.TitsKernelOrbitWeights

/-! # Tits obstructions of full star orbit weights and the actual anisotropic kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TitsIndexData

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {d : TitsIndexData G}

/-- A full star orbit weight is a star-fixed weight. -/
theorem absoluteOrbitWeight_mem_starFixedWeights (hsc : IsSimplyConnected G) (a : d.Vertex) :
    d.absoluteOrbitWeight hsc a ∈ d.pinning.starFixedWeights :=
  (d.pinning.mem_starFixedWeights _).mpr fun σ => d.absoluteOrbitWeight_star hsc σ a

/-- A full star orbit weight, as an element of the star-fixed weights. -/
def starFixedOrbitWeight (hsc : IsSimplyConnected G) (a : d.Vertex) :
    d.pinning.starFixedWeights :=
  ⟨d.absoluteOrbitWeight hsc a, d.absoluteOrbitWeight_mem_starFixedWeights hsc a⟩

namespace AnisotropicKernelIndex

/-- The restriction of a full star orbit weight to the actual anisotropic kernel, as a
star-fixed weight of the kernel, is the explicit restricted orbit weight. -/
theorem starFixedRestriction_starFixedOrbitWeight (p : d.AnisotropicKernelIndex)
    (hsc : IsSimplyConnected G) (a : d.Vertex) :
    ((p.leviComparison.starFixedRestriction
        (p.index.pinning.corootSpan_eq_top_of_simplyConnected (p.isSimplyConnected hsc))
        (d.starFixedOrbitWeight hsc a) : p.index.pinning.starFixedWeights) :
      characterLattice p.index.pinning.toSplitPinning.torus) =
      p.restrictedOrbitWeight hsc a :=
  p.weightRestriction_absoluteOrbitWeight hsc a

/-- Clause 3: the actual Tits obstruction of a full star orbit weight of `G` is the actual
Tits obstruction of the kernel at its restriction. -/
theorem titsObstruction_starFixedOrbitWeight (p : d.AnisotropicKernelIndex)
    (hsc : IsSimplyConnected G) (a : d.Vertex) :
    d.pinning.titsObstruction hsc (d.starFixedOrbitWeight hsc a) =
      p.index.pinning.titsObstruction (p.isSimplyConnected hsc)
        ⟨p.restrictedOrbitWeight hsc a, by
          rw [← p.starFixedRestriction_starFixedOrbitWeight hsc a]
          exact Subtype.property _⟩ := by
  rw [p.titsObstruction_eq hsc]
  congr 1
  exact Subtype.ext (p.starFixedRestriction_starFixedOrbitWeight hsc a)

/-- Clause 3, orbits inside the zero vertices: the obstruction of the orbit weight at a zero
vertex `a` is the obstruction of the kernel at the kernel orbit weight of the corresponding
kernel vertex. -/
theorem titsObstruction_starFixedOrbitWeight_of_zero (p : d.AnisotropicKernelIndex)
    (hsc : IsSimplyConnected G) (a : d.zeroVertices) :
    d.pinning.titsObstruction hsc (d.starFixedOrbitWeight hsc a.val) =
      p.index.pinning.titsObstruction (p.isSimplyConnected hsc)
        (p.index.starFixedOrbitWeight (p.isSimplyConnected hsc)
          (p.comparison.vertexEquiv.symm a)) := by
  rw [p.titsObstruction_eq hsc]
  congr 1
  apply Subtype.ext
  exact p.weightRestriction_absoluteOrbitWeight_of_zero hsc a

/-- Clause 3, orbits disjoint from the zero vertices: the obstruction of the orbit weight at a
distinguished vertex vanishes. -/
theorem titsObstruction_starFixedOrbitWeight_of_not_zero (p : d.AnisotropicKernelIndex)
    (hsc : IsSimplyConnected G) (a : d.Vertex) (ha : a ∉ d.zeroVertices) :
    d.pinning.titsObstruction hsc (d.starFixedOrbitWeight hsc a) = 0 := by
  rw [p.titsObstruction_eq hsc]
  have h0 : p.leviComparison.starFixedRestriction
      (p.index.pinning.corootSpan_eq_top_of_simplyConnected (p.isSimplyConnected hsc))
      (d.starFixedOrbitWeight hsc a) = 0 :=
    Subtype.ext (p.weightRestriction_absoluteOrbitWeight_of_not_zero hsc a ha)
  rw [h0, map_zero]

end AnisotropicKernelIndex

end Langlands.GroupScheme.TitsIndexData
