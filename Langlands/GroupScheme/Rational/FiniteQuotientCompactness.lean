import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Compactness from a compact subgroup and a finite schematic quotient -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Topology

/-- A group with a compact kernel and finite homomorphic image is compact.
Surjectivity onto the given codomain is not required. -/
theorem compactSpace_of_finite_image_of_isCompact_ker
    {G : Type u} {H : Type v} [Group G] [Group H] [TopologicalSpace G]
    [ContinuousMul G] (f : G →* H) [Finite f.range]
    (hk : IsCompact (f.ker : Set G)) : CompactSpace G := by
  classical
  let s : f.range → G := fun y => Classical.choose y.property
  have hs (y : f.range) : f (s y) = y.val := Classical.choose_spec y.property
  have hcover : (Set.univ : Set G) =
      ⋃ y : f.range, (fun x : G => s y * x) '' (f.ker : Set G) := by
    symm
    apply Set.eq_univ_iff_forall.mpr
    intro g
    let y : f.range := ⟨f g, g, rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨y, (s y)⁻¹ * g, ?_, ?_⟩
    · change f ((s y)⁻¹ * g) = 1
      rw [map_mul, map_inv, hs]
      exact inv_mul_cancel (f g)
    · exact mul_inv_cancel_left (s y) g
  apply isCompact_univ_iff.mp
  rw [hcover]
  exact isCompact_iUnion fun y => hk.image (continuous_const.mul continuous_id)

end Langlands.Topology

namespace Langlands.AlgebraicGeometry.PointTopology

variable (k : Type u) [Field k]

/-- A finite scheme has a finite-dimensional actual affine coordinate algebra,
including when the scheme has nilpotents. -/
theorem affineCoordinate_finite_of_isFinite
    (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] [IsFinite X.hom] :
    Module.Finite k (AffineCoordinateRing k X) := by
  apply RingHom.finite_algebraMap.mp
  apply (IsFinite.SpecMap_iff
    (CommRingCat.ofHom (algebraMap k (AffineCoordinateRing k X)))).mp
  change IsFinite (Spec.algebraMap k (AffineCoordinateRing k X))
  rw [affineCoordinateSpecMap]
  exact MorphismProperty.IsStableUnderComposition.comp_mem X.left.isoSpec.inv X.hom
    (by infer_instance) (by infer_instance)

/-- Points of a finite scheme in any field extension form a finite set.
No smoothness, reducedness or separability condition is imposed. -/
theorem finite_ringPoint_of_isFinite
    (X : Over (Spec (CommRingCat.of k))) [IsFinite X.hom]
    (K : Type u) [Field K] [Algebra k K] : Finite (RingPoint k X K) := by
  let : IsAffine X.left := isAffine_of_isAffineHom X.hom
  let : Module.Finite k (AffineCoordinateRing k X) :=
    affineCoordinate_finite_of_isFinite k X
  exact Finite.of_equiv (AffineCoordinateRing k X →ₐ[k] K)
    ((affineSchemePointEquiv k X K).trans AlgPoint.algHomEquiv).symm

/-- The actual identity-test rational points of a finite scheme are finite. -/
theorem finite_rationalPoint_of_isFinite
    (X : Over (Spec (CommRingCat.of k))) [IsFinite X.hom] :
    Finite (RationalPoint k X) := by
  let : Finite (RingPoint k X k) := finite_ringPoint_of_isFinite k X k
  exact Finite.of_equiv (RingPoint k X k) (rationalPointEquiv k X).symm

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    {H G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffine H.X.left] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- A compact actual subgroup and a finite actual scheme target with exactly
that kernel imply compactness of the entire canonical rational-point group.
No surjectivity of the point map to `Q` is assumed. -/
theorem compactSpace_rationalPoints_of_finite_quotient
    (z : H ⟶ G) (q : G ⟶ Q) [IsFinite Q.X.hom]
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range z)
    (hH : let : TopologicalSpace (rationalPoints H) := rationalPointTopology k H.X
      CompactSpace (rationalPoints H)) :
    let : TopologicalSpace (rationalPoints G) := rationalPointTopology k G.X
    CompactSpace (rationalPoints G) := by
  let : TopologicalSpace (rationalPoints H) := rationalPointTopology k H.X
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology k G.X
  let : CompactSpace (rationalPoints H) := hH
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup k G
  let : Finite (rationalPoints Q) := finite_rationalPoint_of_isFinite k Q.X
  have hr : Set.range (fun p : rationalPoints H => p ≫ z.hom.hom) =
      ((rationalPoints.map q).ker : Set (rationalPoints G)) := by
    ext p
    change p ∈ (SubgroupFunctor.range z).carrier _ ↔
      p ≫ q.hom.hom = 1
    rw [← hker, mem_range_kernelι_iff]
  apply Langlands.Topology.compactSpace_of_finite_image_of_isCompact_ker
    (rationalPoints.map q)
  rw [← hr]
  exact isCompact_range (continuous_rationalPointMap k z.hom.hom)

/-- The finite schematic-quotient compactness theorem for an explicit
represented fppf quotient. Point-surjectivity is still unnecessary. -/
theorem compactSpace_rationalPoints_of_finite_fppf_quotient
    (N : SubgroupFunctor G) (z : H ⟶ G) (hz : N.IsRepresentedBy z)
    (q : G ⟶ Q) (hq : RelativeRoot.IsFppfQuotient N q) [IsFinite Q.X.hom]
    (hH : let : TopologicalSpace (rationalPoints H) := rationalPointTopology k H.X
      CompactSpace (rationalPoints H)) :
    let : TopologicalSpace (rationalPoints G) := rationalPointTopology k G.X
    CompactSpace (rationalPoints G) :=
  compactSpace_rationalPoints_of_finite_quotient z q (hq.2.2.2.trans hz.2.symm) hH

end Langlands.GroupScheme
