import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedCompactness
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.Representation.Plancherel.RationalCharacterTopology
import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# Bounded subgroups and the actual rational norm kernel

Algebraic boundedness gives compact closure in the canonical local-field point
topology. A closed immersion pulls this compact closure back to the source,
where the compact subgroup argument uses the source's own rational characters.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (X : Over (Spec (CommRingCat.of F))) [IsAffine X.left]

local instance : TopologicalSpace (RationalPoint F X) := rationalPointTopology F X

/-- Each regular-function bound extends to the closure in the canonical point topology. -/
theorem IsAlgebraicallyBounded.closure {B : Set (RationalPoint F X)}
    (hB : IsAlgebraicallyBounded F X B) :
    IsAlgebraicallyBounded F X (_root_.closure B) := by
  intro f
  obtain ⟨b, hb, hf⟩ := hB f
  refine ⟨b, hb, ?_⟩
  let e := (rationalPointHomeomorph F X).trans (affineSchemePointHomeomorph F X F)
  have hc : Continuous (fun p : RationalPoint F X => rationalPointAlgebraHom F X p f) :=
    (AlgPoint.continuous_eval f).comp e.continuous
  have hclosed : IsClosed {p : RationalPoint F X | rationalPointAlgebraHom F X p f ≤ᵥ b} := by
    have hball := (ValuativeRel.valuation F).isClosed_closedBall
      ((ValuativeRel.valuation F).restrict b)
    have hclosed' : IsClosed {p : RationalPoint F X |
        (ValuativeRel.valuation F) (rationalPointAlgebraHom F X p f) ≤
          (ValuativeRel.valuation F) b} := by
      simpa only [Set.preimage_ofPred_eq, Valuation.restrict_le_iff] using hball.preimage hc
    convert hclosed' using 1
    ext p
    exact (ValuativeRel.valuation F).vle_iff_le
  exact closure_minimal hf hclosed

/-- Bounded sets of finite-type affine local-field points have compact closure. -/
theorem IsAlgebraicallyBounded.isCompact_closure [LocallyOfFiniteType X.hom]
    {B : Set (RationalPoint F X)} (hB : IsAlgebraicallyBounded F X B) :
    IsCompact (_root_.closure B) :=
  (localFieldAffineBoundedCompactness_proof F X _ isClosed_closure).1 (hB.closure X)

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

open Langlands.AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- A subgroup with compact closure lies in the actual common rational norm kernel. -/
theorem subgroup_le_rationalCommonNormKernel_of_isCompact_closure
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (Q : Subgroup (rationalPoints G)) :
    let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsCompact (closure (Q : Set (rationalPoints G))) →
      Q ≤ rationalCommonNormKernel G := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  dsimp only
  intro hQ
  exact Q.le_topologicalClosure.trans
    (compactSubgroup_le_rationalCommonNormKernel G Q.topologicalClosure hQ)

/-- A closed immersion pulls a compact closure back; the norm kernel in the
conclusion is that of the source group scheme. -/
theorem comap_le_rationalCommonNormKernel_of_isCompact_closure
    {G H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine G.X.left] [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
    (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (Q : Subgroup (rationalPoints G)) :
    let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsCompact (closure (Q : Set (rationalPoints G))) →
      Q.comap (rationalPoints.map j) ≤ rationalCommonNormKernel H := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : TopologicalSpace (rationalPoints H) := rationalPointTopology F H.X
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  let : IsClosedImmersion j.hom.hom.left := hj
  dsimp only
  intro hQ
  have he : IsClosedEmbedding (rationalPoints.map j) :=
    isClosedEmbedding_rationalPointMap F j.hom.hom
  apply subgroup_le_rationalCommonNormKernel_of_isCompact_closure H
  refine (he.isCompact_preimage hQ).of_isClosed_subset isClosed_closure ?_
  exact closure_minimal
    (fun p hp => subset_closure hp)
    (isClosed_closure.preimage he.continuous)

/-- Algebraic boundedness in the ambient affine finite-type group suffices for
membership in the source norm kernel after a closed-immersion pullback. -/
theorem comap_le_rationalCommonNormKernel_of_isAlgebraicallyBounded
    {G H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine G.X.left] [IsAffine H.X.left]
    [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
    (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (Q : Subgroup (rationalPoints G))
    (hQ : IsAlgebraicallyBounded F G.X (Q : Set (rationalPoints G))) :
    Q.comap (rationalPoints.map j) ≤ rationalCommonNormKernel H :=
  comap_le_rationalCommonNormKernel_of_isCompact_closure j hj Q
    (hQ.isCompact_closure G.X)

end Langlands.Plancherel
