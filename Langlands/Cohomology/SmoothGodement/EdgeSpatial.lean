import Langlands.Cohomology.SmoothGodement.CoefficientInvariants
import Mathlib.CategoryTheory.Comma.Arrow

/-! # Proper spatial maps of the full coefficient invariants edge -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

namespace Langlands.Cohomology.SmoothGodementCohomology.Spatial

open CategoryTheory HomologicalComplex
open Langlands.Sheaf.Equivariant
open Langlands.Cohomology.SmoothGodementComparison

variable (R : Type u) [CommRing R] (G : Type u) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (X : Type u) [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X]

/-- The canonical invariants edge on the full smooth coefficient sheaves. -/
def coefficientInvariantsEdge (q : ℕ) :
    LocallyConstantSheaf.smoothFunctor R G X ⋙
        smoothGodementInvariantCompactCohomology R G X q ⟶
      (LocallyConstantSheaf.smoothFunctor R G X ⋙
        smoothGodementCompactCohomology R G X q) ⋙ smoothInvariants R G :=
  Functor.whiskerLeft (LocallyConstantSheaf.smoothFunctor R G X)
    (godementEdge (X := X) (smoothInvariants R G) q)

/-- Retain both cohomology functors and their canonical edge in the arrow category. -/
def coefficientInvariantsEdgeArrow (q : ℕ) :
    Arrow (Langlands.SmoothRep.{u, u, u} R G ⥤ ModuleCat.{u} R) :=
  Arrow.mk (coefficientInvariantsEdge R G X q)

instance isIso_coefficientInvariantsEdge_zero :
    IsIso (coefficientInvariantsEdge R G X 0) :=
  inferInstanceAs (IsIso (Functor.whiskerLeft _ _))

/-- All-degree invertibility retains the explicit preservation-of-homology hypothesis. -/
instance isIso_coefficientInvariantsEdge
    [(smoothInvariants R G).PreservesHomology] (q : ℕ) :
    IsIso (coefficientInvariantsEdge R G X q) :=
  inferInstanceAs (IsIso (Functor.whiskerLeft _ _))

variable {R G X}
  {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G Y] [MulAction G Z]
  [ContinuousConstSMul G Y] [ContinuousConstSMul G Z]
  [HasStableNeighbourhoods G Y] [HasStableNeighbourhoods G Z]
  (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- The actual proper compact chain map makes the invariants edge spatially natural. -/
@[reassoc]
theorem coefficientInvariantsEdge_pullback (hp : IsProperMap f) (q : ℕ) :
    coefficientInvariantCohomologyNatTrans f hf hp q ≫ coefficientInvariantsEdge R G X q =
      coefficientInvariantsEdge R G Y q ≫
        Functor.whiskerRight (coefficientCohomologyNatTrans f hf hp q) (smoothInvariants R G) := by
  apply NatTrans.ext
  funext M
  change (homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q).map
      ((coefficientInvariantCompactNatTrans f hf hp).app M) ≫ _ = _
  rw [coefficientInvariantCompactNatTrans_app_eq_map]
  exact (LeftExactHomology.homologyNatTrans (smoothInvariants R G)
    (ComplexShape.up ℕ) q).naturality ((coefficientCompactNatTrans f hf hp).app M)

/-- Proper pullback is a morphism between the full coefficient edge arrows. -/
def coefficientInvariantsEdgePullback (hp : IsProperMap f) (q : ℕ) :
    coefficientInvariantsEdgeArrow R G Y q ⟶ coefficientInvariantsEdgeArrow R G X q :=
  Arrow.homMk (coefficientInvariantCohomologyNatTrans f hf hp q)
    (Functor.whiskerRight (coefficientCohomologyNatTrans f hf hp q) (smoothInvariants R G))
    (coefficientInvariantsEdge_pullback f hf hp q)

@[simp]
theorem coefficientInvariantsEdgePullback_left (hp : IsProperMap f) (q : ℕ) :
    (coefficientInvariantsEdgePullback (R := R) f hf hp q).left =
      coefficientInvariantCohomologyNatTrans f hf hp q := rfl

@[simp]
theorem coefficientInvariantsEdgePullback_right (hp : IsProperMap f) (q : ℕ) :
    (coefficientInvariantsEdgePullback (R := R) f hf hp q).right =
      Functor.whiskerRight (coefficientCohomologyNatTrans f hf hp q) (smoothInvariants R G) := rfl

@[simp]
theorem coefficientInvariantsEdgePullback_id (q : ℕ) :
    coefficientInvariantsEdgePullback (R := R) (ContinuousMap.id X)
        (fun (_ : G) (_ : X) => rfl) isProperMap_id q =
      𝟙 (coefficientInvariantsEdgeArrow R G X q) := by
  apply Arrow.hom_ext
  · exact coefficientInvariantCohomologyNatTrans_id q
  · simp [coefficientInvariantsEdgePullback, coefficientInvariantsEdgeArrow]

/-- Strict contravariant composition holds for the entire commutative square. -/
theorem coefficientInvariantsEdgePullback_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g) (q : ℕ) :
    coefficientInvariantsEdgePullback (R := R) (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
        (hq.comp hp) q =
      coefficientInvariantsEdgePullback g hg hq q ≫ coefficientInvariantsEdgePullback f hf hp q := by
  apply Arrow.hom_ext
  · exact coefficientInvariantCohomologyNatTrans_comp f hf g hg hp hq q
  · change Functor.whiskerRight
        (coefficientCohomologyNatTrans (g.comp f) _ (hq.comp hp) q) _ = _
    rw [coefficientCohomologyNatTrans_comp f hf g hg hp hq q]
    rfl

end Langlands.Cohomology.SmoothGodementCohomology.Spatial
