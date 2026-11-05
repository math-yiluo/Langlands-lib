import Langlands.GroupScheme.AffineWeilRestrictionTopology
import Langlands.GroupScheme.Rational.PointTopology
import Langlands.GroupScheme.GaloisPointRational

/-! # Continuity of the affine Weil-restriction point comparison without a module topology -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

open Langlands.Algebra

section AlgPoints

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Module.Finite A B] [Module.Projective A B]
  [Algebra.FiniteType B C]
  [TopologicalSpace A] [TopologicalSpace B] [ContinuousSMul A B] [ContinuousAdd B]

/-- The representing bijection from `A`-points of the Weil restriction to `B`-points is
continuous as soon as scalar multiplication `A × B → B` and addition on `B` are continuous. -/
theorem continuous_weilRestrictionAlgPointEquiv_of_continuousSMul :
    Continuous (weilRestrictionAlgPointEquiv A B C) := by
  have hcont (z : B ⊗[A] WeilRestrictionFiniteType A B C) :
      Continuous (fun p : AlgPoint A (WeilRestrictionFiniteType A B C) A ↦
        Algebra.TensorProduct.rid A B B
          (Algebra.TensorProduct.lTensor (S := B) B p.toAlgHom z)) := by
    induction z with
    | tmul b w =>
      change Continuous (fun p : AlgPoint A (WeilRestrictionFiniteType A B C) A ↦
        p w • b)
      exact (AlgPoint.continuous_eval w).smul (continuous_const (y := b))
    | add z w hz hw =>
      simp only [map_add]
      exact hz.add hw
  apply (AlgPoint.continuous_iff _).mpr
  intro c
  exact hcont (WeilRestrictionFiniteType.universalPoint A B C c)

end AlgPoints

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
  (X : Over (Spec (CommRingCat.of B))) [IsAffine X.left] [LocallyOfFiniteType X.hom]
  [TopologicalSpace A] [TopologicalSpace B] [ContinuousSMul A B] [ContinuousAdd B]

/-- The canonical base-point map of an actual affine finite-type Weil restriction, as a
continuous map for the global-section topologies, without a module-topology assumption. -/
def affineWeilRestrictionPointContinuousMap :
    C(RingPoint A (affineWeilRestriction A B X) A, RingPoint B X B) where
  toFun := (affineSchemePointHomeomorph B X B).symm ∘
    weilRestrictionAlgPointEquiv A B (AffineCoordinateRing B X) ∘
      spectrumAlgebraPointHomeomorph A A
        (WeilRestrictionFiniteType A B (AffineCoordinateRing B X))
  continuous_toFun := (affineSchemePointHomeomorph B X B).symm.continuous.comp
    ((continuous_weilRestrictionAlgPointEquiv_of_continuousSMul A B
      (AffineCoordinateRing B X)).comp (spectrumAlgebraPointHomeomorph A A _).continuous)

/-- The continuous map induces exactly the canonical tensor-unit representing map in
global-section coordinates. -/
@[simp]
theorem affineWeilRestrictionPointContinuousMap_apply
    (p : RingPoint A (affineWeilRestriction A B X) A) :
    affineSchemePointEquiv B X B (affineWeilRestrictionPointContinuousMap A B X p) =
      weilRestrictionAlgPointEquiv A B (AffineCoordinateRing B X)
        (AlgPoint.ofAlgHom (affineRingPointEquiv A
          (WeilRestrictionFiniteType A B (AffineCoordinateRing B X)) A p)) :=
  (affineSchemePointEquiv B X B).apply_symm_apply _

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.AffineWeil

open Langlands.Algebra Langlands.AlgebraicGeometry.PointTopology

section General

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
  (G : GroupScheme (Spec (CommRingCat.of B))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [TopologicalSpace A] [TopologicalSpace B] [ContinuousSMul A B] [ContinuousAdd B]

/-- The multiplicative base-point comparison is the continuous scheme-level map. -/
theorem basePointsEquiv_eq_continuousMap
    (p : (groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) A)) :
    basePointsEquiv A B G p = affineWeilRestrictionPointContinuousMap A B G.X p := by
  apply (affineSchemePointEquiv B G.X B).injective
  apply AlgPoint.ext
  intro c
  have h := congrArg AlgPoint.toAlgHom
    (affineWeilRestrictionPointContinuousMap_apply A B G.X p)
  rw [weilRestrictionAlgPointEquiv_toAlgHom] at h
  exact congrArg (fun f => f c) ((basePointsEquiv_coordinates A B G p).trans h.symm)

/-- The multiplicative base-point comparison is continuous for the existing regular-function
evaluation topologies, assuming only continuity of `A × B → B` and of addition on `B`. -/
theorem continuous_basePointsEquiv_of_continuousSMul :
    @Continuous ((groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) A))
      (G.affinePoints (CommAlgCat.of (CommRingCat.of B) B))
      ((groupScheme A B G).affinePointsTopologicalSpace (CommAlgCat.of (CommRingCat.of A) A))
      (G.affinePointsTopologicalSpace (CommAlgCat.of (CommRingCat.of B) B))
      (basePointsEquiv A B G) := by
  let : TopologicalSpace
      ((groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) A)) :=
    (groupScheme A B G).affinePointsTopologicalSpace (CommAlgCat.of (CommRingCat.of A) A)
  let : TopologicalSpace (G.affinePoints (CommAlgCat.of (CommRingCat.of B) B)) :=
    G.affinePointsTopologicalSpace (CommAlgCat.of (CommRingCat.of B) B)
  have he : (basePointsEquiv A B G :
      (groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) A) →
        G.affinePoints (CommAlgCat.of (CommRingCat.of B) B)) =
      (G.affinePointsRingPointHomeomorph (CommAlgCat.of (CommRingCat.of B) B)).symm ∘
        affineWeilRestrictionPointContinuousMap A B G.X ∘
          (groupScheme A B G).affinePointsRingPointHomeomorph
            (CommAlgCat.of (CommRingCat.of A) A) := by
    funext p
    change basePointsEquiv A B G p =
      (G.affinePointsRingPointHomeomorph (CommAlgCat.of (CommRingCat.of B) B)).symm
        (affineWeilRestrictionPointContinuousMap A B G.X
          ((groupScheme A B G).affinePointsRingPointHomeomorph
            (CommAlgCat.of (CommRingCat.of A) A) p))
    rw [affinePointsRingPointHomeomorph_apply, affinePointsRingPointHomeomorph_symm_apply]
    exact basePointsEquiv_eq_continuousMap A B G p
  rw [he]
  exact (G.affinePointsRingPointHomeomorph _).symm.continuous.comp
    ((affineWeilRestrictionPointContinuousMap A B G.X).continuous.comp
      ((groupScheme A B G).affinePointsRingPointHomeomorph _).continuous)

end General

section Rational

variable (A B : Type u) [Field A] [Field B] [Algebra A B] [FiniteDimensional A B]
  (G : GroupScheme (Spec (CommRingCat.of B))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [TopologicalSpace A] [TopologicalSpace B] [ContinuousSMul A B] [ContinuousAdd B]

/-- The comparison from rational points of the Weil restriction to rational points of the
original group, through the existing rational coefficient equivalences, is continuous for
the named rational-point topologies. -/
theorem continuous_rationalBasePoints_of_continuousSMul :
    @Continuous (rationalPoints (groupScheme A B G)) (rationalPoints G)
      (rationalPointTopology A (groupScheme A B G).X) (rationalPointTopology B G.X)
      (fun x => (GaloisPointComparison.rationalCoeffEquiv B G).symm
        (basePointsEquiv A B G
          (GaloisPointComparison.rationalCoeffEquiv A (groupScheme A B G) x))) := by
  let : TopologicalSpace (rationalPoints (groupScheme A B G)) :=
    rationalPointTopology A (groupScheme A B G).X
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology B G.X
  let : TopologicalSpace
      ((groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) A)) :=
    (groupScheme A B G).affinePointsTopologicalSpace (CommAlgCat.of (CommRingCat.of A) A)
  let : TopologicalSpace (G.affinePoints (CommAlgCat.of (CommRingCat.of B) B)) :=
    G.affinePointsTopologicalSpace (CommAlgCat.of (CommRingCat.of B) B)
  have h₁ : (GaloisPointComparison.rationalCoeffEquiv A (groupScheme A B G) :
      rationalPoints (groupScheme A B G) →
        (groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) A)) =
      rationalPointsAffineHomeomorph (groupScheme A B G) := by
    funext x
    exact GaloisPointComparison.rationalCoeffEquiv_eq A (groupScheme A B G) x
  have h₂ : ((GaloisPointComparison.rationalCoeffEquiv B G).symm :
      G.affinePoints (CommAlgCat.of (CommRingCat.of B) B) → rationalPoints G) =
      (rationalPointsAffineHomeomorph G).symm := by
    funext y
    apply (GaloisPointComparison.rationalCoeffEquiv B G).injective
    rw [MulEquiv.apply_symm_apply, GaloisPointComparison.rationalCoeffEquiv_eq]
    exact ((rationalPointsAffineHomeomorph G).apply_symm_apply y).symm
  change Continuous (((GaloisPointComparison.rationalCoeffEquiv B G).symm :
      G.affinePoints (CommAlgCat.of (CommRingCat.of B) B) → rationalPoints G) ∘
    (basePointsEquiv A B G :
      (groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) A) →
        G.affinePoints (CommAlgCat.of (CommRingCat.of B) B)) ∘
    (GaloisPointComparison.rationalCoeffEquiv A (groupScheme A B G) :
      rationalPoints (groupScheme A B G) →
        (groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) A)))
  rw [h₁, h₂]
  exact (rationalPointsAffineHomeomorph G).symm.continuous.comp
    ((continuous_basePointsEquiv_of_continuousSMul A B G).comp
      (rationalPointsAffineHomeomorph (groupScheme A B G)).continuous)

end Rational

end Langlands.GroupScheme.AffineWeil
