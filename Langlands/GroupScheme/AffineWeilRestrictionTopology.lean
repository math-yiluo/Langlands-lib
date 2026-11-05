import Langlands.GroupScheme.AffineWeilRestriction
import Langlands.GroupScheme.AffinePointRingPointComparison
import Mathlib.Topology.Algebra.ContinuousMonoidHom

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj CategoryTheory.Obj TensorProduct

namespace Langlands.GroupScheme.AffineWeil

open Langlands.Algebra Langlands.AlgebraicGeometry.PointTopology

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  (G : GroupScheme (Spec (CommRingCat.of B)))

/-- The tensor-unit coefficient isomorphism acts on the original actual point groups. -/
def tensorUnitPointsEquiv :
    G.affinePoints (CommAlgCat.of (CommRingCat.of B) (B ⊗[A] A)) ≃*
      G.affinePoints (CommAlgCat.of (CommRingCat.of B) B) :=
  (G.affinePointFunctor.mapIso
    (CommAlgCat.isoMk (Algebra.TensorProduct.rid A B B))).groupIsoToMulEquiv

/-- The tensor-unit comparison is the original coefficient-change homomorphism. -/
theorem tensorUnitPointsEquiv_apply
    (p : G.affinePoints (CommAlgCat.of (CommRingCat.of B) (B ⊗[A] A))) :
    tensorUnitPointsEquiv A B G p =
      G.affinePointMap (CommAlgCat.ofHom (Algebra.TensorProduct.rid A B B).toAlgHom) p := rfl

variable [Module.Finite A B] [Module.Projective A B]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The canonical multiplicative comparison at the base ring, followed by tensor-unit. -/
def basePointsEquiv :
    (groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) A) ≃*
      G.affinePoints (CommAlgCat.of (CommRingCat.of B) B) :=
  (pointsEquiv A B G A).trans (tensorUnitPointsEquiv A B G)

/-- The exact tensor-unit formula in the original global-section coordinates. -/
theorem basePointsEquiv_coordinates
    (p : (groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) A)) :
    (affineSchemePointEquiv B G.X B (basePointsEquiv A B G p)).toAlgHom =
      (Algebra.TensorProduct.rid A B B).toAlgHom.comp
        (WeilRestrictionFiniteType.homEquiv A B (AffineCoordinateRing B G.X) A
          (affineRingPointEquiv A
            (WeilRestrictionFiniteType A B (AffineCoordinateRing B G.X)) A p)) := by
  change (affineSchemePointEquiv B G.X B
    (ringTestMap B (Algebra.TensorProduct.rid A B B).toAlgHom ≫
      pointsEquiv A B G A p)).toAlgHom = _
  exact (coordinatePoint_changeRing B G.X
    (Algebra.TensorProduct.rid A B B).toAlgHom (pointsEquiv A B G A p)).trans
      (congrArg ((Algebra.TensorProduct.rid A B B).toAlgHom.comp)
        (pointsEquiv_coordinates A B G A p))

variable [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace B] [IsTopologicalRing B] [IsModuleTopology A B]

local instance restrictedPointTopology :
    TopologicalSpace
      ((groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) A)) :=
  (groupScheme A B G).affinePointsTopologicalSpace (CommAlgCat.of (CommRingCat.of A) A)

local instance originalPointTopology :
    TopologicalSpace (G.affinePoints (CommAlgCat.of (CommRingCat.of B) B)) :=
  G.affinePointsTopologicalSpace (CommAlgCat.of (CommRingCat.of B) B)

/-- The multiplicative map is precisely the published affine-scheme homeomorphism. -/
theorem basePointsEquiv_eq
    (p : (groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) A)) :
    basePointsEquiv A B G p = affineWeilRestrictionPointHomeomorph A B G.X p := by
  apply (affineSchemePointEquiv B G.X B).injective
  apply AlgPoint.ext
  intro c
  have h := congrArg AlgPoint.toAlgHom
    (affineWeilRestrictionPointHomeomorph_apply A B G.X p)
  rw [weilRestrictionAlgPointEquiv_toAlgHom] at h
  exact congrArg (fun f => f c) ((basePointsEquiv_coordinates A B G p).trans h.symm)

/-- The existing homeomorphism, expressed on actual group-point carriers with their
existing regular-function evaluation topologies. -/
def basePointsHomeomorph :
    (groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) A) ≃ₜ
      G.affinePoints (CommAlgCat.of (CommRingCat.of B) B) :=
  (((groupScheme A B G).affinePointsRingPointHomeomorph
      (CommAlgCat.of (CommRingCat.of A) A)).trans
    (affineWeilRestrictionPointHomeomorph A B G.X)).trans
      (G.affinePointsRingPointHomeomorph (CommAlgCat.of (CommRingCat.of B) B)).symm

/-- The carrier identifications in the homeomorphism are the identity on actual points. -/
theorem basePointsHomeomorph_apply
    (p : (groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) A)) :
    basePointsHomeomorph A B G p = affineWeilRestrictionPointHomeomorph A B G.X p := by
  change (G.affinePointsRingPointHomeomorph (CommAlgCat.of (CommRingCat.of B) B)).symm
    (affineWeilRestrictionPointHomeomorph A B G.X
      ((groupScheme A B G).affinePointsRingPointHomeomorph
        (CommAlgCat.of (CommRingCat.of A) A) p)) = _
  rw [affinePointsRingPointHomeomorph_apply, affinePointsRingPointHomeomorph_symm_apply]

/-- The canonical group equivalence is a homeomorphism for the original point topologies. -/
theorem isHomeomorph_basePointsEquiv : IsHomeomorph (basePointsEquiv A B G) := by
  have he : (basePointsEquiv A B G :
      (groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) A) →
        G.affinePoints (CommAlgCat.of (CommRingCat.of B) B)) =
      basePointsHomeomorph A B G := by
    funext p
    exact (basePointsEquiv_eq A B G p).trans (basePointsHomeomorph_apply A B G p).symm
  rw [he]
  exact (basePointsHomeomorph A B G).isHomeomorph

/-- Continuous group equivalence on actual base points, retaining both evaluation topologies. -/
def basePointsContinuousEquiv :
    (groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) A) ≃ₜ*
      G.affinePoints (CommAlgCat.of (CommRingCat.of B) B) where
  toMulEquiv := basePointsEquiv A B G
  continuous_toFun := (isHomeomorph_basePointsEquiv A B G).continuous
  continuous_invFun := ((basePointsEquiv A B G).toEquiv.isHomeomorph_iff.mp
    (isHomeomorph_basePointsEquiv A B G)).2

/-- The continuous group comparison has exactly the existing scheme-level map. -/
@[simp] theorem basePointsContinuousEquiv_apply
    (p : (groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) A)) :
    basePointsContinuousEquiv A B G p = affineWeilRestrictionPointHomeomorph A B G.X p :=
  basePointsEquiv_eq A B G p

end Langlands.GroupScheme.AffineWeil
