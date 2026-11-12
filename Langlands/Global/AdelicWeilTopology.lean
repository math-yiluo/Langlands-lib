import Langlands.Global.AdelicWeilNormOneComparison
import Langlands.Global.NumberFieldAdeleContinuousTensor

/-! # The canonical adelic Weil point homeomorphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.Global.AdelicWeilRestriction

open Langlands.Algebra Langlands.AlgebraicGeometry.PointTopology

variable (F L : Type u) [Field F] [NumberField F] [Field L] [NumberField L]
  [Algebra F L]
  (C : Type u) [CommRing C] [Algebra L C] [Algebra.FiniteType L C]

/-- The representing bijection followed by the canonical full adelic tensor map. -/
def algPointEquiv :
    AlgPoint F (WeilRestrictionFiniteType F L C) (Adeles F) ≃
      AlgPoint L C (Adeles L) :=
  AlgPoint.algHomEquiv.trans <|
    (WeilRestrictionFiniteType.homEquiv F L C (Adeles F)).trans <|
      (AlgEquiv.arrowCongr (AlgEquiv.refl : C ≃ₐ[L] C)
        (numberFieldAdeleTensorEquiv F L)).trans AlgPoint.algHomEquiv.symm

theorem algPointEquiv_toAlgHom
    (p : AlgPoint F (WeilRestrictionFiniteType F L C) (Adeles F)) :
    (algPointEquiv F L C p).toAlgHom =
      (numberFieldAdeleTensorEquiv F L).toAlgHom.comp
        (WeilRestrictionFiniteType.homEquiv F L C (Adeles F) p.toAlgHom) := by
  ext c
  rfl

theorem continuous_algPointEquiv :
    Continuous (algPointEquiv F L C) := by
  have hcont (z : L ⊗[F] WeilRestrictionFiniteType F L C) :
      Continuous (fun p : AlgPoint F (WeilRestrictionFiniteType F L C) (Adeles F) =>
        numberFieldAdeleTensorEquiv F L
          (Algebra.TensorProduct.lTensor (S := L) L p.toAlgHom z)) := by
    induction z with
    | tmul a w =>
      change Continuous (fun p : AlgPoint F (WeilRestrictionFiniteType F L C) (Adeles F) =>
        algebraMap L (Adeles L) a * AdelicFunctoriality.adeleInclusion (p w))
      exact continuous_const.mul
        (AdelicFunctoriality.continuous_adeleInclusion.comp (AlgPoint.continuous_eval w))
    | add z w hz hw =>
      simp only [map_add]
      exact hz.add hw
  apply (AlgPoint.continuous_iff _).mpr
  intro c
  exact hcont (WeilRestrictionFiniteType.universalPoint F L C c)

/-- Classify the universal continuous family through full adelic scalar extension. -/
def continuousPoint :
    WeilRestrictionFiniteType F L C →ₐ[F] C(AlgPoint L C (Adeles L), Adeles F) :=
  (WeilRestrictionFiniteType.homEquiv F L C _).symm
    ((adeleContinuousMapTensorAlgEquiv F L (AlgPoint L C (Adeles L))).symm.toAlgHom.comp
      (AlgPoint.continuousEvaluationAlgHom L C (Adeles L)))

theorem continuousPoint_evaluate (q : AlgPoint L C (Adeles L)) :
    algPointEquiv F L C
        (AlgPoint.ofAlgHom ((ContinuousMap.evalAlgHom F (Adeles F) q).comp
          (continuousPoint F L C))) = q := by
  apply AlgPoint.ext
  intro c
  change (numberFieldAdeleTensorEquiv F L)
      (WeilRestrictionFiniteType.homEquiv F L C (Adeles F)
        ((ContinuousMap.evalAlgHom F (Adeles F) q).comp
          (continuousPoint F L C)) c) = q.toAlgHom c
  rw [WeilRestrictionFiniteType.homEquiv_comp]
  simp only [continuousPoint, Equiv.apply_symm_apply, AlgHom.comp_apply]
  calc
    _ = adeleContinuousMapTensorAlgHom F L (AlgPoint L C (Adeles L))
          ((adeleContinuousMapTensorAlgEquiv F L (AlgPoint L C (Adeles L))).symm
            (AlgPoint.continuousEvaluationAlgHom L C (Adeles L) c)) q :=
      (congrArg (fun f : L ⊗[F] C(AlgPoint L C (Adeles L), Adeles F) →ₐ[L] Adeles L =>
        f ((adeleContinuousMapTensorAlgEquiv F L (AlgPoint L C (Adeles L))).symm
          (AlgPoint.continuousEvaluationAlgHom L C (Adeles L) c)))
        (eval_comp_adeleContinuousMapTensorAlgHom F L (AlgPoint L C (Adeles L)) q)).symm
    _ = q.toAlgHom c := by
      change (adeleContinuousMapTensorAlgEquiv F L (AlgPoint L C (Adeles L))
        ((adeleContinuousMapTensorAlgEquiv F L (AlgPoint L C (Adeles L))).symm
          (AlgPoint.continuousEvaluationAlgHom L C (Adeles L) c))) q = _
      simp

theorem continuous_algPointEquiv_symm :
    Continuous (algPointEquiv F L C).symm := by
  apply (AlgPoint.continuous_iff _).mpr
  intro w
  have heq (q : AlgPoint L C (Adeles L)) :
      (algPointEquiv F L C).symm q =
        AlgPoint.ofAlgHom ((ContinuousMap.evalAlgHom F (Adeles F) q).comp
          (continuousPoint F L C)) := by
    apply (algPointEquiv F L C).injective
    rw [Equiv.apply_symm_apply, continuousPoint_evaluate]
  simpa only [heq, AlgPoint.ofAlgHom_apply, AlgHom.comp_apply,
    ContinuousMap.evalAlgHom_apply] using (continuousPoint F L C w).continuous

/-- The adelic representing bijection preserves the original evaluation topologies. -/
def algPointHomeomorph :
    AlgPoint F (WeilRestrictionFiniteType F L C) (Adeles F) ≃ₜ
      AlgPoint L C (Adeles L) where
  toEquiv := algPointEquiv F L C
  continuous_toFun := continuous_algPointEquiv F L C
  continuous_invFun := continuous_algPointEquiv_symm F L C

variable (X : Over (Spec (CommRingCat.of L))) [IsAffine X.left]
  [LocallyOfFiniteType X.hom]

/-- The adelic comparison on actual affine-scheme points with their existing
global-section evaluation topologies. -/
def schemePointHomeomorph :
    RingPoint F (affineWeilRestriction F L X) (Adeles F) ≃ₜ
      RingPoint L X (Adeles L) :=
  ((spectrumAlgebraPointHomeomorph F (Adeles F)
      (WeilRestrictionFiniteType F L (AffineCoordinateRing L X))).trans
    (algPointHomeomorph F L (AffineCoordinateRing L X))).trans
      (affineSchemePointHomeomorph L X (Adeles L)).symm

/-- The scheme comparison has exactly the canonical tensor-map formula in coordinates. -/
theorem schemePointHomeomorph_coordinates
    (p : RingPoint F (affineWeilRestriction F L X) (Adeles F)) :
    (affineSchemePointEquiv L X (Adeles L)
      (schemePointHomeomorph F L X p)).toAlgHom =
      (numberFieldAdeleTensorEquiv F L).toAlgHom.comp
        (WeilRestrictionFiniteType.homEquiv F L (AffineCoordinateRing L X) (Adeles F)
          (affineRingPointEquiv F
            (WeilRestrictionFiniteType F L (AffineCoordinateRing L X)) (Adeles F) p)) := by
  have h := (affineSchemePointEquiv L X (Adeles L)).apply_symm_apply
    (algPointEquiv F L (AffineCoordinateRing L X)
      (spectrumAlgebraPointHomeomorph F (Adeles F)
        (WeilRestrictionFiniteType F L (AffineCoordinateRing L X)) p))
  exact (congrArg AlgPoint.toAlgHom h).trans
    (algPointEquiv_toAlgHom F L (AffineCoordinateRing L X) _)

open Langlands.GroupScheme

variable (G : GroupScheme (Spec (CommRingCat.of L)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The fixed canonical multiplicative equivalence has the expected global-section
coordinate formula. -/
theorem adelicPointsEquiv_coordinates
    (p : AdelicGroupPoints F (AffineWeil.groupScheme F L G)) :
    (affineSchemePointEquiv L G.X (Adeles L)
      (adelicPointsEquiv F L G p)).toAlgHom =
      (numberFieldAdeleTensorEquiv F L).toAlgHom.comp
        (WeilRestrictionFiniteType.homEquiv F L (AffineCoordinateRing L G.X) (Adeles F)
          (affineRingPointEquiv F
            (WeilRestrictionFiniteType F L (AffineCoordinateRing L G.X)) (Adeles F) p)) := by
  change (affineSchemePointEquiv L G.X (Adeles L)
    (ringTestMap L (numberFieldAdeleTensorEquiv F L).toAlgHom ≫
      AffineWeil.pointsEquiv F L G (Adeles F) p)).toAlgHom = _
  exact (AffineWeil.coordinatePoint_changeRing L G.X
    (numberFieldAdeleTensorEquiv F L).toAlgHom
      (AffineWeil.pointsEquiv F L G (Adeles F) p)).trans
    (congrArg ((numberFieldAdeleTensorEquiv F L).toAlgHom.comp)
      (AffineWeil.pointsEquiv_coordinates F L G (Adeles F) p))

/-- The fixed group comparison agrees with the constructed scheme homeomorphism. -/
theorem adelicPointsEquiv_eq
    (p : AdelicGroupPoints F (AffineWeil.groupScheme F L G)) :
    adelicPointsEquiv F L G p = schemePointHomeomorph F L G.X p := by
  apply (affineSchemePointEquiv L G.X (Adeles L)).injective
  apply AlgPoint.ext
  intro c
  exact congrArg (fun f => f c) ((adelicPointsEquiv_coordinates F L G p).trans
    (schemePointHomeomorph_coordinates F L G.X p).symm)

/-- The same homeomorphism on the original actual adelic group-point carriers. -/
def adelicPointsHomeomorph :
    AdelicGroupPoints F (AffineWeil.groupScheme F L G) ≃ₜ AdelicGroupPoints L G :=
  (((AffineWeil.groupScheme F L G).affinePointsRingPointHomeomorph
      (CommAlgCat.of (CommRingCat.of F) (Adeles F))).trans
    (schemePointHomeomorph F L G.X)).trans
      (G.affinePointsRingPointHomeomorph
        (CommAlgCat.of (CommRingCat.of L) (Adeles L))).symm

set_option maxRecDepth 2048 in
/-- The carrier identifications are literally the identity on the actual points. -/
theorem adelicPointsHomeomorph_apply
    (p : AdelicGroupPoints F (AffineWeil.groupScheme F L G)) :
    adelicPointsHomeomorph F L G p = schemePointHomeomorph F L G.X p := by
  change (G.affinePointsRingPointHomeomorph
    (CommAlgCat.of (CommRingCat.of L) (Adeles L))).symm
      (schemePointHomeomorph F L G.X
        ((AffineWeil.groupScheme F L G).affinePointsRingPointHomeomorph
          (CommAlgCat.of (CommRingCat.of F) (Adeles F)) p)) = _
  rw [affinePointsRingPointHomeomorph_apply, affinePointsRingPointHomeomorph_symm_apply]

/-- The canonical actual adelic Weil comparison is a homeomorphism. -/
theorem isHomeomorph_adelicPointsEquiv :
    IsHomeomorph (adelicPointsEquiv F L G) := by
  have he : (adelicPointsEquiv F L G :
      AdelicGroupPoints F (AffineWeil.groupScheme F L G) → AdelicGroupPoints L G) =
      adelicPointsHomeomorph F L G := by
    funext p
    exact (adelicPointsEquiv_eq F L G p).trans
      (adelicPointsHomeomorph_apply F L G p).symm
  rw [he]
  exact (adelicPointsHomeomorph F L G).isHomeomorph

/-- A continuous multiplicative equivalence with precisely the original canonical map. -/
def adelicPointsContinuousEquiv :
    AdelicGroupPoints F (AffineWeil.groupScheme F L G) ≃ₜ* AdelicGroupPoints L G where
  toMulEquiv := adelicPointsEquiv F L G
  continuous_toFun := (isHomeomorph_adelicPointsEquiv F L G).continuous
  continuous_invFun := ((adelicPointsEquiv F L G).toEquiv.isHomeomorph_iff.mp
    (isHomeomorph_adelicPointsEquiv F L G)).2

end Langlands.Global.AdelicWeilRestriction
