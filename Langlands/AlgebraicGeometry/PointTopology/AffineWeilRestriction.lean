import Langlands.AlgebraicGeometry.PointTopology.ContinuousMapTensor
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily
import Langlands.RingTheory.WeilRestriction.FiniteType

/-! # The actual affine Weil-restriction point homeomorphism -/

noncomputable section

universe u

open TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

namespace AlgPoint

variable (R D S : Type*) [CommRing R] [CommRing D] [CommRing S]
  [Algebra R D] [Algebra R S] [TopologicalSpace S] [IsTopologicalRing S]

/-- The universal family of algebra points has continuous coordinate functions. -/
def continuousEvaluationAlgHom : D →ₐ[R] C(AlgPoint R D S, S) where
  toFun d := ⟨fun q ↦ q d, continuous_eval d⟩
  map_one' := by ext q; exact q.toAlgHom.map_one
  map_mul' d e := by ext q; exact q.toAlgHom.map_mul d e
  map_zero' := by ext q; exact q.toAlgHom.map_zero
  map_add' d e := by ext q; exact q.toAlgHom.map_add d e
  commutes' r := by ext q; exact q.toAlgHom.commutes r

@[simp]
theorem continuousEvaluationAlgHom_apply (d : D) (q : AlgPoint R D S) :
    continuousEvaluationAlgHom R D S d q = q d := rfl

end AlgPoint

open Langlands.Algebra

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Module.Finite A B] [Module.Projective A B]
  [Algebra.FiniteType B C]

/-- The representing bijection at the base ring, followed by the tensor-unit
isomorphism, on independently named algebra-point carriers. -/
def weilRestrictionAlgPointEquiv :
    AlgPoint A (WeilRestrictionFiniteType A B C) A ≃ AlgPoint B C B :=
  AlgPoint.algHomEquiv.trans <|
    (WeilRestrictionFiniteType.homEquiv A B C A).trans <|
      (AlgEquiv.arrowCongr (AlgEquiv.refl : C ≃ₐ[B] C)
        (Algebra.TensorProduct.rid A B B)).trans AlgPoint.algHomEquiv.symm

theorem weilRestrictionAlgPointEquiv_toAlgHom
    (p : AlgPoint A (WeilRestrictionFiniteType A B C) A) :
    (weilRestrictionAlgPointEquiv A B C p).toAlgHom =
      (Algebra.TensorProduct.rid A B B).toAlgHom.comp
        (WeilRestrictionFiniteType.homEquiv A B C A p.toAlgHom) := by
  ext c
  rfl

variable [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace B] [IsTopologicalRing B] [IsModuleTopology A B]

omit [IsTopologicalRing A] in
theorem continuous_weilRestrictionAlgPointEquiv :
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

/-- Classify the universal continuous family through the continuous-function
tensor comparison. -/
def weilRestrictionContinuousPoint :
    WeilRestrictionFiniteType A B C →ₐ[A] C(AlgPoint B C B, A) :=
  (WeilRestrictionFiniteType.homEquiv A B C _).symm
    ((continuousMapTensorAlgEquiv A B (AlgPoint B C B)).symm.toAlgHom.comp
      (AlgPoint.continuousEvaluationAlgHom B C B))

theorem weilRestrictionContinuousPoint_evaluate (q : AlgPoint B C B) :
    weilRestrictionAlgPointEquiv A B C
        (AlgPoint.ofAlgHom ((ContinuousMap.evalAlgHom A A q).comp
          (weilRestrictionContinuousPoint A B C))) = q := by
  apply AlgPoint.ext
  intro c
  change (Algebra.TensorProduct.rid A B B)
      (WeilRestrictionFiniteType.homEquiv A B C A
        ((ContinuousMap.evalAlgHom A A q).comp
          (weilRestrictionContinuousPoint A B C)) c) = q.toAlgHom c
  rw [WeilRestrictionFiniteType.homEquiv_comp]
  simp only [weilRestrictionContinuousPoint, Equiv.apply_symm_apply, AlgHom.comp_apply]
  calc
    _ = (continuousMapTensorAlgEquiv A B (AlgPoint B C B))
          ((continuousMapTensorAlgEquiv A B (AlgPoint B C B)).symm
            (AlgPoint.continuousEvaluationAlgHom B C B c)) q :=
      (congrArg (fun f : B ⊗[A] C(AlgPoint B C B, A) →ₐ[B] B ↦
        f ((continuousMapTensorAlgEquiv A B (AlgPoint B C B)).symm
          (AlgPoint.continuousEvaluationAlgHom B C B c)))
        (eval_comp_continuousMapTensorAlgEquiv A B (AlgPoint B C B) q)).symm
    _ = q.toAlgHom c := by simp

theorem continuous_weilRestrictionAlgPointEquiv_symm :
    Continuous (weilRestrictionAlgPointEquiv A B C).symm := by
  apply (AlgPoint.continuous_iff _).mpr
  intro w
  have heq (q : AlgPoint B C B) :
      (weilRestrictionAlgPointEquiv A B C).symm q =
        AlgPoint.ofAlgHom ((ContinuousMap.evalAlgHom A A q).comp
          (weilRestrictionContinuousPoint A B C)) := by
    apply (weilRestrictionAlgPointEquiv A B C).injective
    rw [Equiv.apply_symm_apply, weilRestrictionContinuousPoint_evaluate]
  simpa only [heq, AlgPoint.ofAlgHom_apply, AlgHom.comp_apply,
    ContinuousMap.evalAlgHom_apply] using
      (weilRestrictionContinuousPoint A B C w).continuous

/-- The canonical finite-type affine Weil-restriction bijection is a
homeomorphism for the two independent evaluation topologies. -/
def weilRestrictionAlgPointHomeomorph :
    AlgPoint A (WeilRestrictionFiniteType A B C) A ≃ₜ AlgPoint B C B where
  toEquiv := weilRestrictionAlgPointEquiv A B C
  continuous_toFun := continuous_weilRestrictionAlgPointEquiv A B C
  continuous_invFun := continuous_weilRestrictionAlgPointEquiv_symm A B C

end Langlands.AlgebraicGeometry.PointTopology

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

open Langlands.Algebra

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]

section Spectra

variable (C : Type u) [CommRing C] [Algebra B C] [Algebra.FiniteType B C]
  [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace B] [IsTopologicalRing B] [IsModuleTopology A B]

/-- The canonical comparison on actual relative morphisms of spectra. -/
def weilRestrictionSpecPointHomeomorph :
    SpecPoint A (WeilRestrictionFiniteType A B C) A ≃ₜ SpecPoint B C B :=
  ((specPointHomeomorph A (WeilRestrictionFiniteType A B C) A).trans
    (weilRestrictionAlgPointHomeomorph A B C)).trans
      (specPointHomeomorph B C B).symm

/-- The spectrum-point comparison is exactly the representing algebra map. -/
@[simp]
theorem weilRestrictionSpecPointHomeomorph_apply
    (p : SpecPoint A (WeilRestrictionFiniteType A B C) A) :
    specPointEquiv B C B (weilRestrictionSpecPointHomeomorph A B C p) =
      weilRestrictionAlgPointEquiv A B C
        (specPointEquiv A (WeilRestrictionFiniteType A B C) A p) :=
  (specPointEquiv B C B).apply_symm_apply _

/-- The same comparison in the existing actual `Over (Spec _)` point carriers,
with their independently defined global-section topologies. -/
def weilRestrictionRingPointHomeomorph :
    RingPoint A (ringTest A (WeilRestrictionFiniteType A B C)) A ≃ₜ
      RingPoint B (ringTest B C) B :=
  ((spectrumAlgebraPointHomeomorph A A (WeilRestrictionFiniteType A B C)).trans
    (weilRestrictionAlgPointHomeomorph A B C)).trans
      (spectrumAlgebraPointHomeomorph B B C).symm

end Spectra

variable (X : Over (Spec (CommRingCat.of B))) [IsAffine X.left]
  [LocallyOfFiniteType X.hom]

/-- The actual affine finite-type Weil-restriction scheme, formed from the
global-section coordinate algebra of the original affine scheme. -/
def affineWeilRestriction : Over (Spec (CommRingCat.of A)) :=
  ringTest A (WeilRestrictionFiniteType A B (AffineCoordinateRing B X))

instance affineWeilRestriction_isAffine :
    IsAffine (affineWeilRestriction A B X).left :=
  inferInstanceAs (IsAffine
    (ringTest A (WeilRestrictionFiniteType A B (AffineCoordinateRing B X))).left)

instance affineWeilRestriction_locallyOfFiniteType :
    LocallyOfFiniteType (affineWeilRestriction A B X).hom :=
  inferInstanceAs (LocallyOfFiniteType
    (ringTest A (WeilRestrictionFiniteType A B (AffineCoordinateRing B X))).hom)

theorem affineWeilRestriction_quasiCompact :
    QuasiCompact (affineWeilRestriction A B X).hom :=
  inferInstance

/-- Its representing equivalence on all actual affine test schemes.
The target is the actual tensor-product ring, with no topology assumed. -/
def affineWeilRestrictionPointEquiv (T : Type u) [CommRing T] [Algebra A T] :
    RingPoint A (affineWeilRestriction A B X) T ≃
      RingPoint B X (B ⊗[A] T) :=
  ((affineRingPointEquiv A
      (WeilRestrictionFiniteType A B (AffineCoordinateRing B X)) T).trans
    (WeilRestrictionFiniteType.homEquiv A B (AffineCoordinateRing B X) T)).trans
      (AlgPoint.algHomEquiv.symm.trans
        (affineSchemePointEquiv B X (B ⊗[A] T)).symm)

variable [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace B] [IsTopologicalRing B] [IsModuleTopology A B]

/-- The canonical base-point bijection for an arbitrary actual affine
finite-type scheme is a homeomorphism for the global-section topologies. -/
def affineWeilRestrictionPointHomeomorph :
    RingPoint A (affineWeilRestriction A B X) A ≃ₜ RingPoint B X B :=
  ((spectrumAlgebraPointHomeomorph A A
      (WeilRestrictionFiniteType A B (AffineCoordinateRing B X))).trans
    (weilRestrictionAlgPointHomeomorph A B (AffineCoordinateRing B X))).trans
      (affineSchemePointHomeomorph B X B).symm

/-- The constructed scheme homeomorphism induces exactly the canonical
tensor-unit representing map in global-section coordinates. -/
@[simp]
theorem affineWeilRestrictionPointHomeomorph_apply
    (p : RingPoint A (affineWeilRestriction A B X) A) :
    affineSchemePointEquiv B X B (affineWeilRestrictionPointHomeomorph A B X p) =
      weilRestrictionAlgPointEquiv A B (AffineCoordinateRing B X)
        (AlgPoint.ofAlgHom (affineRingPointEquiv A
          (WeilRestrictionFiniteType A B (AffineCoordinateRing B X)) A p)) :=
  (affineSchemePointEquiv B X B).apply_symm_apply _

end Langlands.AlgebraicGeometry.PointTopology
