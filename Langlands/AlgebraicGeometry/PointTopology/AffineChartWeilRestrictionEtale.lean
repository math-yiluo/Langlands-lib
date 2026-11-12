import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionFiniteType
import Langlands.TauCeti.RingTheory.WeilRestriction.Smooth
import Langlands.TauCeti.Algebra.TensorProduct.Ideal
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Étaleness of actual affine-chart Weil restrictions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.Algebra

open TauCeti.Algebra
open scoped TensorProduct

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Module.Finite A B] [Module.Projective A B]

/-- Weil restriction of a finitely presented formally unramified algebra along a finite
projective algebra is formally unramified. -/
theorem weilRestriction_formallyUnramified [Algebra.FinitePresentation B C]
    [Algebra.FormallyUnramified B C] :
    Algebra.FormallyUnramified A (WeilRestriction A B C) := by
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro T _ _ I hI g₁ g₂ h
  let q := Algebra.TensorProduct.lTensor (S := B) B (Ideal.Quotient.mkₐ A I)
  have hqker : RingHom.ker q = Ideal.rightTensorIdeal A B I :=
    Ideal.ker_tensorProduct_map_id_quotient (R := A) (A := B) I
  have hker : IsNilpotent (RingHom.ker (q : B ⊗[A] T →+* B ⊗[A] (T ⧸ I))) := by
    refine ⟨2, ?_⟩
    change RingHom.ker q ^ 2 = ⊥
    rw [hqker, Ideal.rightTensorIdeal_def, ← Ideal.map_pow, hI, Ideal.map_bot]
  apply (WeilRestriction.homEquiv A B C T).injective
  refine Algebra.FormallyUnramified.lift_unique' q hker _ _ ?_
  rw [← WeilRestriction.homEquiv_comp, ← WeilRestriction.homEquiv_comp, h]

/-- Weil restriction along a finite projective algebra preserves étale algebras. -/
theorem weilRestriction_etale [Algebra.Etale B C] :
    Algebra.Etale A (WeilRestriction A B C) := by
  have := weilRestriction_formallyUnramified A B C
  rw [Algebra.Etale.iff_formallyUnramified_and_smooth]
  exact ⟨inferInstance, inferInstance⟩

/-- The finite-type affine Weil algebra of an étale algebra is étale. -/
theorem weilRestrictionFiniteType_etale [Algebra.Etale B C] :
    Algebra.Etale A (WeilRestrictionFiniteType A B C) := by
  have := weilRestriction_etale A B C
  exact Algebra.Etale.of_equiv (WeilRestrictionFiniteType.finitePresentationAlgEquiv A B C).symm

end Langlands.Algebra

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

/-- The coordinate algebra of an affine étale scheme is étale. -/
theorem affineCoordinate_etale (R : Type u) [CommRing R]
    (U : Over (Spec (CommRingCat.of R))) [IsAffine U.left] [Etale U.hom] :
    Algebra.Etale R (AffineCoordinateRing R U) := by
  rw [← RingHom.etale_algebraMap]
  apply (HasRingHomProperty.Spec_iff (P := @Etale) (Q := @RingHom.Etale)
    (φ := CommRingCat.ofHom (algebraMap R (AffineCoordinateRing R U)))).mp
  change Etale (Spec.algebraMap R (AffineCoordinateRing R U))
  rw [affineCoordinateSpecMap]
  infer_instance

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]

/-- The affine Weil restriction of an affine étale scheme is étale. -/
instance affineWeilRestriction_etale (X : Over (Spec (CommRingCat.of B))) [IsAffine X.left]
    [LocallyOfFiniteType X.hom] [Etale X.hom] :
    Etale (affineWeilRestriction A B X).hom := by
  have := affineCoordinate_etale B X
  have := Langlands.Algebra.weilRestrictionFiniteType_etale A B (AffineCoordinateRing B X)
  change Etale (Spec.algebraMap A
    (Langlands.Algebra.WeilRestrictionFiniteType A B (AffineCoordinateRing B X)))
  apply (HasRingHomProperty.Spec_iff (P := @Etale) (Q := @RingHom.Etale)).mpr
  exact RingHom.etale_algebraMap.mpr inferInstance

instance openOver_etale (Y : Over (Spec (CommRingCat.of B))) [Etale Y.hom] (U : Y.left.Opens) :
    Etale (openOver B Y U).hom :=
  inferInstanceAs (Etale (U.ι ≫ Y.hom))

/-- The glued affine-chart Weil restriction of an étale scheme is étale. -/
instance affineChartWeilRestriction_etale (Y : Over (Spec (CommRingCat.of B)))
    [LocallyOfFiniteType Y.hom] [Etale Y.hom] :
    Etale (affineChartWeilRestriction A B Y).hom := by
  apply IsZariskiLocalAtSource.of_openCover (P := @Etale)
    (affineChartWeilRestrictionOpenCover A B Y)
  intro U
  change Etale
    ((affineChartWeilRestrictionι A B Y U).left ≫ (affineChartWeilRestriction A B Y).hom)
  rw [Over.w]
  infer_instance

end Langlands.AlgebraicGeometry.PointTopology
