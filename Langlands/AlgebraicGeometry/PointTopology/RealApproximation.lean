import Langlands.AlgebraicGeometry.PointTopology.AffineGroupProofs
import Langlands.AlgebraicGeometry.PointTopology.AffineProductRingTopologyProof
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Elementary transport of real approximation for affine schemes -/

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Density of actual rational points in actual real points, with the evaluation topology. -/
def HasRealApproximation (X : Over (Spec (CommRingCat.of ℚ))) [IsAffine X.left] : Prop :=
  DenseRange (fun p : RingPoint ℚ X ℚ => p.changeRing (Algebra.ofId ℚ ℝ))

variable {X Y : Over (Spec (CommRingCat.of ℚ))} [IsAffine X.left] [IsAffine Y.left]

/-- Density descends through a morphism which is surjective on actual real points. -/
theorem HasRealApproximation.map (hX : HasRealApproximation X) (f : X ⟶ Y)
    (hf : Function.Surjective
      (fun p : RingPoint ℚ X ℝ => (p ≫ f : RingPoint ℚ Y ℝ))) :
    HasRealApproximation Y := by
  have hd := (hf.denseRange (X := RingPoint ℚ Y ℝ)).comp
    (Y := RingPoint ℚ X ℝ) (Z := RingPoint ℚ Y ℝ)
    hX (continuous_affineSchemePointMap ℚ ℝ f)
  refine Dense.mono ?_ hd
  rintro _ ⟨p, rfl⟩
  exact ⟨p ≫ f, (Category.assoc _ _ _).symm⟩

/-- A scheme isomorphism transports real approximation. -/
theorem HasRealApproximation.of_iso (hX : HasRealApproximation X) (e : X ≅ Y) :
    HasRealApproximation Y := by
  apply hX.map e.hom
  intro p
  refine ⟨p ≫ e.inv, ?_⟩
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Real approximation is preserved by products over the rationals. -/
theorem HasRealApproximation.tensor
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (hX : HasRealApproximation X) (hY : HasRealApproximation Y) :
    letI : IsAffine (X ⊗ Y).left := tensor_isAffine ℚ X Y
    HasRealApproximation (X ⊗ Y) := by
  let : IsAffine (X ⊗ Y).left := tensor_isAffine ℚ X Y
  have hsurj : Function.Surjective
      (fun q : RingPoint ℚ X ℝ × RingPoint ℚ Y ℝ =>
        (lift q.1 q.2 : RingPoint ℚ (X ⊗ Y) ℝ)) := by
    intro p
    refine ⟨(p ≫ fst X Y, p ≫ snd X Y), ?_⟩
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have hd := (hsurj.denseRange (X := RingPoint ℚ (X ⊗ Y) ℝ)).comp
    (Y := RingPoint ℚ X ℝ × RingPoint ℚ Y ℝ) (Z := RingPoint ℚ (X ⊗ Y) ℝ)
    (hX.prodMap hY)
    (continuous_affineSchemePointPair ℚ ℝ X Y)
  refine Dense.mono ?_ hd
  rintro _ ⟨q, rfl⟩
  refine ⟨lift q.1 q.2, ?_⟩
  exact comp_lift _ _ _

/-- The direct spectrum comparison respects the inclusion of coefficient fields. -/
theorem spectrumAlgebraPointEquiv_changeRing_real
    (A : Type) [CommRing A] [Algebra ℚ A]
    (p : RingPoint ℚ (ringTest ℚ A) ℚ) :
    spectrumAlgebraPointEquiv ℚ ℝ A (p.changeRing (Algebra.ofId ℚ ℝ)) =
      AlgPoint.mapCoefficients (Algebra.ofId ℚ ℝ)
        (spectrumAlgebraPointEquiv ℚ ℚ A p) := by
  apply AlgHom.coe_ringHom_injective
  let p₀ : Spec (CommRingCat.of ℚ) ⟶ Spec (CommRingCat.of A) := p.left
  change (Spec.preimage (Spec.map (CommRingCat.ofHom
      (Algebra.ofId ℚ ℝ).toRingHom) ≫ p₀)).hom =
    (Algebra.ofId ℚ ℝ).toRingHom.comp (Spec.preimage p₀).hom
  rw [Spec.preimage_comp, Spec.preimage_map, CommRingCat.hom_comp]
  rfl

/-- Polynomial spectra have real approximation, for any index type in `Type`. -/
theorem hasRealApproximation_polynomialSpectrum (ι : Type) :
    HasRealApproximation (ringTest ℚ (MvPolynomial ι ℚ)) := by
  let eQ := (spectrumAlgebraPointHomeomorph ℚ ℚ (MvPolynomial ι ℚ)).trans
    (AlgPoint.polynomialPointHomeomorph (R := ℚ) (S := ℚ) ι)
  let eR := (spectrumAlgebraPointHomeomorph ℚ ℝ (MvPolynomial ι ℚ)).trans
    (AlgPoint.polynomialPointHomeomorph (R := ℚ) (S := ℝ) ι)
  have hcoord : DenseRange (fun v : ι → ℚ => fun i => (v i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hd := eR.symm.surjective.denseRange.comp hcoord eR.symm.continuous
  have hnat (p : RingPoint ℚ (ringTest ℚ (MvPolynomial ι ℚ)) ℚ) :
      eR (p.changeRing (Algebra.ofId ℚ ℝ)) = fun i => (eQ p i : ℝ) := by
    funext i
    change spectrumAlgebraPointEquiv ℚ ℝ (MvPolynomial ι ℚ)
      (p.changeRing (Algebra.ofId ℚ ℝ)) (MvPolynomial.X i) = _
    rw [spectrumAlgebraPointEquiv_changeRing_real]
    rfl
  apply DenseRange.of_comp (g := eQ.symm)
  have he :
      (fun p : RingPoint ℚ (ringTest ℚ (MvPolynomial ι ℚ)) ℚ =>
        p.changeRing (Algebra.ofId ℚ ℝ)) ∘ eQ.symm =
          eR.symm ∘ (fun v : ι → ℚ => fun i => (v i : ℝ)) := by
    funext v
    apply eR.injective
    rw [Function.comp_apply, hnat, Homeomorph.apply_symm_apply]
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
  rw [he]
  exact hd

/-- Every affine space over the rationals has real approximation. -/
theorem hasRealApproximation_affineSpace (ι : Type) :
    letI : IsAffine
      (Over.mk (𝔸(ι; Spec (CommRingCat.of ℚ)) ↘ Spec (CommRingCat.of ℚ))).left :=
        IsAffine.of_isIso (AffineSpace.SpecIso ι (CommRingCat.of ℚ)).hom
    HasRealApproximation
      (Over.mk (𝔸(ι; Spec (CommRingCat.of ℚ)) ↘ Spec (CommRingCat.of ℚ))) := by
  let : IsAffine
      (Over.mk (𝔸(ι; Spec (CommRingCat.of ℚ)) ↘ Spec (CommRingCat.of ℚ))).left :=
    IsAffine.of_isIso (AffineSpace.SpecIso ι (CommRingCat.of ℚ)).hom
  let e : ringTest ℚ (MvPolynomial ι ℚ) ≅
      Over.mk (𝔸(ι; Spec (CommRingCat.of ℚ)) ↘ Spec (CommRingCat.of ℚ)) :=
    Over.isoMk (AffineSpace.SpecIso ι (CommRingCat.of ℚ)).symm
      (AffineSpace.SpecIso_inv_over _)
  exact (hasRealApproximation_polynomialSpectrum ι).of_iso e

end Langlands.AlgebraicGeometry.PointTopology
