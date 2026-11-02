import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyComparisons

/-!
# Transport of the four affine topology axioms
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

theorem schemeTopology_toAlgebras_functorial
    (T : AffineSchemeTopologyFamily R S)
    (hfun : AffineSchemeTopologyFunctorial R S T) :
    AffineTopologyFunctorial R S (schemeTopologyFamilyToAlgebras R S T) := by
  intro A B _ _ f
  let := T (ringTest R A)
  let := T (ringTest R B)
  let := schemeTopologyFamilyToAlgebras R S T A
  let := schemeTopologyFamilyToAlgebras R S T B
  have h := (schemeTopologySpectrumPointHomeomorph R S T A).continuous.comp
    ((hfun _ _ (ringTestMap R f.hom)).comp
      (schemeTopologySpectrumPointHomeomorph R S T B).symm.continuous)
  have he : (AlgPoint.precomp f.hom : AlgPoint R B S → AlgPoint R A S) =
      (spectrumAlgebraPointEquiv R S A) ∘
        (fun p : RingPoint R (ringTest R B) S => p ≫ ringTestMap R f.hom) ∘
          (spectrumAlgebraPointEquiv R S B).symm := by
    funext p
    change AlgPoint.precomp f.hom p = spectrumAlgebraPointEquiv R S A
      (((spectrumAlgebraPointEquiv R S B).symm p) ≫ ringTestMap R f.hom)
    rw [spectrumAlgebraPointEquiv_natural, Equiv.apply_symm_apply]
  rw [he]
  exact h

theorem schemeTopology_toAlgebras_quotientEmbeddings
    (T : AffineSchemeTopologyFamily R S)
    (hclosed : AffineSchemeTopologyClosedImmersions R S T) :
    AffineTopologyQuotientEmbeddings R S (schemeTopologyFamilyToAlgebras R S T) := by
  intro A B _ _ f hf
  let := T (ringTest R A)
  let := T (ringTest R B)
  let := schemeTopologyFamilyToAlgebras R S T A
  let := schemeTopologyFamilyToAlgebras R S T B
  let : IsClosedImmersion (ringTestMap R f.hom).left :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom f.hom.toRingHom) hf
  have h := (schemeTopologySpectrumPointHomeomorph R S T A).isEmbedding.comp
    ((hclosed _ _ (ringTestMap R f.hom)).comp
      (schemeTopologySpectrumPointHomeomorph R S T B).symm.isEmbedding)
  have he : (AlgPoint.precomp f.hom : AlgPoint R B S → AlgPoint R A S) =
      (spectrumAlgebraPointEquiv R S A) ∘
        (fun p : RingPoint R (ringTest R B) S => p ≫ ringTestMap R f.hom) ∘
          (spectrumAlgebraPointEquiv R S B).symm := by
    funext p
    change AlgPoint.precomp f.hom p = spectrumAlgebraPointEquiv R S A
      (((spectrumAlgebraPointEquiv R S B).symm p) ≫ ringTestMap R f.hom)
    rw [spectrumAlgebraPointEquiv_natural, Equiv.apply_symm_apply]
  rw [he]
  exact h

theorem schemeTopology_toAlgebras_line [TopologicalSpace S]
    (T : AffineSchemeTopologyFamily R S)
    (hline : AffineSchemeTopologyLine R S T) :
    AffineTopologyLine R S (schemeTopologyFamilyToAlgebras R S T) := by
  let := T (ringTest R (MvPolynomial Unit R))
  let := schemeTopologyFamilyToAlgebras R S T
    (CommAlgCat.of R (MvPolynomial Unit R))
  have h := hline.comp
    (schemeTopologySpectrumPointHomeomorph R S T (MvPolynomial Unit R)).symm.isHomeomorph
  have he : (fun p : AlgPoint R (MvPolynomial Unit R) S => p (MvPolynomial.X ())) =
      (fun p : RingPoint R (ringTest R (MvPolynomial Unit R)) S =>
        spectrumAlgebraPointEquiv R S (MvPolynomial Unit R) p (MvPolynomial.X ())) ∘
          (spectrumAlgebraPointEquiv R S (MvPolynomial Unit R)).symm := by
    funext p
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  change IsHomeomorph (fun p : AlgPoint R (MvPolynomial Unit R) S =>
    p (MvPolynomial.X ()))
  rw [he]
  exact h

theorem schemeTopology_toAlgebras_pushouts
    (T : AffineSchemeTopologyFamily R S)
    (hpull : AffineSchemeTopologyPullbacks R S T) :
    AffineTopologyPushouts R S (schemeTopologyFamilyToAlgebras R S T) := by
  intro A B C _ _ _ f g c _ hc
  let := T (ringTest R A)
  let := T (ringTest R B)
  let := T (ringTest R c.pt)
  let := schemeTopologyFamilyToAlgebras R S T A
  let := schemeTopologyFamilyToAlgebras R S T B
  let := schemeTopologyFamilyToAlgebras R S T c.pt
  let : IsAffine (algebraSpectrumPullback R c).pt.left :=
    inferInstanceAs (IsAffine (ringTest R c.pt).left)
  let : LocallyOfFiniteType (algebraSpectrumPullback R c).pt.hom :=
    inferInstanceAs (LocallyOfFiniteType (ringTest R c.pt).hom)
  let : TopologicalSpace (RingPoint R (algebraSpectrumPullback R c).pt S) :=
    T (ringTest R c.pt)
  have hcone := hpull _ _ _ (ringTestMap R f.hom) (ringTestMap R g.hom)
    (algebraSpectrumPullback R c) (algebraSpectrumPullbackIsLimit R c hc)
  have h := (schemeTopologySpectrumCompatiblePairHomeomorph R S T A B C f g).isHomeomorph.comp
    (hcone.comp (schemeTopologySpectrumPointHomeomorph R S T c.pt).symm.isHomeomorph)
  have he : affinePushoutPointComparison R S c =
      (schemeTopologySpectrumCompatiblePairHomeomorph R S T A B C f g) ∘
        (affineSchemePullbackPointComparison R S (algebraSpectrumPullback R c)) ∘
          (spectrumAlgebraPointEquiv R S c.pt).symm := by
    funext p
    apply Subtype.ext
    apply Prod.ext
    · exact ((spectrumAlgebraPointEquiv_natural R S c.inl.hom
        ((spectrumAlgebraPointEquiv R S c.pt).symm p)).trans
          (congrArg (AlgPoint.precomp c.inl.hom) (Equiv.apply_symm_apply _ p))).symm
    · exact ((spectrumAlgebraPointEquiv_natural R S c.inr.hom
        ((spectrumAlgebraPointEquiv R S c.pt).symm p)).trans
          (congrArg (AlgPoint.precomp c.inr.hom) (Equiv.apply_symm_apply _ p))).symm
  rw [he]
  exact h

theorem schemeTopology_toAlgebras_axioms [TopologicalSpace S]
    (T : AffineSchemeTopologyFamily R S)
    (h : AffineSchemeTopologyAxioms R S T) :
    AffineTopologyAxioms R S (schemeTopologyFamilyToAlgebras R S T) :=
  ⟨schemeTopology_toAlgebras_functorial R S T h.1,
    schemeTopology_toAlgebras_pushouts R S T h.2.1,
    schemeTopology_toAlgebras_quotientEmbeddings R S T h.2.2.1,
    schemeTopology_toAlgebras_line R S T h.2.2.2⟩

theorem algebraTopology_toSchemes_functorial
    (T : AffinePointTopologyFamily R S)
    (hfun : AffineTopologyFunctorial R S T) :
    AffineSchemeTopologyFunctorial R S (algebraTopologyFamilyToSchemes R S T) := by
  intro X Y _ _ _ _ f
  let := T (CommAlgCat.of R (AffineCoordinateRing R X))
  let := T (CommAlgCat.of R (AffineCoordinateRing R Y))
  let := algebraTopologyFamilyToSchemes R S T X
  let := algebraTopologyFamilyToSchemes R S T Y
  have h := (algebraTopologySchemePointHomeomorph R S T Y).symm.continuous.comp
    ((hfun _ _ (CommAlgCat.ofHom (affineCoordinatePullback R f))).comp
      (algebraTopologySchemePointHomeomorph R S T X).continuous)
  have he : (fun p : RingPoint R X S => p ≫ f) =
      (affineSchemePointEquiv R Y S).symm ∘
        (AlgPoint.precomp (affineCoordinatePullback R f)) ∘
          (affineSchemePointEquiv R X S) := by
    funext p
    apply (affineSchemePointEquiv R Y S).injective
    change affineSchemePointEquiv R Y S (p ≫ f) =
      affineSchemePointEquiv R Y S
        ((affineSchemePointEquiv R Y S).symm
          (AlgPoint.precomp (affineCoordinatePullback R f)
            (affineSchemePointEquiv R X S p)))
    rw [Equiv.apply_symm_apply, affineSchemePointEquiv_natural]
  rw [he]
  exact h

theorem algebraTopology_toSchemes_closedImmersions
    (T : AffinePointTopologyFamily R S)
    (hquot : AffineTopologyQuotientEmbeddings R S T) :
    AffineSchemeTopologyClosedImmersions R S (algebraTopologyFamilyToSchemes R S T) := by
  intro X Y _ _ _ _ f _
  let := T (CommAlgCat.of R (AffineCoordinateRing R X))
  let := T (CommAlgCat.of R (AffineCoordinateRing R Y))
  let := algebraTopologyFamilyToSchemes R S T X
  let := algebraTopologyFamilyToSchemes R S T Y
  have hf : Function.Surjective (affineCoordinatePullback R f) :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine f.left).2
  have h := (algebraTopologySchemePointHomeomorph R S T Y).symm.isEmbedding.comp
    ((hquot _ _ (CommAlgCat.ofHom (affineCoordinatePullback R f)) hf).comp
      (algebraTopologySchemePointHomeomorph R S T X).isEmbedding)
  have he : (fun p : RingPoint R X S => p ≫ f) =
      (affineSchemePointEquiv R Y S).symm ∘
        (AlgPoint.precomp (affineCoordinatePullback R f)) ∘
          (affineSchemePointEquiv R X S) := by
    funext p
    apply (affineSchemePointEquiv R Y S).injective
    change affineSchemePointEquiv R Y S (p ≫ f) =
      affineSchemePointEquiv R Y S
        ((affineSchemePointEquiv R Y S).symm
          (AlgPoint.precomp (affineCoordinatePullback R f)
            (affineSchemePointEquiv R X S p)))
    rw [Equiv.apply_symm_apply, affineSchemePointEquiv_natural]
  rw [he]
  exact h

theorem algebraTopology_toSchemes_line [TopologicalSpace S]
    (T : AffinePointTopologyFamily R S)
    (hfun : AffineTopologyFunctorial R S T)
    (hline : AffineTopologyLine R S T) :
    AffineSchemeTopologyLine R S (algebraTopologyFamilyToSchemes R S T) := by
  let := T (CommAlgCat.of R (MvPolynomial Unit R))
  let := algebraTopologyFamilyToSchemes R S T (ringTest R (MvPolynomial Unit R))
  exact hline.comp (algebraTopology_spectrum_isHomeomorph R S T hfun (MvPolynomial Unit R))

theorem algebraTopology_toSchemes_pullbacks
    (T : AffinePointTopologyFamily R S)
    (hpush : AffineTopologyPushouts R S T) :
    AffineSchemeTopologyPullbacks R S (algebraTopologyFamilyToSchemes R S T) := by
  intro X Y Z _ _ _ _ _ _ f g c _ _ hc
  let := T (CommAlgCat.of R (AffineCoordinateRing R X))
  let := T (CommAlgCat.of R (AffineCoordinateRing R Y))
  let := T (CommAlgCat.of R (AffineCoordinateRing R c.pt))
  let := algebraTopologyFamilyToSchemes R S T X
  let := algebraTopologyFamilyToSchemes R S T Y
  let := algebraTopologyFamilyToSchemes R S T c.pt
  let : Algebra.FiniteType R (affineCoordinatePushout R c).pt :=
    inferInstanceAs (Algebra.FiniteType R (AffineCoordinateRing R c.pt))
  let : TopologicalSpace (AlgPoint R (affineCoordinatePushout R c).pt S) :=
    T (CommAlgCat.of R (AffineCoordinateRing R c.pt))
  let H := algebraTopologySchemeCompatiblePairHomeomorph R S T X Y Z f g
  have hcoord := hpush _ _ _ (CommAlgCat.ofHom (affineCoordinatePullback R f))
    (CommAlgCat.ofHom (affineCoordinatePullback R g))
    (affineCoordinatePushout R c) (affineCoordinatePushoutIsColimit R c hc)
  have h := H.symm.isHomeomorph.comp
    (hcoord.comp (algebraTopologySchemePointHomeomorph R S T c.pt).isHomeomorph)
  have he : affineSchemePullbackPointComparison R S c =
      H.symm ∘ (affinePushoutPointComparison R S (affineCoordinatePushout R c)) ∘
        (affineSchemePointEquiv R c.pt S) := by
    funext p
    apply H.injective
    change H (affineSchemePullbackPointComparison R S c p) =
      H (H.symm (affinePushoutPointComparison R S (affineCoordinatePushout R c)
        (affineSchemePointEquiv R c.pt S p)))
    rw [Homeomorph.apply_symm_apply]
    exact affineSchemePullbackPointComparison_coordinates R S c p
  rw [he]
  exact h

theorem algebraTopology_toSchemes_axioms [TopologicalSpace S]
    (T : AffinePointTopologyFamily R S)
    (h : AffineTopologyAxioms R S T) :
    AffineSchemeTopologyAxioms R S (algebraTopologyFamilyToSchemes R S T) :=
  ⟨algebraTopology_toSchemes_functorial R S T h.1,
    algebraTopology_toSchemes_pullbacks R S T h.2.1,
    algebraTopology_toSchemes_closedImmersions R S T h.2.2.1,
    algebraTopology_toSchemes_line R S T h.1 h.2.2.2⟩

theorem affineSchemeTopologyTransport_proof [TopologicalSpace S] [IsTopologicalRing S] :
    AffineSchemeTopologyTransportProperty R S :=
  ⟨fun T h => ⟨algebraTopology_toSchemes_axioms R S T h,
      affineTopology_transport_recover R S T h.1⟩,
    fun T h => ⟨schemeTopology_toAlgebras_axioms R S T h,
      affineSchemeTopology_transport_recover R S T h.1⟩⟩

end Langlands.AlgebraicGeometry.PointTopology
