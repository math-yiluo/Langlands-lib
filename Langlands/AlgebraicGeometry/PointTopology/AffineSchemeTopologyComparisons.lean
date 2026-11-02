import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyAxioms
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Comparisons for arbitrary affine scheme topology assignments
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

theorem spectrumAlgebraPointEquiv_natural
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (p : RingPoint R (ringTest R B) S) :
    spectrumAlgebraPointEquiv R S A (p ≫ ringTestMap R f) =
      AlgPoint.precomp f (spectrumAlgebraPointEquiv R S B p) := by
  dsimp only [RingPoint] at p
  let q : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B) := p.left
  apply AlgHom.coe_ringHom_injective
  change (Spec.preimage (q ≫ Spec.map (CommRingCat.ofHom f.toRingHom))).hom =
    (Spec.preimage q).hom.comp f.toRingHom
  rw [Spec.preimage_comp, Spec.preimage_map]
  rfl

theorem spectrumAlgebraPointEquiv_symm_natural
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (p : AlgPoint R B S) :
    (spectrumAlgebraPointEquiv R S A).symm (AlgPoint.precomp f p) =
      (spectrumAlgebraPointEquiv R S B).symm p ≫ ringTestMap R f := by
  apply (spectrumAlgebraPointEquiv R S A).injective
  rw [Equiv.apply_symm_apply, spectrumAlgebraPointEquiv_natural, Equiv.apply_symm_apply]

/-- The point equivalence is a homeomorphism for the induced algebra-to-scheme
assignment, without any axioms on that assignment. -/
def algebraTopologySchemePointHomeomorph (T : AffinePointTopologyFamily R S)
    (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]
    [LocallyOfFiniteType X.hom] :
    letI := algebraTopologyFamilyToSchemes R S T X
    letI := T (CommAlgCat.of R (AffineCoordinateRing R X))
    RingPoint R X S ≃ₜ AlgPoint R (AffineCoordinateRing R X) S := by
  letI := algebraTopologyFamilyToSchemes R S T X
  letI := T (CommAlgCat.of R (AffineCoordinateRing R X))
  exact (affineSchemePointEquiv R X S).toHomeomorphOfIsInducing ⟨rfl⟩

/-- The direct spectrum point equivalence is a homeomorphism for the
scheme-to-algebra induced assignment. -/
def schemeTopologySpectrumPointHomeomorph (T : AffineSchemeTopologyFamily R S)
    (A : Type u) [CommRing A] [Algebra R A] [Algebra.FiniteType R A] :
    letI := T (ringTest R A)
    letI := schemeTopologyFamilyToAlgebras R S T (CommAlgCat.of R A)
    RingPoint R (ringTest R A) S ≃ₜ AlgPoint R A S := by
  letI := T (ringTest R A)
  letI := schemeTopologyFamilyToAlgebras R S T (CommAlgCat.of R A)
  exact ((spectrumAlgebraPointEquiv R S A).symm.toHomeomorphOfIsInducing ⟨rfl⟩).symm

theorem affineTopology_isHomeomorph_algEquiv
    (T : AffinePointTopologyFamily R S)
    (hfun : AffineTopologyFunctorial R S T)
    (A B : CommAlgCat.{u} R) [Algebra.FiniteType R A] [Algebra.FiniteType R B]
    (e : A ≃ₐ[R] B) :
    @IsHomeomorph (AlgPoint R B S) (AlgPoint R A S) (T B) (T A)
      (AlgPoint.precomp e.toAlgHom) := by
  let := T A
  let := T B
  apply isHomeomorph_iff_exists_inverse.mpr
  refine ⟨hfun A B (CommAlgCat.ofHom e.toAlgHom),
    AlgPoint.precomp e.symm.toAlgHom, ?_, ?_,
    hfun B A (CommAlgCat.ofHom e.symm.toAlgHom)⟩
  · intro p
    ext b
    simp
  · intro p
    ext a
    simp

/-- Under functoriality the direct spectrum comparison also preserves an
algebra assignment transported to schemes. -/
theorem algebraTopology_spectrum_isHomeomorph
    (T : AffinePointTopologyFamily R S)
    (hfun : AffineTopologyFunctorial R S T)
    (A : Type u) [CommRing A] [Algebra R A] [Algebra.FiniteType R A] :
    @IsHomeomorph (RingPoint R (ringTest R A) S) (AlgPoint R A S)
      (algebraTopologyFamilyToSchemes R S T (ringTest R A)) (T (CommAlgCat.of R A))
      (spectrumAlgebraPointEquiv R S A) := by
  let := T (CommAlgCat.of R A)
  let := T (CommAlgCat.of R (AffineCoordinateRing R (ringTest R A)))
  let := algebraTopologyFamilyToSchemes R S T (ringTest R A)
  have hcoord := (algebraTopologySchemePointHomeomorph R S T (ringTest R A)).isHomeomorph
  have hiso := affineTopology_isHomeomorph_algEquiv R S T hfun
    (CommAlgCat.of R A)
    (CommAlgCat.of R (AffineCoordinateRing R (ringTest R A)))
    (spectrumCoordinateAlgEquiv R A).symm
  have hcomp := hiso.comp hcoord
  have he : (spectrumAlgebraPointEquiv R S A :
      RingPoint R (ringTest R A) S → AlgPoint R A S) =
      AlgPoint.precomp (spectrumCoordinateAlgEquiv R A).symm.toAlgHom ∘
        (affineSchemePointEquiv R (ringTest R A) S) := by
    funext p
    rw [Function.comp_apply, affineSchemePointEquiv_spectrum]
    ext a
    change spectrumAlgebraPointEquiv R S A p a =
      spectrumAlgebraPointEquiv R S A p
        ((spectrumCoordinateAlgEquiv R A)
          ((spectrumCoordinateAlgEquiv R A).symm a))
    rw [AlgEquiv.apply_symm_apply]
  rw [he]
  exact hcomp

theorem affineTopology_transport_recover
    (T : AffinePointTopologyFamily R S)
    (hfun : AffineTopologyFunctorial R S T) :
    schemeTopologyFamilyToAlgebras R S (algebraTopologyFamilyToSchemes R S T) = T := by
  funext A _
  let := T A
  let := algebraTopologyFamilyToSchemes R S T (ringTest R A)
  have h := algebraTopology_spectrum_isHomeomorph R S T hfun A
  exact ((spectrumAlgebraPointEquiv R S A).toHomeomorphOfIsInducing
    h.isInducing).symm.isInducing.eq_induced.symm

theorem spectrumPointPair_compatible_iff
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : C →ₐ[R] A) (g : C →ₐ[R] B)
    (p : RingPoint R (ringTest R A) S) (q : RingPoint R (ringTest R B) S) :
    p ≫ ringTestMap R f = q ≫ ringTestMap R g ↔
      AlgPoint.precomp f (spectrumAlgebraPointEquiv R S A p) =
        AlgPoint.precomp g (spectrumAlgebraPointEquiv R S B q) := by
  rw [← spectrumAlgebraPointEquiv_natural, ← spectrumAlgebraPointEquiv_natural]
  exact (spectrumAlgebraPointEquiv R S C).injective.eq_iff.symm

def schemeTopologySpectrumCompatiblePairHomeomorph
    (T : AffineSchemeTopologyFamily R S)
    (A B C : CommAlgCat.{u} R)
    [Algebra.FiniteType R A] [Algebra.FiniteType R B] [Algebra.FiniteType R C]
    (f : C ⟶ A) (g : C ⟶ B) :
    letI := T (ringTest R A)
    letI := T (ringTest R B)
    letI := schemeTopologyFamilyToAlgebras R S T A
    letI := schemeTopologyFamilyToAlgebras R S T B
    {q : RingPoint R (ringTest R A) S × RingPoint R (ringTest R B) S //
      q.1 ≫ ringTestMap R f.hom = q.2 ≫ ringTestMap R g.hom} ≃ₜ
    {q : AlgPoint R A S × AlgPoint R B S //
      AlgPoint.precomp f.hom q.1 = AlgPoint.precomp g.hom q.2} := by
  letI := T (ringTest R A)
  letI := T (ringTest R B)
  letI := schemeTopologyFamilyToAlgebras R S T A
  letI := schemeTopologyFamilyToAlgebras R S T B
  exact ((schemeTopologySpectrumPointHomeomorph R S T A).prodCongr
    (schemeTopologySpectrumPointHomeomorph R S T B)).subtype
      (fun q => spectrumPointPair_compatible_iff R S f.hom g.hom q.1 q.2)

def algebraTopologySchemeCompatiblePairHomeomorph
    (T : AffinePointTopologyFamily R S)
    (X Y Z : Over (Spec (CommRingCat.of R)))
    [IsAffine X.left] [IsAffine Y.left] [IsAffine Z.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    letI := algebraTopologyFamilyToSchemes R S T X
    letI := algebraTopologyFamilyToSchemes R S T Y
    letI := T (CommAlgCat.of R (AffineCoordinateRing R X))
    letI := T (CommAlgCat.of R (AffineCoordinateRing R Y))
    {q : RingPoint R X S × RingPoint R Y S // q.1 ≫ f = q.2 ≫ g} ≃ₜ
    {q : AlgPoint R (AffineCoordinateRing R X) S ×
        AlgPoint R (AffineCoordinateRing R Y) S //
      AlgPoint.precomp (affineCoordinatePullback R f) q.1 =
        AlgPoint.precomp (affineCoordinatePullback R g) q.2} := by
  letI := algebraTopologyFamilyToSchemes R S T X
  letI := algebraTopologyFamilyToSchemes R S T Y
  letI := T (CommAlgCat.of R (AffineCoordinateRing R X))
  letI := T (CommAlgCat.of R (AffineCoordinateRing R Y))
  exact ((algebraTopologySchemePointHomeomorph R S T X).prodCongr
    (algebraTopologySchemePointHomeomorph R S T Y)).subtype
      (fun q => affineSchemePointPair_compatible_iff R S q.1 q.2)

/-- Functoriality alone forces an arbitrary scheme assignment to respect
actual relative isomorphisms. -/
theorem affineSchemeTopology_isHomeomorph_iso
    (T : AffineSchemeTopologyFamily R S)
    (hfun : AffineSchemeTopologyFunctorial R S T)
    (X Y : Over (Spec (CommRingCat.of R))) [IsAffine X.left] [IsAffine Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (e : X ≅ Y) :
    @IsHomeomorph (RingPoint R X S) (RingPoint R Y S) (T X) (T Y)
      (fun p => p ≫ e.hom) := by
  let := T X
  let := T Y
  apply isHomeomorph_iff_exists_inverse.mpr
  refine ⟨hfun X Y e.hom, (fun p => p ≫ e.inv), ?_, ?_, hfun Y X e.inv⟩
  · intro p
    dsimp only [RingPoint] at p ⊢
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · intro p
    dsimp only [RingPoint] at p ⊢
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem affineSchemePointEquiv_overIso
    (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]
    (p : RingPoint R X S) :
    affineSchemePointEquiv R X S p =
      spectrumAlgebraPointEquiv R S (AffineCoordinateRing R X)
        (p ≫ (affineSchemeOverIso R X).hom) := by
  dsimp only [RingPoint] at p
  change spectrumAlgebraPointEquiv R S (AffineCoordinateRing R X)
      ((𝟙 _ ≫ p) ≫ (affineSchemeOverIso R X).hom) = _
  rw [Category.id_comp]

/-- A functorial scheme assignment is recovered by restricting to actual
spectra and transporting back through global sections. -/
theorem affineSchemeTopology_transport_recover
    (T : AffineSchemeTopologyFamily R S)
    (hfun : AffineSchemeTopologyFunctorial R S T) :
    algebraTopologyFamilyToSchemes R S (schemeTopologyFamilyToAlgebras R S T) = T := by
  funext X _ _
  let := T X
  let := T (ringTest R (AffineCoordinateRing R X))
  let := schemeTopologyFamilyToAlgebras R S T
    (CommAlgCat.of R (AffineCoordinateRing R X))
  have hspec := (schemeTopologySpectrumPointHomeomorph R S T
    (AffineCoordinateRing R X)).isHomeomorph
  have hiso := affineSchemeTopology_isHomeomorph_iso R S T hfun X
    (ringTest R (AffineCoordinateRing R X)) (affineSchemeOverIso R X)
  have hcomp := hspec.comp hiso
  change IsHomeomorph ((spectrumAlgebraPointEquiv R S (AffineCoordinateRing R X)) ∘
    fun p : RingPoint R X S => p ≫ (affineSchemeOverIso R X).hom) at hcomp
  have hpoint : IsHomeomorph (affineSchemePointEquiv R X S) := by
    have he : (affineSchemePointEquiv R X S :
        RingPoint R X S → AlgPoint R (AffineCoordinateRing R X) S) =
        (spectrumAlgebraPointEquiv R S (AffineCoordinateRing R X)) ∘
          (fun p : RingPoint R X S => p ≫ (affineSchemeOverIso R X).hom) := by
      funext p
      exact affineSchemePointEquiv_overIso R S X p
    rw [he]
    exact hcomp
  exact hpoint.isInducing.eq_induced.symm

theorem evaluationAlgebraTopology_toSchemes [TopologicalSpace S] :
    algebraTopologyFamilyToSchemes R S (evaluationAffineTopologyFamily R S) =
      evaluationAffineSchemeTopologyFamily R S := rfl

theorem evaluationSchemeTopology_toAlgebras [TopologicalSpace S] :
    schemeTopologyFamilyToAlgebras R S (evaluationAffineSchemeTopologyFamily R S) =
      evaluationAffineTopologyFamily R S := by
  funext A _
  exact (spectrumAlgebraPointHomeomorph R S A).symm.isInducing.eq_induced.symm

end Langlands.AlgebraicGeometry.PointTopology
