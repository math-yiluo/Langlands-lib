import Langlands.AlgebraicGeometry.PointTopology.AffineScheme

/-!
# Global-section maps for affine scheme points

The pullback is the actual map on global sections of a scheme morphism.
Its compatibility with the specified base and with actual relative points
is proved through the fully faithful spectrum functor.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R]
variable {X Y : Over (Spec (CommRingCat.of R))} [IsAffine X.left] [IsAffine Y.left]

theorem affineCoordinateMap_natural (f : X ⟶ Y) :
    f.left.appTop.hom.comp (affineCoordinateMap R Y) = affineCoordinateMap R X := by
  have h :
      Spec.preimage (Y.left.isoSpec.inv ≫ Y.hom) ≫ f.left.appTop =
        Spec.preimage (X.left.isoSpec.inv ≫ X.hom) := by
    apply Spec.map_injective
    simp only [Spec.map_comp, Spec.map_preimage]
    rw [← Category.assoc, Scheme.isoSpec_inv_naturality, Category.assoc, Over.w f]
  exact congrArg (fun g => g.hom) h

/-- The actual global-section pullback, as an algebra map over the given base. -/
def affineCoordinatePullback (f : X ⟶ Y) :
    AffineCoordinateRing R Y →ₐ[R] AffineCoordinateRing R X where
  toRingHom := f.left.appTop.hom
  commutes' r := congrArg (fun g : R →+* AffineCoordinateRing R X => g r)
    (affineCoordinateMap_natural R f)

@[simp] theorem affineCoordinatePullback_apply (f : X ⟶ Y)
    (a : AffineCoordinateRing R Y) :
    affineCoordinatePullback R f a = f.left.appTop.hom a := rfl

@[simp] theorem affineCoordinatePullback_id :
    affineCoordinatePullback R (𝟙 X) = AlgHom.id R (AffineCoordinateRing R X) := by
  ext a
  change (Scheme.Hom.appTop (𝟙 X.left)).hom a = a
  rw [Scheme.Hom.id_appTop]
  rfl

theorem affineCoordinatePullback_comp
    {Z : Over (Spec (CommRingCat.of R))} [IsAffine Z.left]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    affineCoordinatePullback R (f ≫ g) =
      (affineCoordinatePullback R f).comp (affineCoordinatePullback R g) := by
  ext a
  change (f.left ≫ g.left).appTop.hom a = f.left.appTop.hom (g.left.appTop.hom a)
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- An actual affine scheme isomorphism induces the contravariant isomorphism
of its coordinate algebras over the specified base. -/
def affineCoordinateAlgEquiv (e : X ≅ Y) :
    AffineCoordinateRing R Y ≃ₐ[R] AffineCoordinateRing R X :=
  AlgEquiv.ofAlgHom (affineCoordinatePullback R e.hom)
    (affineCoordinatePullback R e.inv)
    (by rw [← affineCoordinatePullback_comp, Iso.hom_inv_id, affineCoordinatePullback_id])
    (by rw [← affineCoordinatePullback_comp, Iso.inv_hom_id, affineCoordinatePullback_id])

variable (S : Type u) [CommRing S] [Algebra R S]

/-- The coordinate point gives exactly the spectrum of the original point
followed by the canonical affine isomorphism. -/
theorem affineSchemePointEquiv_spec (p : RingPoint R X S) :
    Spec.map (CommRingCat.ofHom
      (affineSchemePointEquiv R X S p).toAlgHom.toRingHom) =
        p.left ≫ X.left.isoSpec.hom := by
  change Spec.map (Spec.preimage _) = _
  exact Spec.map_preimage _

/-- Scheme-point composition agrees with precomposition of algebra points. -/
theorem affineSchemePointEquiv_natural (f : X ⟶ Y) (p : RingPoint R X S) :
    affineSchemePointEquiv R Y S (p ≫ f) =
      AlgPoint.precomp (affineCoordinatePullback R f) (affineSchemePointEquiv R X S p) := by
  dsimp only [RingPoint] at p
  apply AlgHom.coe_ringHom_injective
  suffices h : CommRingCat.ofHom
      (affineSchemePointEquiv R Y S (p ≫ f)).toAlgHom.toRingHom =
      f.left.appTop ≫ CommRingCat.ofHom
        (affineSchemePointEquiv R X S p).toAlgHom.toRingHom by
    exact congrArg (fun g => g.hom) h
  apply Spec.map_injective
  change Spec.map (Spec.preimage ((p.left ≫ f.left) ≫ Y.left.isoSpec.hom)) =
    Spec.map (f.left.appTop ≫ Spec.preimage (p.left ≫ X.left.isoSpec.hom))
  rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage]
  change (p.left ≫ f.left) ≫ Y.left.isoSpec.hom =
    (p.left ≫ X.left.isoSpec.hom) ≫ Spec.map f.left.appTop
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => p.left ≫ k)
      (Scheme.isoSpec_hom_naturality f.left).symm).trans
        (Category.assoc _ _ _).symm)

/-- The coordinate-algebra comparison realizes an actual scheme isomorphism
as a homeomorphism on its relative point spaces. -/
def affineSchemePointIsoHomeomorph [TopologicalSpace S] (e : X ≅ Y) :
    RingPoint R X S ≃ₜ RingPoint R Y S :=
  ((affineSchemePointHomeomorph R X S).trans
    (AlgPoint.congr (affineCoordinateAlgEquiv R e).symm)).trans
      (affineSchemePointHomeomorph R Y S).symm

@[simp] theorem affineSchemePointIsoHomeomorph_apply [TopologicalSpace S]
    (e : X ≅ Y) (p : RingPoint R X S) :
    affineSchemePointIsoHomeomorph R S e p = p ≫ e.hom := by
  apply (affineSchemePointEquiv R Y S).injective
  change (affineSchemePointEquiv R Y S)
    ((affineSchemePointEquiv R Y S).symm
      (AlgPoint.precomp (affineCoordinatePullback R e.hom)
        (affineSchemePointEquiv R X S p))) =
    affineSchemePointEquiv R Y S (p ≫ e.hom)
  rw [Equiv.apply_symm_apply]
  exact (affineSchemePointEquiv_natural R S e.hom p).symm

section Spectrum

variable (A : Type u) [CommRing A] [Algebra R A]

instance ringTest_isAffine : IsAffine (ringTest R A).left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))

theorem spectrumCoordinateMap :
    affineCoordinateMap R (ringTest R A) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.comp (algebraMap R A) := by
  change (Spec.preimage ((Spec (CommRingCat.of A)).isoSpec.inv ≫
    Spec.algebraMap R A)).hom = _
  rw [Scheme.isoSpec_Spec_inv, ← Spec.map_comp, Spec.preimage_map]
  rfl

/-- The global-section coordinate algebra of a spectrum is its original algebra,
with the specified base structure retained. -/
def spectrumCoordinateAlgEquiv :
    AffineCoordinateRing R (ringTest R A) ≃ₐ[R] A :=
  { (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv with
    commutes' r := by
      change (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
        (affineCoordinateMap R (ringTest R A) r) = algebraMap R A r
      rw [spectrumCoordinateMap]
      exact congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of A =>
        f.hom (algebraMap R A r)) (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id }

@[simp] theorem spectrumCoordinateAlgEquiv_apply
    (a : AffineCoordinateRing R (ringTest R A)) :
    spectrumCoordinateAlgEquiv R A a =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom a := rfl

/-- The canonical global-section point comparison agrees with the existing
spectrum point comparison after the actual coordinate-algebra isomorphism. -/
theorem affineSchemePointEquiv_spectrum (p : RingPoint R (ringTest R A) S) :
    affineSchemePointEquiv R (ringTest R A) S p =
      AlgPoint.precomp (spectrumCoordinateAlgEquiv R A).toAlgHom
        (AlgPoint.ofAlgHom (affineRingPointEquiv R A S p)) := by
  dsimp only [RingPoint] at p
  apply AlgHom.coe_ringHom_injective
  suffices h : CommRingCat.ofHom
      (affineSchemePointEquiv R (ringTest R A) S p).toAlgHom.toRingHom =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫
        Spec.preimage p.left by
    exact congrArg (fun g => g.hom) h
  apply Spec.map_injective
  let g : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of A) := p.left
  change Spec.map (Spec.preimage (g ≫ (Spec (CommRingCat.of A)).isoSpec.hom)) =
    Spec.map ((Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ Spec.preimage g)
  simp only [Spec.map_preimage, Spec.map_comp, Scheme.isoSpec_Spec_hom]

/-- The identity on the actual relative spectrum morphism identifies the
global-section topology with the previously constructed spectrum topology. -/
def spectrumRingPointHomeomorph [TopologicalSpace S] :
    RingPoint R (ringTest R A) S ≃ₜ SpecPoint R A S :=
  ((affineSchemePointHomeomorph R (ringTest R A) S).trans
    (AlgPoint.congr (spectrumCoordinateAlgEquiv R A))).trans
      (specPointHomeomorph R A S).symm

@[simp] theorem spectrumRingPointHomeomorph_apply [TopologicalSpace S]
    (p : RingPoint R (ringTest R A) S) :
    (spectrumRingPointHomeomorph R S A p).val = p.left := by
  dsimp only [RingPoint] at p
  have h := affineSchemePointEquiv_spectrum R S A p
  change (Spec.homEquivAlgHom.symm
    ((AlgPoint.congr (spectrumCoordinateAlgEquiv R A))
      (affineSchemePointEquiv R (ringTest R A) S p))).val = p.left
  rw [h]
  change (Spec.homEquivAlgHom.symm
    ((affineRingPointEquiv R A S p).comp
      ((spectrumCoordinateAlgEquiv R A).toAlgHom.comp
        (spectrumCoordinateAlgEquiv R A).symm.toAlgHom))).val = p.left
  simp
  exact congrArg Subtype.val
    (Spec.homEquivAlgHom.symm_apply_apply
      ((ringPointEquiv R (ringTest R A) S) p))

/-- Any actual affine spectrum presentation gives the same point topology.
The map is postcomposition with that presentation. -/
def affinePresentationPointHomeomorph [TopologicalSpace S] (e : X ≅ ringTest R A) :
    RingPoint R X S ≃ₜ SpecPoint R A S :=
  (affineSchemePointIsoHomeomorph R S e).trans (spectrumRingPointHomeomorph R S A)

@[simp] theorem affinePresentationPointHomeomorph_apply [TopologicalSpace S]
    (e : X ≅ ringTest R A) (p : RingPoint R X S) :
    (affinePresentationPointHomeomorph R S A e p).val = p.left ≫ e.hom.left := by
  change (spectrumRingPointHomeomorph R S A
    (affineSchemePointIsoHomeomorph R S e p)).val = _
  rw [spectrumRingPointHomeomorph_apply, affineSchemePointIsoHomeomorph_apply]
  rfl

end Spectrum

end Langlands.AlgebraicGeometry.PointTopology
