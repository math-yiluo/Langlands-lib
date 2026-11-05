import Langlands.AlgebraicGeometry.PointTopology.SmoothOpenMapStatement
import Langlands.AlgebraicGeometry.PointTopology.SubmersiveOpenMap
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMaps
import Langlands.Galois.Local.AbsoluteDefinitions

/-!
# Proof that smooth morphisms are open on local-field rational points

The canonical homeomorphisms identify rational points of affine schemes with algebra points of
their coordinate rings. Under this identification, postcomposition with a morphism is restriction
along its global-section pullback, which is a smooth ring map when the morphism is smooth. The
local field carries its canonical complete nontrivially normed structure, whose topology is the
given one, so the implicit-function argument for smooth algebra maps applies.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- The composite of the rational-point and affine-coordinate homeomorphisms carries
postcomposition with `f` to restriction along the coordinate pullback of `f`. -/
theorem affineRationalPoint_natural (R : Type u) [CommRing R]
    {X Y : Over (Spec (CommRingCat.of R))} [IsAffine X.left] [IsAffine Y.left]
    (f : X ⟶ Y) (p : RationalPoint R X) :
    affineSchemePointEquiv R Y R (rationalPointEquiv R Y (p ≫ f)) =
      AlgPoint.precomp (affineCoordinatePullback R f)
        (affineSchemePointEquiv R X R (rationalPointEquiv R X p)) := by
  rw [rationalPointEquiv_natural, affineSchemePointEquiv_natural]

/-- Over a nonarchimedean local field, restriction of points along a smooth algebra map is open. -/
theorem isOpenMap_precomp_of_smooth_localField (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] {A B : Type u} [CommRing A] [CommRing B]
    [Algebra F A] [Algebra F B] (φ : A →ₐ[F] B) (hφ : (φ : A →+* B).Smooth) :
    IsOpenMap (AlgPoint.precomp (S := F) φ) := by
  let _ := Langlands.LocalGalois.localNormedField F
  have := Langlands.LocalGalois.localNormedField_complete F
  exact SubmersiveOpen.isOpenMap_precomp_of_smooth φ hφ

/-- The rational points of an affine scheme are homeomorphic to the algebra points of its
coordinate ring. -/
def affineRationalPointHomeomorph (R : Type u) [CommRing R] [TopologicalSpace R]
    (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left] :
    letI : TopologicalSpace (RationalPoint R X) := rationalPointTopology R X
    RationalPoint R X ≃ₜ AlgPoint R (AffineCoordinateRing R X) R :=
  letI : TopologicalSpace (RationalPoint R X) := rationalPointTopology R X
  (rationalPointHomeomorph R X).trans (affineSchemePointHomeomorph R X R)

theorem affineRationalPointHomeomorph_apply (R : Type u) [CommRing R] [TopologicalSpace R]
    (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left] (p : RationalPoint R X) :
    affineRationalPointHomeomorph R X p =
      affineSchemePointEquiv R X R (rationalPointEquiv R X p) :=
  rfl

/-- Smoothness of an affine morphism is smoothness of its coordinate pullback. -/
theorem smooth_affineCoordinatePullback (R : Type u) [CommRing R]
    {X Y : Over (Spec (CommRingCat.of R))} [IsAffine X.left] [IsAffine Y.left]
    (f : X ⟶ Y) [Smooth f.left] :
    ((affineCoordinatePullback R f : AffineCoordinateRing R Y →ₐ[R] AffineCoordinateRing R X) :
      AffineCoordinateRing R Y →+* AffineCoordinateRing R X).Smooth :=
  (HasRingHomProperty.iff_of_isAffine (P := @Smooth) (f := f.left)).mp inferInstance

/-- Smooth morphisms of affine schemes over a nonarchimedean local field induce open maps on
rational points. -/
theorem smoothRationalPointOpenMap : SmoothRationalPointOpenMapStatement.{u} := by
  intro F _ _ _ _ X Y _ _ f _
  let _ : TopologicalSpace (RationalPoint F X) := rationalPointTopology F X
  let _ : TopologicalSpace (RationalPoint F Y) := rationalPointTopology F Y
  have hopen : IsOpenMap (AlgPoint.precomp (S := F) (affineCoordinatePullback F f)) :=
    isOpenMap_precomp_of_smooth_localField F _ (smooth_affineCoordinatePullback F f)
  have heq : (fun p : RationalPoint F X => p ≫ f) =
      (affineRationalPointHomeomorph F Y).symm ∘ AlgPoint.precomp (affineCoordinatePullback F f) ∘
        affineRationalPointHomeomorph F X := by
    funext p
    rw [Function.comp_apply, Function.comp_apply, affineRationalPointHomeomorph_apply,
      ← affineRationalPoint_natural, ← affineRationalPointHomeomorph_apply,
      Homeomorph.symm_apply_apply]
  rw [heq]
  exact (affineRationalPointHomeomorph F Y).symm.isOpenMap.comp
    (hopen.comp (affineRationalPointHomeomorph F X).isOpenMap)

end Langlands.AlgebraicGeometry.PointTopology
