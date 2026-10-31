import Langlands.AlgebraicGeometry.Modules.CechResolution.CohomologyBaseChange
import Langlands.AlgebraicGeometry.Modules.CechResolution.Acyclic
import Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentHigherDirectImageVanishingProof
import Langlands.AlgebraicGeometry.Picard.LineBundleQuasicoherent
import Langlands.AlgebraicGeometry.OrderedAffineCoverCompact

/-! # Canonical scalar Čech base change for actual line bundles -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.Modules.CechResolution

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [IsAffineHom g]

/-- Actual line-bundle pullbacks are acyclic for an affine pushforward. -/
lemma isZero_higherDirectImage_pullback_lineBundle (L : LineBundle X) (q : ℕ) :
    IsZero ((higherDirectImage g (q + 1)).obj ((Scheme.Modules.pullback g).obj L.obj)) :=
  affineQuasicoherentHigherDirectImageVanishing Y X g inferInstance
    ((Scheme.Modules.pullback g).obj L.obj) (L.property.isQuasicoherent_pullback g) q

variable {R S : CommRingCat.{u}}
  (φ : R ⟶ S) (f : X ⟶ Spec R) (f' : Y ⟶ Spec S)
  (w : g ≫ f = f' ≫ Spec.map φ) [IsSeparated f]
  (L : LineBundle X)

/-- The canonical scalar comparison for a line bundle and an ordered affine cover
is invertible under flat base change. -/
theorem isIso_scalarBaseChangeMap_lineBundle_of_cech
    (𝒰 : X.OrderedAffineCover)
    (h : IsPullback g f' f (Spec.map φ)) (hφ : φ.hom.Flat)
    (n : ℕ) :
    IsIso (scalarBaseChangeMap φ f f' g w L.obj
      (isZero_higherDirectImage_pullback_lineBundle g L) n) := by
  have : IsSeparated f' := MorphismProperty.of_isPullback h inferInstance
  have : ((Scheme.Modules.pullback g).obj L.obj).IsQuasicoherent :=
    L.property.isQuasicoherent_pullback g
  exact isIso_scalarBaseChangeMap_of_cech φ f f' g w L.obj 𝒰 h hφ
    (isZero_relativeCohomology_cechTerm f 𝒰 L.obj)
    (isZero_relativeCohomology_cechTerm f' (inverseImageCover g 𝒰)
      ((Scheme.Modules.pullback g).obj L.obj))
    (isZero_higherDirectImage_pullback_lineBundle g L) n

/-- The canonical line-bundle scalar comparison packaged as an isomorphism. -/
def lineBundleScalarBaseChangeIsoOfCech
    (𝒰 : X.OrderedAffineCover)
    (h : IsPullback g f' f (Spec.map φ)) (hφ : φ.hom.Flat)
    (n : ℕ) :
    (ModuleCat.extendScalars φ.hom).obj ((relativeCohomology f n).obj L.obj) ≅
      (relativeCohomology f' n).obj ((Scheme.Modules.pullback g).obj L.obj) := by
  have := isIso_scalarBaseChangeMap_lineBundle_of_cech g φ f f' w L 𝒰 h hφ n
  exact asIso (scalarBaseChangeMap φ f f' g w L.obj
    (isZero_higherDirectImage_pullback_lineBundle g L) n)

/-- Quasi-compactness supplies the ordered affine cover needed to prove that
the canonical scalar line-bundle comparison is invertible. -/
theorem isIso_scalarBaseChangeMap_lineBundle [CompactSpace X]
    (h : IsPullback g f' f (Spec.map φ)) (hφ : φ.hom.Flat)
    (n : ℕ) :
    IsIso (scalarBaseChangeMap φ f f' g w L.obj
      (isZero_higherDirectImage_pullback_lineBundle g L) n) :=
  isIso_scalarBaseChangeMap_lineBundle_of_cech g φ f f' w L
    (Scheme.OrderedAffineCover.ofCompactSpace X) h hφ n

/-- Canonical scalar flat base change for an actual line bundle on a
quasi-compact scheme separated over an affine base. -/
def lineBundleScalarBaseChangeIso [CompactSpace X]
    (h : IsPullback g f' f (Spec.map φ)) (hφ : φ.hom.Flat)
    (n : ℕ) :
    (ModuleCat.extendScalars φ.hom).obj ((relativeCohomology f n).obj L.obj) ≅
      (relativeCohomology f' n).obj ((Scheme.Modules.pullback g).obj L.obj) := by
  have := isIso_scalarBaseChangeMap_lineBundle g φ f f' w L h hφ n
  exact asIso (scalarBaseChangeMap φ f f' g w L.obj
    (isZero_higherDirectImage_pullback_lineBundle g L) n)

end Langlands.AlgebraicGeometry.Modules.CechResolution
