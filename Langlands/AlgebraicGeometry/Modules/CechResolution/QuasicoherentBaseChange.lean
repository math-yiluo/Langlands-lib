import Langlands.AlgebraicGeometry.Modules.CechResolution.CohomologyBaseChange
import Langlands.AlgebraicGeometry.Modules.CechResolution.Acyclic
import Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentHigherDirectImageVanishingProof
import Langlands.AlgebraicGeometry.Modules.PullbackQuasicoherent
import Langlands.AlgebraicGeometry.OrderedAffineCoverCompact

/-! # Canonical scalar flat base change for quasi-coherent modules -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open scoped TensorProduct ChangeOfRings

namespace Langlands.AlgebraicGeometry.Modules.CechResolution

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [IsAffineHom g]

/-- The actual pullback of a quasi-coherent module is acyclic for affine pushforward. -/
lemma isZero_higherDirectImage_pullback_quasicoherent
    (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    IsZero ((higherDirectImage g (q + 1)).obj ((Scheme.Modules.pullback g).obj M)) :=
  affineQuasicoherentHigherDirectImageVanishing Y X g inferInstance
    ((Scheme.Modules.pullback g).obj M) inferInstance q

variable {R S : CommRingCat.{u}}
  (φ : R ⟶ S) (f : X ⟶ Spec R) (f' : Y ⟶ Spec S)
  (w : g ≫ f = f' ≫ Spec.map φ) [IsSeparated f]
  (M : X.Modules) [M.IsQuasicoherent]

/-- An ordered affine cover proves invertibility of the canonical scalar comparison
for any quasi-coherent coefficient module under flat base change. -/
theorem isIso_scalarBaseChangeMap_quasicoherent_of_cech
    (𝒰 : X.OrderedAffineCover)
    (h : IsPullback g f' f (Spec.map φ)) (hφ : φ.hom.Flat)
    (n : ℕ) :
    IsIso (scalarBaseChangeMap φ f f' g w M
      (isZero_higherDirectImage_pullback_quasicoherent g M) n) := by
  have : IsSeparated f' := MorphismProperty.of_isPullback h inferInstance
  exact isIso_scalarBaseChangeMap_of_cech φ f f' g w M 𝒰 h hφ
    (isZero_relativeCohomology_cechTerm f 𝒰 M)
    (isZero_relativeCohomology_cechTerm f' (inverseImageCover g 𝒰)
      ((Scheme.Modules.pullback g).obj M))
    (isZero_higherDirectImage_pullback_quasicoherent g M) n

/-- The canonical scalar comparison packaged as an isomorphism using a chosen cover. -/
def quasicoherentScalarBaseChangeIsoOfCech
    (𝒰 : X.OrderedAffineCover)
    (h : IsPullback g f' f (Spec.map φ)) (hφ : φ.hom.Flat)
    (n : ℕ) :
    (ModuleCat.extendScalars φ.hom).obj ((relativeCohomology f n).obj M) ≅
      (relativeCohomology f' n).obj ((Scheme.Modules.pullback g).obj M) := by
  have := isIso_scalarBaseChangeMap_quasicoherent_of_cech g φ f f' w M 𝒰 h hφ n
  exact asIso (scalarBaseChangeMap φ f f' g w M
    (isZero_higherDirectImage_pullback_quasicoherent g M) n)

/-- Quasi-compactness supplies the ordered affine cover for canonical scalar flat
base change of a quasi-coherent module. -/
theorem isIso_scalarBaseChangeMap_quasicoherent [CompactSpace X]
    (h : IsPullback g f' f (Spec.map φ)) (hφ : φ.hom.Flat)
    (n : ℕ) :
    IsIso (scalarBaseChangeMap φ f f' g w M
      (isZero_higherDirectImage_pullback_quasicoherent g M) n) :=
  isIso_scalarBaseChangeMap_quasicoherent_of_cech g φ f f' w M
    (Scheme.OrderedAffineCover.ofCompactSpace X) h hφ n

/-- Canonical scalar flat base change of any quasi-coherent module on a quasi-compact
scheme separated over an affine base. -/
def quasicoherentScalarBaseChangeIso [CompactSpace X]
    (h : IsPullback g f' f (Spec.map φ)) (hφ : φ.hom.Flat)
    (n : ℕ) :
    (ModuleCat.extendScalars φ.hom).obj ((relativeCohomology f n).obj M) ≅
      (relativeCohomology f' n).obj ((Scheme.Modules.pullback g).obj M) := by
  have := isIso_scalarBaseChangeMap_quasicoherent g φ f f' w M h hφ n
  exact asIso (scalarBaseChangeMap φ f f' g w M
    (isZero_higherDirectImage_pullback_quasicoherent g M) n)

/-- The forward map is the specified canonical scalar cohomology map. -/
@[simp]
lemma quasicoherentScalarBaseChangeIso_hom [CompactSpace X]
    (h : IsPullback g f' f (Spec.map φ)) (hφ : φ.hom.Flat) (n : ℕ) :
    (quasicoherentScalarBaseChangeIso g φ f f' w M h hφ n).hom =
      scalarBaseChangeMap φ f f' g w M
        (isZero_higherDirectImage_pullback_quasicoherent g M) n := rfl

/-- On `1 ⊗ x`, the forward isomorphism is the published semilinear base-change map. -/
lemma quasicoherentScalarBaseChangeIso_one_tmul [CompactSpace X]
    (h : IsPullback g f' f (Spec.map φ)) (hφ : φ.hom.Flat)
    (n : ℕ) (x : (relativeCohomology f n).obj M) :
    (quasicoherentScalarBaseChangeIso g φ f f' w M h hφ n).hom
        ((1 : S) ⊗ₜ[R,φ.hom] x) =
      baseChangeMap φ f f' g w M
        (isZero_higherDirectImage_pullback_quasicoherent g M)
        (fun J hJ q => (pushforwardInjectiveAcyclic Y X g J hJ q).2 R f) n x :=
  scalarBaseChangeMap_one_tmul φ f f' g w M
    (isZero_higherDirectImage_pullback_quasicoherent g M) _ n x

/-- The canonical isomorphisms are natural in quasi-coherent coefficients. -/
@[reassoc]
lemma quasicoherentScalarBaseChangeIso_naturality [CompactSpace X]
    (h : IsPullback g f' f (Spec.map φ)) (hφ : φ.hom.Flat)
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (a : M ⟶ N) (n : ℕ) :
    (ModuleCat.extendScalars φ.hom).map ((relativeCohomology f n).map a) ≫
        (quasicoherentScalarBaseChangeIso g φ f f' w N h hφ n).hom =
      (quasicoherentScalarBaseChangeIso g φ f f' w M h hφ n).hom ≫
        (relativeCohomology f' n).map ((Scheme.Modules.pullback g).map a) :=
  scalarBaseChangeMap_naturality φ f f' g w a
    (isZero_higherDirectImage_pullback_quasicoherent g M)
    (isZero_higherDirectImage_pullback_quasicoherent g N) n

end Langlands.AlgebraicGeometry.Modules.CechResolution
