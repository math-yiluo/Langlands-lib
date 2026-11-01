import Langlands.Geometry.EtaleInverseImageAffineExact
import Langlands.Geometry.EtaleInverseImageRestriction
import Langlands.Geometry.EtaleImageFunctoriality
import Langlands.Geometry.EtaleRestrictionCover
import Mathlib.AlgebraicGeometry.Cover.Open

/-! # Exactness of the constructed inverse image for arbitrary scheme maps -/

noncomputable section

universe u v w vB uB vC uC

namespace Langlands.Geometry.EtaleInverseImage

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open EtalePullback EtaleRestrictionCover

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (R : Type u) [CommRing R]

/-- Inverse image commutes with etale restriction in any actual commuting
square. This is assembled from the constructed composition and restriction
comparisons, without an input base-change isomorphism. -/
def inverseImageRestrictionSquare {X Z Y W : Scheme.{u}}
    (f : Z ⟶ X) (i : Y ⟶ X) [Etale i]
    (j : W ⟶ Z) [Etale j] (g : W ⟶ Y) (h : j ≫ f = g ≫ i) :
    inverseImage f R ⋙ restriction j (ModuleCat.{u} R) ≅
      restriction i (ModuleCat.{u} R) ⋙ inverseImage g R :=
  Functor.isoWhiskerLeft (inverseImage f R) (inverseImageIsoRestriction j R).symm ≪≫
    inverseImageComp R f j ≪≫ inverseImageCongr R h ≪≫
    (inverseImageComp R i g).symm ≪≫
    Functor.isoWhiskerRight (inverseImageIsoRestriction i R) (inverseImage g R)

/-- The chosen affine open cover, regarded as an etale scheme cover. -/
def affineEtaleCover (X : Scheme.{u}) : X.Cover (Scheme.precoverage (@Etale)) :=
  X.affineCover.changeProp fun _ => inferInstance

instance affineEtaleCover_map_etale (X : Scheme.{u}) (i : (affineEtaleCover X).I₀) :
    Etale ((affineEtaleCover X).f i) :=
  (affineEtaleCover X).map_prop i

instance affineEtaleCover_isAffine (X : Scheme.{u}) (i : (affineEtaleCover X).I₀) :
    IsAffine ((affineEtaleCover X).X i) :=
  inferInstanceAs (IsAffine (X.affineCover.X i))

/-- Pull back the actual affine etale cover along an arbitrary scheme map. -/
def pulledBackAffineCover {X Z : Scheme.{u}} (f : Z ⟶ X) :
    Z.Cover (Scheme.precoverage (@Etale)) :=
  (affineEtaleCover X).pullback₂ f

instance pulledBackAffineCover_map_etale {X Z : Scheme.{u}} (f : Z ⟶ X)
    (i : (pulledBackAffineCover f).I₀) : Etale ((pulledBackAffineCover f).f i) :=
  (pulledBackAffineCover f).map_prop i

/-- The local geometric comparison at each member of the pulled-back
affine cover. -/
def inverseImageAffineLocalIso {X Z : Scheme.{u}} (f : Z ⟶ X)
    (i : (affineEtaleCover X).I₀) :
    inverseImage f R ⋙
        restriction ((pulledBackAffineCover f).f i) (ModuleCat.{u} R) ≅
      restriction ((affineEtaleCover X).f i) (ModuleCat.{u} R) ⋙
        inverseImage (pullback.fst ((affineEtaleCover X).f i) f) R :=
  inverseImageRestrictionSquare R f ((affineEtaleCover X).f i)
    ((pulledBackAffineCover f).f i) (pullback.fst _ _) pullback.condition.symm

instance inverseImageAffineLocal_preservesFiniteLimits {X Z : Scheme.{u}} (f : Z ⟶ X)
    (i : (affineEtaleCover X).I₀) :
    PreservesFiniteLimits (inverseImage f R ⋙
      restriction ((pulledBackAffineCover f).f i) (ModuleCat.{u} R)) :=
  preservesFiniteLimits_of_natIso (inverseImageAffineLocalIso R f i).symm

section ProductLimits

variable {I : Type v} {C : I → Type uC} [∀ i, Category.{vC} (C i)]
    {B : Type uB} [Category.{vB} B] {J : Type w} [Category J]
    {F : J ⥤ (∀ i, C i)}

/-- The limiting lift in a product of categories is built componentwise.
The independent universes are needed for the actual large sheaf categories. -/
private def productIsLimit {c : Cone F}
    (hc : ∀ i, IsLimit ((Pi.eval C i).mapCone c)) : IsLimit c where
  lift s i := (hc i).lift {
    pt := s.pt i
    π := {
      app := fun j => s.π.app j i
      naturality := fun j j' a => congr_fun (s.π.naturality a) i } }
  fac s j := by
    funext i
    exact (hc i).fac _ j
  uniq s m hm := by
    funext i
    apply (hc i).uniq
      { pt := s.pt i
        π := {
          app := fun j => s.π.app j i
          naturality := fun j j' a => congr_fun (s.π.naturality a) i } } (m i)
    intro j
    exact congr_fun (hm j) i

end ProductLimits

variable {X Z : Scheme.{u}} (f : Z ⟶ X)

instance inverseImage_restrictedFamily_preservesFiniteLimits :
    PreservesFiniteLimits (inverseImage f R ⋙
      restrictionFamily (coverObjects (pulledBackAffineCover f)) (ModuleCat.{u} R)) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u}
  intro J _ _
  exact { preservesLimit := {
    preserves := fun hc => ⟨productIsLimit (fun i =>
      isLimitOfPreserves (inverseImage f R ⋙
        restriction ((pulledBackAffineCover f).f i) (ModuleCat.{u} R)) hc)⟩ } }

/-- The original constructed inverse image preserves finite limits for
every scheme morphism. Exactness is detected on the pulled-back affine cover. -/
instance inverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (inverseImage f R) := by
  have := restrictionFamilyReflectsFiniteLimits
    (coverObjects (pulledBackAffineCover f)) R
      (coverObjects_coversTop (pulledBackAffineCover f))
  exact preservesFiniteLimits_of_reflects_of_preserves (inverseImage f R)
    (restrictionFamily (coverObjects (pulledBackAffineCover f)) (ModuleCat.{u} R))

/-- The canonical finite-limit comparison for any geometric inverse image. -/
def inverseImageLimitIso {J : Type*} [SmallCategory J] [FinCategory J]
    (F : J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (inverseImage f R).obj (limit F) ≅ limit (F ⋙ inverseImage f R) :=
  preservesLimitIso (inverseImage f R) F

/-- The actual affine-Kan/sheafification inverse image, now equipped with
proved exactness for an arbitrary scheme morphism. -/
def inverseImageExactFunctor :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} R) ⥤ₑ
      Sheaf Z.smallEtaleTopology (ModuleCat.{u} R) :=
  ExactFunctor.of (inverseImage f R)

@[simp] theorem inverseImageExactFunctor_obj :
    (inverseImageExactFunctor R f).obj = inverseImage f R := rfl

end Langlands.Geometry.EtaleInverseImage
