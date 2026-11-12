import Langlands.AlgebraicGeometry.AlgebraicSpace.RepresentedAtlasProperty
import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeLocalGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineOpenExtensionProduct
import Langlands.AlgebraicGeometry.AlgebraicSpace.Thickening

/-! # Effective descent of represented properties from a target atlas -/

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- A property of scheme maps descends effectively from a represented pullback
along one surjective étale target atlas. The conclusion includes scheme
representability; the original space map need not be representable a priori. -/
def EtaleAtlasPropertyEffectivity (P : MorphismProperty Scheme.{u}) : Prop :=
  ∀ (S : Scheme.{u}) (X Y : AlgebraicSpace S) (f : X ⟶ Y)
    (U V : Over S)
    (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (b : (schemeYoneda S).obj V ⟶ Y.presheaf) (q : U ⟶ V),
    IsEtale b → IsSurjective b →
    IsPullback a ((schemeYoneda S).map q) (hom f) b →
    P q.left →
    (MorphismProperty.inverseImage P (Over.forget S)).relative (schemeYoneda S) (hom f)

/-- The one-target-atlas effectivity criteria for closed immersions, affine
morphisms, open immersions and finite morphisms of algebraic spaces.
Stacks, Morphisms of Algebraic Spaces, Tags 03M4, 03WG and 03ZQ. -/
def RepresentedAtlasEffectivityStatement : Prop :=
  EtaleAtlasPropertyEffectivity.{u} @_root_.AlgebraicGeometry.IsClosedImmersion ∧
    EtaleAtlasPropertyEffectivity.{u} @IsAffineHom ∧
    EtaleAtlasPropertyEffectivity.{u} @_root_.AlgebraicGeometry.IsOpenImmersion ∧
    EtaleAtlasPropertyEffectivity.{u} @_root_.AlgebraicGeometry.IsFinite

end Langlands.AlgebraicGeometry.AlgebraicSpace
