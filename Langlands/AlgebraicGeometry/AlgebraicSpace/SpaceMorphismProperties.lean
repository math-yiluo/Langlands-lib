import Langlands.AlgebraicGeometry.AlgebraicSpace.SpacePoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.Thickening
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Properties of morphisms of algebraic spaces

Surjective, universally closed, separated, quasi-compact, locally of finite type, proper and
smooth morphisms of algebraic spaces over a scheme `S`, and morphisms with geometrically
connected fibres, following the Stacks Project chapter "Morphisms of Algebraic Spaces". The
morphisms need not be representable. Fibre products are the actual pullbacks of presheaves.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A morphism is surjective when the induced map on points is surjective (Stacks,
Tag 03ME). -/
def IsSurjectiveMorphism (f : X ⟶ Y) : Prop :=
  Function.Surjective (Points.map (hom f))

/-- A morphism is universally closed when for every scheme `T` over `S` and every
`g : h_T ⟶ Y`, the projection from the points of `X ×_Y h_T` to the points of `h_T` is closed
(Stacks, Tags 03HI and 03IT). -/
def IsUniversallyClosedMorphism (f : X ⟶ Y) : Prop :=
  ∀ (T : Over S) (g : (schemeYoneda S).obj T ⟶ Y.presheaf),
    @IsClosedMap _ _ (pointTopology (Limits.pullback (hom f) g))
      (pointTopology ((schemeYoneda S).obj T)) (Points.map (Limits.pullback.snd (hom f) g))

/-- A morphism is separated when its relative diagonal `X ⟶ X ×_Y X` is a representable
closed immersion (Stacks, Tag 03HL). -/
def IsSeparatedMorphism (f : X ⟶ Y) : Prop :=
  IsClosedImmersion (Limits.pullback.diagonal (hom f))

/-- A morphism is quasi-compact when for every affine scheme `T` over `S` and every
`g : h_T ⟶ Y`, the fibre product `X ×_Y h_T` admits a surjective étale map from a quasi-compact
scheme (Stacks, Tags 03HE, 03KG and 03E3). -/
def IsQuasiCompactMorphism (f : X ⟶ Y) : Prop :=
  ∀ (T : Over S), IsAffine T.left → ∀ g : (schemeYoneda S).obj T ⟶ Y.presheaf,
    ∃ (U : Over S) (a : (schemeYoneda S).obj U ⟶ Limits.pullback (hom f) g),
      CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a

/-- A morphism is locally of finite type when there is a commutative square from a scheme
morphism `φ : U ⟶ V` locally of finite type, with `h_U ⟶ X` étale and surjective and
`h_V ⟶ Y` étale (Stacks, Tag 040Y, condition (8)). -/
def IsLocallyOfFiniteTypeMorphism (f : X ⟶ Y) : Prop :=
  ∃ (U V : Over S) (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (b : (schemeYoneda S).obj V ⟶ Y.presheaf) (φ : U ⟶ V),
    IsEtale a ∧ IsSurjective a ∧ IsEtale b ∧ LocallyOfFiniteType φ.left ∧
      a ≫ hom f = (schemeYoneda S).map φ ≫ b

/-- A morphism is proper when it is separated, of finite type and universally closed
(Stacks, Tag 03ZM). -/
def IsProperMorphism (f : X ⟶ Y) : Prop :=
  IsSeparatedMorphism f ∧ IsQuasiCompactMorphism f ∧ IsLocallyOfFiniteTypeMorphism f ∧
    IsUniversallyClosedMorphism f

/-- A morphism is smooth when there is a commutative square from a smooth scheme morphism
`φ : U ⟶ V`, with `h_U ⟶ X` étale and surjective and `h_V ⟶ Y` étale (Stacks, Tag 03ZC). -/
def IsSmoothMorphism (f : X ⟶ Y) : Prop :=
  ∃ (U V : Over S) (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (b : (schemeYoneda S).obj V ⟶ Y.presheaf) (φ : U ⟶ V),
    IsEtale a ∧ IsSurjective a ∧ IsEtale b ∧ Smooth φ.left ∧
      a ≫ hom f = (schemeYoneda S).map φ ≫ b

/-- A morphism has geometrically connected fibres when for every field `K`, every structure
morphism `Spec K ⟶ S` and every point `h_{Spec K} ⟶ Y`, the points of the fibre
`X ×_Y h_{Spec K}` form a connected space. -/
def HasGeometricallyConnectedFibres (f : X ⟶ Y) : Prop :=
  ∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S)
    (y : (schemeYoneda S).obj (Over.mk s) ⟶ Y.presheaf),
    @ConnectedSpace (Points (Limits.pullback (hom f) y)) (pointTopology _)

end Langlands.AlgebraicGeometry.AlgebraicSpace
