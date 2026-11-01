import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Mathlib.CategoryTheory.MorphismProperty.Representable
import Mathlib.CategoryTheory.Limits.Yoneda

/-! # Algebraic spaces over a scheme

We use the Stacks Project fppf-sheaf convention, without a quasi-compactness
condition on the diagonal. Presheaves have values in `Type (u + 1)`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry

namespace AlgebraicSpace

/-- Actual presheaves on schemes over `S`, allowing the universe of rigidified classes. -/
abbrev Presheaf (S : Scheme.{u}) := (Over S)ᵒᵖ ⥤ Type (u + 1)

/-- The actual slice of the fppf topology of schemes. -/
abbrev fppfTopology (S : Scheme.{u}) : GrothendieckTopology (Over S) :=
  Scheme.fppfTopology.over S

/-- Actual type-valued fppf sheaves on schemes over `S`. -/
abbrev FppfSheaf (S : Scheme.{u}) := Sheaf (fppfTopology S) (Type (u + 1))

/-- The functor of points of an actual scheme over `S`, with lifted values. -/
abbrev schemeYoneda (S : Scheme.{u}) : Over S ⥤ Presheaf S :=
  CategoryTheory.uliftYoneda.{u + 1}

/-- Representability by actual schemes of every base change along a scheme's points. -/
def IsRepresentableMorphism {S : Scheme.{u}} {F G : Presheaf S} (f : F ⟶ G) : Prop :=
  (schemeYoneda S).relativelyRepresentable f

/-- A representable transformation is etale when every represented projection is etale. -/
def IsEtale {S : Scheme.{u}} {F G : Presheaf S} (f : F ⟶ G) : Prop :=
  (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).relative
    (schemeYoneda S) f

/-- Geometric surjectivity: every represented projection is a surjective scheme morphism. -/
def IsSurjective {S : Scheme.{u}} {F G : Presheaf S} (f : F ⟶ G) : Prop :=
  (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).relative
    (schemeYoneda S) f

namespace IsRepresentableMorphism

variable {S : Scheme.{u}} {F G : Presheaf S} {f : F ⟶ G}
  (hf : IsRepresentableMorphism f) {U : Over S} (g : (schemeYoneda S).obj U ⟶ G)

/-- The actual scheme over `S` representing the base change of `f` along `g`. -/
abbrev pullback : Over S := Functor.relativelyRepresentable.pullback hf g

/-- The projection to the actual test scheme in a represented base change. -/
abbrev snd : hf.pullback g ⟶ U := Functor.relativelyRepresentable.snd hf g

/-- The first projection of the represented base change, as a natural transformation. -/
abbrev fst : (schemeYoneda S).obj (hf.pullback g) ⟶ F :=
  Functor.relativelyRepresentable.fst hf g

/-- The represented square has the pullback universal property in actual presheaves. -/
theorem isPullback : IsPullback (hf.fst g) ((schemeYoneda S).map (hf.snd g)) f g :=
  Functor.relativelyRepresentable.isPullback hf g

end IsRepresentableMorphism

/-- Etale transformations are representable by actual schemes. -/
theorem IsEtale.representable {S : Scheme.{u}} {F G : Presheaf S} {f : F ⟶ G}
    (hf : IsEtale f) : IsRepresentableMorphism f := hf.1

/-- Every actual projection in a represented pullback of an etale map is etale. -/
theorem IsEtale.projection {S : Scheme.{u}} {F G : Presheaf S} {f : F ⟶ G}
    (hf : IsEtale f) {U V : Over S} (g : (schemeYoneda S).obj U ⟶ G)
    (a : (schemeYoneda S).obj V ⟶ F) (p : V ⟶ U)
    (h : IsPullback a ((schemeYoneda S).map p) f g) : Etale p.left :=
  hf.2 g a p h

/-- Geometrically surjective transformations are representable by actual schemes. -/
theorem IsSurjective.representable {S : Scheme.{u}} {F G : Presheaf S} {f : F ⟶ G}
    (hf : IsSurjective f) : IsRepresentableMorphism f := hf.1

/-- Every actual projection in a represented pullback of a surjective map is surjective. -/
theorem IsSurjective.projection {S : Scheme.{u}} {F G : Presheaf S} {f : F ⟶ G}
    (hf : IsSurjective f) {U V : Over S} (g : (schemeYoneda S).obj U ⟶ G)
    (a : (schemeYoneda S).obj V ⟶ F) (p : V ⟶ U)
    (h : IsPullback a ((schemeYoneda S).map p) f g) : Surjective p.left :=
  hf.2 g a p h

/-- The diagonal is representable by actual schemes over the base. -/
def HasRepresentableDiagonal {S : Scheme.{u}} (F : Presheaf S) : Prop :=
  IsRepresentableMorphism (Limits.diag F)

/-- The geometric conditions on an actual fppf sheaf in the Stacks convention. -/
def IsAlgebraicSpace (S : Scheme.{u}) (F : FppfSheaf S) : Prop :=
  HasRepresentableDiagonal F.obj ∧
    ∃ (U : Over S) (a : (schemeYoneda S).obj U ⟶ F.obj), IsEtale a ∧ IsSurjective a

/-- The actual fppf sheaf represented by a scheme, with lifted values. -/
abbrev schemeSheaf (S : Scheme.{u}) : Over S ⥤ FppfSheaf S :=
  GrothendieckTopology.uliftYoneda.{u + 1} (fppfTopology S)

/-- A scheme has representable diagonal because schemes over `S` have pullbacks. -/
theorem scheme_hasRepresentableDiagonal {S : Scheme.{u}} (U : Over S) :
    HasRepresentableDiagonal ((schemeYoneda S).obj U) := by
  apply Functor.relativelyRepresentable.diag_of_map_from_obj
  intro V g
  obtain ⟨h, rfl⟩ := (schemeYoneda S).map_surjective g
  exact Functor.relativelyRepresentable.map (schemeYoneda S) h

/-- A scheme is an algebraic space: its identity is a surjective etale atlas. -/
theorem scheme_isAlgebraicSpace {S : Scheme.{u}} (U : Over S) :
    IsAlgebraicSpace S ((schemeSheaf S).obj U) := by
  refine ⟨scheme_hasRepresentableDiagonal U, U, 𝟙 _, ?_, ?_⟩
  · change (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).relative
      (schemeYoneda S) (𝟙 _)
    let : MorphismProperty.RespectsIso (@Etale.{u}) :=
      Etale.etale_isStableUnderBaseChange.respectsIso
    let := MorphismProperty.RespectsIso.inverseImage (@Etale.{u}) (Over.forget S)
    apply MorphismProperty.relative.of_exists
    intro V g
    refine ⟨V, g, 𝟙 V, ?_, ?_⟩
    · simpa using IsPullback.of_id_snd (f := g)
    · change Etale (𝟙 V.left)
      infer_instance
  · change (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).relative
      (schemeYoneda S) (𝟙 _)
    let := MorphismProperty.RespectsIso.inverseImage (@Surjective.{u}) (Over.forget S)
    apply MorphismProperty.relative.of_exists
    intro V g
    refine ⟨V, g, 𝟙 V, ?_, ?_⟩
    · simpa using IsPullback.of_id_snd (f := g)
    · change Surjective (𝟙 V.left)
      infer_instance

end AlgebraicSpace

/-- An actual fppf sheaf with representable diagonal and a surjective etale scheme atlas. -/
abbrev AlgebraicSpace (S : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (AlgebraicSpace.IsAlgebraicSpace S)

namespace AlgebraicSpace

variable {S : Scheme.{u}}

/-- The underlying actual fppf sheaf. -/
abbrev toSheaf (X : AlgebraicSpace S) : FppfSheaf S := X.obj

/-- The underlying actual presheaf. -/
abbrev presheaf (X : AlgebraicSpace S) : Presheaf S := X.toSheaf.obj

/-- Sections over an actual scheme over the base. -/
abbrev sections (X : AlgebraicSpace S) (T : Over S) : Type (u + 1) :=
  X.presheaf.obj (op T)

/-- Pullback of sections along an actual morphism over the base. -/
abbrev pullback (X : AlgebraicSpace S) {T U : Over S} (f : T ⟶ U) :
    X.sections U → X.sections T :=
  X.presheaf.map f.op

@[simp]
theorem pullback_id (X : AlgebraicSpace S) (T : Over S) (x : X.sections T) :
    X.pullback (𝟙 T) x = x :=
  X.presheaf.map_id_apply (op T) x

@[simp]
theorem pullback_comp (X : AlgebraicSpace S) {T U V : Over S}
    (f : T ⟶ U) (g : U ⟶ V) (x : X.sections V) :
    X.pullback (f ≫ g) x = X.pullback f (X.pullback g x) :=
  X.presheaf.map_comp_apply g.op f.op x

/-- The underlying presheaf of a space has representable diagonal. -/
theorem hasRepresentableDiagonal (X : AlgebraicSpace S) :
    HasRepresentableDiagonal X.presheaf := X.property.1

/-- A map from an actual scheme to a space is representable, by its representable diagonal. -/
theorem representable_from_scheme (X : AlgebraicSpace S) {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ X.presheaf) : IsRepresentableMorphism a :=
  Functor.relativelyRepresentable.of_diag X.hasRepresentableDiagonal a

/-- Every space admits an actual representable surjective etale scheme atlas. -/
theorem exists_atlas (X : AlgebraicSpace S) :
    ∃ (U : Over S) (a : (schemeYoneda S).obj U ⟶ X.presheaf),
      IsRepresentableMorphism a ∧ IsEtale a ∧ IsSurjective a := by
  obtain ⟨U, a, ha, hs⟩ := X.property.2
  exact ⟨U, a, ha.representable, ha, hs⟩

/-- The natural transformation underlying a morphism of algebraic spaces. -/
abbrev hom {X Y : AlgebraicSpace S} (f : X ⟶ Y) : X.presheaf ⟶ Y.presheaf :=
  f.hom.hom

/-- Evaluation of a morphism on sections over an actual test scheme. -/
abbrev mapSections {X Y : AlgebraicSpace S} (f : X ⟶ Y) (T : Over S) :
    X.sections T → Y.sections T :=
  (hom f).app (op T)

/-- Evaluation of a morphism commutes with pullback of sections. -/
theorem mapSections_naturality {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {T U : Over S} (g : T ⟶ U) (x : X.sections U) :
    Y.pullback g (mapSections f U x) = mapSections f T (X.pullback g x) := by
  exact (ConcreteCategory.congr_hom ((hom f).naturality g.op) x).symm

/-- Every natural transformation of the underlying presheaves is a morphism. -/
def homMk {X Y : AlgebraicSpace S} (f : X.presheaf ⟶ Y.presheaf) : X ⟶ Y :=
  ObjectProperty.homMk (ObjectProperty.homMk f)

/-- Morphisms are exactly natural transformations of the underlying sheaves. -/
def homEquiv (X Y : AlgebraicSpace S) : (X ⟶ Y) ≃ (X.presheaf ⟶ Y.presheaf) where
  toFun := hom
  invFun := homMk
  left_inv _ := rfl
  right_inv _ := rfl

/-- Forgetting the geometric conditions retains the actual sheaf. -/
abbrev forgetToSheaf (S : Scheme.{u}) : AlgebraicSpace S ⥤ FppfSheaf S :=
  ObjectProperty.ι (IsAlgebraicSpace S)

/-- Forgetting to the actual presheaf, on both objects and natural transformations. -/
abbrev forgetToPresheaf (S : Scheme.{u}) : AlgebraicSpace S ⥤ Presheaf S :=
  forgetToSheaf S ⋙ sheafToPresheaf (fppfTopology S) (Type (u + 1))

/-- The fully faithful inclusion of actual schemes over `S` into algebraic spaces. -/
def schemeToSpace (S : Scheme.{u}) : Over S ⥤ AlgebraicSpace S :=
  ObjectProperty.lift (IsAlgebraicSpace S) (schemeSheaf S) scheme_isAlgebraicSpace

/-- Full faithfulness is the lifted Yoneda full faithfulness. -/
def schemeToSpaceFullyFaithful (S : Scheme.{u}) : (schemeToSpace S).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := forgetToSheaf S)
    ((fppfTopology S).fullyFaithfulUliftYoneda)

instance (S : Scheme.{u}) : (schemeToSpace S).Full :=
  (schemeToSpaceFullyFaithful S).full

instance (S : Scheme.{u}) : (schemeToSpace S).Faithful :=
  (schemeToSpaceFullyFaithful S).faithful

/-- Scheme representability is an additional property, witnessed by an actual natural isomorphism. -/
def IsRepresentedByScheme (X : AlgebraicSpace S) : Prop :=
  ∃ U : Over S, Nonempty ((schemeYoneda S).obj U ≅ X.presheaf)

/-- A scheme included as a space is represented by that actual scheme. -/
theorem schemeToSpace_isRepresentedByScheme (U : Over S) :
    IsRepresentedByScheme ((schemeToSpace S).obj U) :=
  ⟨U, ⟨Iso.refl _⟩⟩

end AlgebraicSpace

end Langlands.AlgebraicGeometry
