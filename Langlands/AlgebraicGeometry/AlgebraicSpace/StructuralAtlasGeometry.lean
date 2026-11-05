import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasIsoTransport
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Structural properties of algebraic spaces through actual scheme atlases

These predicates assert existence of one surjective etale scheme atlas whose
structural morphism has the specified scheme property. No atlas-independence
or reverse represented-scheme comparison is asserted.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- There is an actual surjective etale scheme atlas whose structure map has `P`. -/
def HasAtlasProperty (P : MorphismProperty Scheme.{u}) (X : AlgebraicSpace S) : Prop :=
  ∃ (U : Over S) (a : (schemeYoneda S).obj U ⟶ X.presheaf),
    IsEtale a ∧ IsSurjective a ∧ P U.hom

/-- Structural smoothness over the scheme base, expressed on one actual etale atlas. -/
def SmoothOverBase (X : AlgebraicSpace S) : Prop :=
  HasAtlasProperty (@_root_.AlgebraicGeometry.Smooth.{u}) X

/-- Local finite presentation over the scheme base, expressed on one actual etale atlas. -/
def LocallyOfFinitePresentationOverBase (X : AlgebraicSpace S) : Prop :=
  HasAtlasProperty (@_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u}) X

/-- Local finite type over the scheme base, expressed on one actual etale atlas. -/
def LocallyOfFiniteTypeOverBase (X : AlgebraicSpace S) : Prop :=
  HasAtlasProperty (@_root_.AlgebraicGeometry.LocallyOfFiniteType.{u}) X

variable {P Q : MorphismProperty Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Recover the actual atlas, its geometric conditions and its structure-map property. -/
theorem HasAtlasProperty.exists_atlas (hX : HasAtlasProperty P X) :
    ∃ (U : Over S) (a : (schemeYoneda S).obj U ⟶ X.presheaf),
      IsEtale a ∧ IsSurjective a ∧ P U.hom :=
  hX

/-- An actual atlas with the required structure-map property introduces the predicate. -/
theorem HasAtlasProperty.of_atlas {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (ha : IsEtale a) (hs : IsSurjective a) (hU : P U.hom) : HasAtlasProperty P X :=
  ⟨U, a, ha, hs, hU⟩

/-- A pointwise implication of scheme properties keeps the same actual atlas. -/
theorem HasAtlasProperty.mono (hX : HasAtlasProperty P X) (hPQ : P ≤ Q) :
    HasAtlasProperty Q X := by
  obtain ⟨U, a, ha, hs, hU⟩ := hX
  exact ⟨U, a, ha, hs, hPQ U.hom hU⟩

/-- A scheme with structure-map property `P` has that atlas property via its identity atlas. -/
theorem HasAtlasProperty.of_scheme (U : Over S) (hU : P U.hom) :
    HasAtlasProperty P ((schemeToSpace S).obj U) := by
  refine ⟨U, 𝟙 _, ?_, ?_, hU⟩
  · change IsEtale (𝟙 ((schemeYoneda S).obj U))
    simpa using isEtale_map (𝟙 U) (by change Etale (𝟙 U.left); infer_instance)
  · change (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).relative
      (schemeYoneda S) (𝟙 _)
    have : (MorphismProperty.inverseImage (@Surjective.{u})
        (Over.forget S)).IsStableUnderBaseChange :=
      isStableUnderBaseChange_inverseImage_forget
    simpa using (MorphismProperty.relative_map
      (P := MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S))
      (F := schemeYoneda S) (f := 𝟙 U)
      (by change Surjective (𝟙 U.left); infer_instance))

/-- Transport along a whole-presheaf isomorphism, retaining the actual source scheme. -/
theorem HasAtlasProperty.of_iso (hX : HasAtlasProperty P X)
    (e : X.presheaf ≅ Y.presheaf) : HasAtlasProperty P Y := by
  obtain ⟨U, a, ha, hs, hU⟩ := hX
  exact ⟨U, a ≫ e.hom, ha.comp_iso e, hs.comp_iso e, hU⟩

/-- The existential atlas property is invariant under a whole-presheaf isomorphism. -/
theorem HasAtlasProperty.iff_of_iso (e : X.presheaf ≅ Y.presheaf) :
    HasAtlasProperty P X ↔ HasAtlasProperty P Y :=
  ⟨fun hX => hX.of_iso e, fun hY => hY.of_iso e.symm⟩

/-- Recover an actual smooth-over-base atlas. -/
theorem SmoothOverBase.exists_atlas (hX : SmoothOverBase X) :
    ∃ (U : Over S) (a : (schemeYoneda S).obj U ⟶ X.presheaf),
      IsEtale a ∧ IsSurjective a ∧ Smooth U.hom :=
  hX

/-- Recover an actual locally finitely presented-over-base atlas. -/
theorem LocallyOfFinitePresentationOverBase.exists_atlas
    (hX : LocallyOfFinitePresentationOverBase X) :
    ∃ (U : Over S) (a : (schemeYoneda S).obj U ⟶ X.presheaf),
      IsEtale a ∧ IsSurjective a ∧ LocallyOfFinitePresentation U.hom :=
  hX

/-- Recover an actual locally finite type-over-base atlas. -/
theorem LocallyOfFiniteTypeOverBase.exists_atlas (hX : LocallyOfFiniteTypeOverBase X) :
    ∃ (U : Over S) (a : (schemeYoneda S).obj U ⟶ X.presheaf),
      IsEtale a ∧ IsSurjective a ∧ LocallyOfFiniteType U.hom :=
  hX

/-- Smoothness of an atlas structure map implies its local finite presentation. -/
theorem SmoothOverBase.locallyOfFinitePresentation (hX : SmoothOverBase X) :
    LocallyOfFinitePresentationOverBase X := by
  apply HasAtlasProperty.mono hX
  intro U V f hf
  let := hf
  infer_instance

/-- Local finite presentation of an atlas structure map implies its local finite type. -/
theorem LocallyOfFinitePresentationOverBase.locallyOfFiniteType
    (hX : LocallyOfFinitePresentationOverBase X) : LocallyOfFiniteTypeOverBase X := by
  apply HasAtlasProperty.mono hX
  intro U V f hf
  let := hf
  infer_instance

/-- A smooth-over-base space has a locally finite type-over-base atlas. -/
theorem SmoothOverBase.locallyOfFiniteType (hX : SmoothOverBase X) :
    LocallyOfFiniteTypeOverBase X :=
  hX.locallyOfFinitePresentation.locallyOfFiniteType

/-- The identity atlas introduces structural smoothness of an actual scheme. -/
theorem SmoothOverBase.of_scheme (U : Over S) (hU : Smooth U.hom) :
    SmoothOverBase ((schemeToSpace S).obj U) :=
  HasAtlasProperty.of_scheme U hU

/-- The identity atlas introduces structural local finite presentation of an actual scheme. -/
theorem LocallyOfFinitePresentationOverBase.of_scheme
    (U : Over S) (hU : LocallyOfFinitePresentation U.hom) :
    LocallyOfFinitePresentationOverBase ((schemeToSpace S).obj U) :=
  HasAtlasProperty.of_scheme U hU

/-- The identity atlas introduces structural local finite type of an actual scheme. -/
theorem LocallyOfFiniteTypeOverBase.of_scheme (U : Over S) (hU : LocallyOfFiniteType U.hom) :
    LocallyOfFiniteTypeOverBase ((schemeToSpace S).obj U) :=
  HasAtlasProperty.of_scheme U hU

/-- Structural smoothness transports with the same source scheme. -/
theorem SmoothOverBase.of_iso (hX : SmoothOverBase X) (e : X.presheaf ≅ Y.presheaf) :
    SmoothOverBase Y :=
  HasAtlasProperty.of_iso hX e

/-- Structural local finite presentation transports with the same source scheme. -/
theorem LocallyOfFinitePresentationOverBase.of_iso
    (hX : LocallyOfFinitePresentationOverBase X) (e : X.presheaf ≅ Y.presheaf) :
    LocallyOfFinitePresentationOverBase Y :=
  HasAtlasProperty.of_iso hX e

/-- Structural local finite type transports with the same source scheme. -/
theorem LocallyOfFiniteTypeOverBase.of_iso (hX : LocallyOfFiniteTypeOverBase X)
    (e : X.presheaf ≅ Y.presheaf) : LocallyOfFiniteTypeOverBase Y :=
  HasAtlasProperty.of_iso hX e

/-- Structural smoothness is invariant under a whole-presheaf isomorphism. -/
theorem SmoothOverBase.iff_of_iso (e : X.presheaf ≅ Y.presheaf) :
    SmoothOverBase X ↔ SmoothOverBase Y :=
  HasAtlasProperty.iff_of_iso e

/-- Structural local finite presentation is invariant under a whole-presheaf isomorphism. -/
theorem LocallyOfFinitePresentationOverBase.iff_of_iso (e : X.presheaf ≅ Y.presheaf) :
    LocallyOfFinitePresentationOverBase X ↔ LocallyOfFinitePresentationOverBase Y :=
  HasAtlasProperty.iff_of_iso e

/-- Structural local finite type is invariant under a whole-presheaf isomorphism. -/
theorem LocallyOfFiniteTypeOverBase.iff_of_iso (e : X.presheaf ≅ Y.presheaf) :
    LocallyOfFiniteTypeOverBase X ↔ LocallyOfFiniteTypeOverBase Y :=
  HasAtlasProperty.iff_of_iso e

end Langlands.AlgebraicGeometry.AlgebraicSpace
