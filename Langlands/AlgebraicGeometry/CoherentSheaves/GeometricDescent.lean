import Langlands.AlgebraicGeometry.CoherentSheaves.Pullback
import Langlands.AlgebraicGeometry.Modules.GeometricQuasicoherentDescent
import Langlands.AlgebraicGeometry.Modules.FinitePresentationDescent

/-! # Geometric descent of actual flat finitely presented families -/

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry
open Langlands.Scheme.Modules.LineBundleFlatDescent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.CoherentSheaves

/-- The actual family condition is detected by flat locally finitely presented
surjective base change. -/
lemma isFamily_iff_pullback_of_fppf
    {X Y B T : Scheme.{u}} {p : X ⟶ Y} {q : X ⟶ T} {f : Y ⟶ B} {g : T ⟶ B}
    (H : IsPullback p q f g) [Flat g] [LocallyOfFinitePresentation g] [Surjective g]
    (M : Y.Modules) :
    IsFamily f M ↔ IsFamily q ((Scheme.Modules.pullback p).obj M) := by
  have : Flat p := MorphismProperty.of_isPullback H.flip inferInstance
  have : LocallyOfFinitePresentation p :=
    MorphismProperty.of_isPullback H.flip inferInstance
  have : Surjective p := MorphismProperty.of_isPullback H.flip inferInstance
  constructor
  · intro hM
    let : M.IsFinitePresentation := hM.1
    exact ⟨Modules.isFinitePresentation_pullback p M,
      Modules.isFlatOver_pullback_of_isPullback H M hM.2⟩
  · intro hM
    let : ((Scheme.Modules.pullback p).obj M).IsFinitePresentation := hM.1
    exact ⟨Modules.isFinitePresentation_of_pullback_fppf p M,
      (Modules.isFlatOver_iff_pullback_of_flat_surjective H M).mpr hM.2⟩

namespace GeometricDescent

open Modules.GeometricQuasicoherentDescent

variable {X Y : Scheme.{u}} {p : X ⟶ Y} {F : X.Modules} (D : Datum p F)

/-- Local finite presentation of an effective module follows from that of the
cover module for a flat locally finitely presented surjection. -/
lemma isFinitePresentation_of_str [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    [F.IsFinitePresentation] {M : Y.Modules} (S : Str D (𝟙 Y) M) :
    M.IsFinitePresentation := by
  have : ((Scheme.Modules.pullback p).obj M).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
      (pullbackIsoOfStr D S).symm inferInstance
  exact Modules.isFinitePresentation_of_pullback_fppf p M

variable {B T : Scheme.{u}} {f : Y ⟶ B} {g : T ⟶ B} {q : X ⟶ T}

/-- An effective structure on a base module descends the actual family condition
through a Cartesian flat locally finitely presented surjection. -/
lemma isFamily_of_str (H : IsPullback p q f g)
    [Flat g] [LocallyOfFinitePresentation g] [Surjective g]
    (hF : IsFamily q F) {M : Y.Modules} (S : Str D (𝟙 Y) M) : IsFamily f M := by
  have : Flat p := MorphismProperty.of_isPullback H.flip inferInstance
  have : LocallyOfFinitePresentation p :=
    MorphismProperty.of_isPullback H.flip inferInstance
  have : Surjective p := MorphismProperty.of_isPullback H.flip inferInstance
  let : F.IsFinitePresentation := hF.1
  exact ⟨isFinitePresentation_of_str D S,
    isFlatOver_of_str_of_isPullback D H S hF.2⟩

/-- The descended object is an object of the published actual family category. -/
def familyOfStr (H : IsPullback p q f g)
    [Flat g] [LocallyOfFinitePresentation g] [Surjective g]
    (hF : IsFamily q F) {M : Y.Modules} (S : Str D (𝟙 Y) M) : Family f :=
  ⟨M, isFamily_of_str D H hF S⟩

/-- Every geometric datum on a family along an affine fppf Cartesian base change
has an effective actual family, with comparisons on all scheme tests. -/
lemma exists_family (H : IsPullback p q f g)
    [IsAffineHom g] [Flat g] [LocallyOfFinitePresentation g] [Surjective g]
    (hF : IsFamily q F) : ∃ M : Family f, Nonempty (Str D (𝟙 Y) M.obj) := by
  have : IsAffineHom p := MorphismProperty.of_isPullback H.flip inferInstance
  have : Flat p := MorphismProperty.of_isPullback H.flip inferInstance
  have : Surjective p := MorphismProperty.of_isPullback H.flip inferInstance
  let : F.IsFinitePresentation := hF.1
  obtain ⟨M, _, ⟨S⟩⟩ := exists_str D (𝟙 Y)
  exact ⟨familyOfStr D H hF S, ⟨S⟩⟩

/-- Compatible isomorphisms are unique in the actual family category. -/
lemma existsUnique_family_iso [IsAffineHom p] [Flat p] [Surjective p]
    [F.IsQuasicoherent] {M N : Family f}
    (S : Str D (𝟙 Y) M.obj) (S' : Str D (𝟙 Y) N.obj) :
    ∃! e : M ≅ N, Str.Hom S S' ((Family.forget f).map e.hom) := by
  obtain ⟨e, he, hu⟩ := existsUnique_iso D S S'
  refine ⟨ObjectProperty.isoMk _ e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply ObjectProperty.hom_ext
  exact congrArg Iso.hom (hu ((Family.forget f).mapIso e') he')

end GeometricDescent

namespace FamilyGroupoid

variable {S X : Scheme.{u}} (f : X ⟶ S) {T U : Over S} (h : U ⟶ T)

/-- Family detection on the actual relative spaces, over the full slice. -/
lemma isFamily_iff_pullback_of_fppf [Flat h.left] [LocallyOfFinitePresentation h.left]
    [Surjective h.left] (M : ((Picard.relativeSpace f).obj T).Modules) :
    IsFamily ((Picard.relativeProjection f).app T) M ↔
      IsFamily ((Picard.relativeProjection f).app U)
        ((Scheme.Modules.pullback ((Picard.relativeSpace f).map h)).obj M) :=
  CoherentSheaves.isFamily_iff_pullback_of_fppf (Picard.relativeProjection_isPullback f h) M

/-- A geometric cocycle on an actual cover family is effective in the actual
family groupoid, with its all-test comparison structure. -/
lemma exists_effective_of_affine_fppf [IsAffineHom h.left] [Flat h.left]
    [LocallyOfFinitePresentation h.left] [Surjective h.left]
    (F : FamilyGroupoid f U)
    (D : Datum ((Picard.relativeSpace f).map h) F.of.obj) :
    ∃ M : FamilyGroupoid f T, Nonempty (Str D (𝟙 _) M.of.obj) := by
  obtain ⟨M, hM⟩ := GeometricDescent.exists_family D
    (Picard.relativeProjection_isPullback f h) F.of.property
  exact ⟨⟨M⟩, hM⟩

/-- Every effective structure gives an actual arrow from the ordinary pullback
of the effective groupoid object to the cover object. -/
def effectiveComparison (F : FamilyGroupoid f U)
    (D : Datum ((Picard.relativeSpace f).map h) F.of.obj)
    {M : FamilyGroupoid f T} (E : Str D (𝟙 _) M.of.obj) :
    (pullback f h).obj M ⟶ F :=
  (homEquiv f U).symm (Modules.GeometricQuasicoherentDescent.pullbackIsoOfStr D E)

/-- The unique compatible module isomorphism is an actual arrow of the family
groupoid, and is unique among its compatible arrows. -/
lemma existsUnique_effective_iso [IsAffineHom h.left] [Flat h.left] [Surjective h.left]
    (F : FamilyGroupoid f U)
    (D : Datum ((Picard.relativeSpace f).map h) F.of.obj)
    {M N : FamilyGroupoid f T} (E : Str D (𝟙 _) M.of.obj)
    (E' : Str D (𝟙 _) N.of.obj) :
    ∃! a : M ⟶ N, Str.Hom E E' ((forget f T).map a) := by
  have := Picard.relativeSpace_map_isAffineHom f h
  have := Picard.relativeSpace_map_flat f h
  have := Picard.relativeSpace_map_surjective f h
  obtain ⟨e, he, hu⟩ := Modules.GeometricQuasicoherentDescent.existsUnique_iso D E E'
  refine ⟨(homEquiv f T).symm e, he, ?_⟩
  intro a ha
  apply (homEquiv f T).injective
  simpa only [Equiv.apply_symm_apply] using hu ((homEquiv f T) a) ha

end FamilyGroupoid

end Langlands.AlgebraicGeometry.CoherentSheaves
