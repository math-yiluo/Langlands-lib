import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorImages
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Open images of flat morphisms locally of finite presentation -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.LocallyQuasiFiniteDescent

open AlgebraicSpace AlgebraicSpace.OpenSubfunctorImages

variable {S : Scheme.{u}}

/-- Flat morphisms locally of finite presentation, as a property of morphisms of schemes. -/
abbrev flatLFPScheme : MorphismProperty Scheme.{u} :=
  (@Flat : MorphismProperty Scheme.{u}) ⊓ (@LocallyOfFinitePresentation : MorphismProperty _)

instance flatLFPScheme_isStableUnderBaseChange :
    flatLFPScheme.{u}.IsStableUnderBaseChange := by
  have : MorphismProperty.IsStableUnderBaseChange (@Flat : MorphismProperty Scheme.{u}) :=
    inferInstance
  have : MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) := inferInstance
  exact MorphismProperty.IsStableUnderBaseChange.inf

instance flatLFPScheme_isStableUnderComposition :
    flatLFPScheme.{u}.IsStableUnderComposition := by
  have : MorphismProperty.IsStableUnderComposition (@Flat : MorphismProperty Scheme.{u}) :=
    inferInstance
  have : MorphismProperty.IsStableUnderComposition
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) := inferInstance
  exact MorphismProperty.IsStableUnderComposition.inf

/-- Flat morphisms locally of finite presentation, as morphisms of schemes over `S`. -/
abbrev flatLFP (S : Scheme.{u}) : MorphismProperty (Over S) :=
  MorphismProperty.inverseImage flatLFPScheme.{u} (Over.forget S)

instance flatLFP_isStableUnderBaseChange : (flatLFP S).IsStableUnderBaseChange where
  of_isPullback sq hg :=
    MorphismProperty.of_isPullback (P := flatLFPScheme.{u}) (sq.map (Over.forget S)) hg

instance flatLFP_respectsIso : (flatLFP S).RespectsIso :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

instance flatLFP_isStableUnderComposition : (flatLFP S).IsStableUnderComposition :=
  MorphismProperty.IsStableUnderComposition.inverseImage (P := flatLFPScheme.{u})
    (Over.forget S)

/-- The functor of points of a flat morphism locally of finite presentation is flat and
locally of finite presentation relative to schemes. -/
theorem flatLFP_relative_map {X Y : Over S} (f : X ⟶ Y) [Flat f.left]
    [LocallyOfFinitePresentation f.left] :
    (flatLFP S).relative (schemeYoneda S) ((schemeYoneda S).map f) :=
  MorphismProperty.relative_map (P := flatLFP S) ⟨inferInstanceAs (Flat f.left),
    inferInstanceAs (LocallyOfFinitePresentation f.left)⟩

/-- The topological image of a flat morphism locally of finite presentation, viewed as an
open. -/
def flatImageOpen {R T : Over S} (p : R ⟶ T) [Flat p.left]
    [LocallyOfFinitePresentation p.left] : T.left.Opens :=
  ⟨Set.range p.left, p.left.isOpenMap.isOpen_range⟩

/-- The open image scheme, with its structure map to the base. -/
def flatImage {R T : Over S} (p : R ⟶ T) [Flat p.left]
    [LocallyOfFinitePresentation p.left] : Over S :=
  Over.mk ((flatImageOpen p).ι ≫ T.hom)

/-- The inclusion of the open image into the target. -/
def flatImageι {R T : Over S} (p : R ⟶ T) [Flat p.left]
    [LocallyOfFinitePresentation p.left] : flatImage p ⟶ T :=
  Over.homMk (flatImageOpen p).ι

instance flatImageι_isOpenImmersion {R T : Over S} (p : R ⟶ T) [Flat p.left]
    [LocallyOfFinitePresentation p.left] :
    _root_.AlgebraicGeometry.IsOpenImmersion (flatImageι p).left :=
  inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion (flatImageOpen p).ι)

theorem range_flatImageι {R T : Over S} (p : R ⟶ T) [Flat p.left]
    [LocallyOfFinitePresentation p.left] :
    Set.range (flatImageι p).left = Set.range p.left :=
  Scheme.Opens.range_ι (flatImageOpen p)

/-- The factorization of a flat morphism locally of finite presentation through its open
image. -/
def toFlatImage {R T : Over S} (p : R ⟶ T) [Flat p.left]
    [LocallyOfFinitePresentation p.left] : R ⟶ flatImage p :=
  (OpenSubfunctorLifting.factors_through_open_iff (flatImageι p) p).mpr
    (range_flatImageι p).ge |>.choose

@[reassoc (attr := simp)]
theorem toFlatImage_fac {R T : Over S} (p : R ⟶ T) [Flat p.left]
    [LocallyOfFinitePresentation p.left] : toFlatImage p ≫ flatImageι p = p :=
  (OpenSubfunctorLifting.factors_through_open_iff (flatImageι p) p).mpr
    (range_flatImageι p).ge |>.choose_spec

instance toFlatImage_flat {R T : Over S} (p : R ⟶ T) [Flat p.left]
    [LocallyOfFinitePresentation p.left] : Flat (toFlatImage p).left := by
  have : MorphismProperty.HasOfPostcompProperty @Flat
      (MorphismProperty.monomorphisms Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.hasOfPostcompProperty_monomorphisms
  refine MorphismProperty.of_postcomp (W' := MorphismProperty.monomorphisms _) (W := @Flat)
    (toFlatImage p).left (flatImageι p).left (inferInstanceAs (Mono (flatImageι p).left)) ?_
  rw [← Over.comp_left, toFlatImage_fac]
  infer_instance

instance toFlatImage_locallyOfFinitePresentation {R T : Over S} (p : R ⟶ T) [Flat p.left]
    [LocallyOfFinitePresentation p.left] :
    LocallyOfFinitePresentation (toFlatImage p).left := by
  have : MorphismProperty.HasOfPostcompProperty @LocallyOfFinitePresentation
      (MorphismProperty.monomorphisms Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.hasOfPostcompProperty_monomorphisms
  refine MorphismProperty.of_postcomp (W' := MorphismProperty.monomorphisms _)
    (W := @LocallyOfFinitePresentation) (toFlatImage p).left (flatImageι p).left
    (inferInstanceAs (Mono (flatImageι p).left)) ?_
  rw [← Over.comp_left, toFlatImage_fac]
  infer_instance

instance toFlatImage_surjective {R T : Over S} (p : R ⟶ T) [Flat p.left]
    [LocallyOfFinitePresentation p.left] : Surjective (toFlatImage p).left := by
  constructor
  intro y
  obtain ⟨x, hx⟩ := y.property
  refine ⟨x, (flatImageι p).left.isOpenEmbedding.injective ?_⟩
  change ((toFlatImage p).left ≫ (flatImageι p).left) x = y.val
  rw [← Over.comp_left, toFlatImage_fac]
  exact hx

/-- The fppf sheafified image of a flat scheme morphism locally of finite presentation is
represented by its open image. -/
theorem sheafify_range_schemeYoneda_map_of_flat {R T : Over S} (p : R ⟶ T) [Flat p.left]
    [LocallyOfFinitePresentation p.left] :
    (Subfunctor.range ((schemeYoneda S).map p)).sheafify (fppfTopology S) =
      Subfunctor.range ((schemeYoneda S).map (flatImageι p)) := by
  have hmap : (schemeYoneda S).map (toFlatImage p) ≫
      (schemeYoneda S).map (flatImageι p) = (schemeYoneda S).map p := by
    rw [← Functor.map_comp, toFlatImage_fac]
  rw [← hmap]
  exact sheafify_range_comp _ _
    (isLocallySurjective_schemeYoneda_map (toFlatImage p))
    (AffineOpenSubfunctors.isOpenImmersion_schemeYoneda_map _ inferInstance)

variable {F G : Presheaf S}

/-- The preimage of the sheafified image of `a` along a test map `g` is represented by the
open image of any represented base change of `a` along `g`. -/
theorem preimage_sheafify_range_eq {a : G ⟶ F} {T P : Over S}
    (g : (schemeYoneda S).obj T ⟶ F) {k : (schemeYoneda S).obj P ⟶ G} (p : P ⟶ T)
    [Flat p.left] [LocallyOfFinitePresentation p.left]
    (sq : IsPullback k ((schemeYoneda S).map p) a g) :
    Subfunctor.range ((schemeYoneda S).map (flatImageι p)) =
      ((Subfunctor.range a).sheafify (fppfTopology S)).preimage g := by
  rw [← sheafify_preimage, ← OpenSubfunctorLifting.range_eq_preimage_of_isPullback sq]
  exact (sheafify_range_schemeYoneda_map_of_flat p).symm

/-- The comparison map from the open image to the sheafified image. -/
def toSheafifyRange {a : G ⟶ F} {T P : Over S}
    (g : (schemeYoneda S).obj T ⟶ F) {k : (schemeYoneda S).obj P ⟶ G} (p : P ⟶ T)
    [Flat p.left] [LocallyOfFinitePresentation p.left]
    (sq : IsPullback k ((schemeYoneda S).map p) a g) :
    (schemeYoneda S).obj (flatImage p) ⟶
      ((Subfunctor.range a).sheafify (fppfTopology S)).toFunctor :=
  Subfunctor.lift ((schemeYoneda S).map (flatImageι p) ≫ g) (by
    rintro U x ⟨z, rfl⟩
    change ((schemeYoneda S).map (flatImageι p)).app U z ∈
      (((Subfunctor.range a).sheafify (fppfTopology S)).preimage g).obj U
    rw [← preimage_sheafify_range_eq g p sq]
    exact ⟨z, rfl⟩)

@[reassoc (attr := simp)]
theorem toSheafifyRange_ι {a : G ⟶ F} {T P : Over S}
    (g : (schemeYoneda S).obj T ⟶ F) {k : (schemeYoneda S).obj P ⟶ G} (p : P ⟶ T)
    [Flat p.left] [LocallyOfFinitePresentation p.left]
    (sq : IsPullback k ((schemeYoneda S).map p) a g) :
    toSheafifyRange g p sq ≫ ((Subfunctor.range a).sheafify (fppfTopology S)).ι =
      (schemeYoneda S).map (flatImageι p) ≫ g :=
  Subfunctor.lift_ι _ _

/-- The base change of the sheafified image of `a` along a test map `g` is the open image of
a represented base change of `a` along `g`. -/
theorem isPullback_toSheafifyRange {a : G ⟶ F} {T P : Over S}
    (g : (schemeYoneda S).obj T ⟶ F) {k : (schemeYoneda S).obj P ⟶ G} (p : P ⟶ T)
    [Flat p.left] [LocallyOfFinitePresentation p.left]
    (sq : IsPullback k ((schemeYoneda S).map p) a g) :
    IsPullback (toSheafifyRange g p sq) ((schemeYoneda S).map (flatImageι p))
      ((Subfunctor.range a).sheafify (fppfTopology S)).ι g := by
  have : Mono (flatImageι p) := Over.mono_of_mono_left _
  exact OpenSubfunctorLifting.isPullback_subfunctor_of_range _ _ _ g
    (toSheafifyRange_ι g p sq) (preimage_sheafify_range_eq g p sq)

/-- The fppf sheafified image of a presheaf map that is flat and locally of finite
presentation relative to schemes is a representable open subfunctor of its target. -/
theorem sheafify_range_open_of_flat (a : G ⟶ F)
    (ha : (flatLFP S).relative (schemeYoneda S) a) :
    IsOpenImmersion ((Subfunctor.range a).sheafify (fppfTopology S)).ι := by
  apply MorphismProperty.relative.of_exists
  intro T g
  have hp := ha.property_snd g
  have : Flat (ha.rep.snd g).left := hp.1
  have : LocallyOfFinitePresentation (ha.rep.snd g).left := hp.2
  exact ⟨flatImage (ha.rep.snd g), toSheafifyRange g _ (ha.rep.isPullback g),
    flatImageι (ha.rep.snd g), isPullback_toSheafifyRange g _ (ha.rep.isPullback g),
    inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion (flatImageι _).left)⟩

end Langlands.AlgebraicGeometry.LocallyQuasiFiniteDescent
