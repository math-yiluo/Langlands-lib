/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphPresentation
public import WeilConjectures.AlgebraicGeometry.SfGraphCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.SfGraphProjectionWord
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.SfEtaleAmbientAdjointProjection
import WeilConjectures.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransfer
import WeilConjectures.CategoryTheory.CompactGenerationEquivalence
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import WeilConjectures.CategoryTheory.TriangulatedEquivalenceTransfer
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-! # Projection maps on proper/open/proper graph words

Source: `LowerShriekComposition.lean`, the graph construction of
`nonempty_iso_rightDerivedLowerShriek_comp`, and Stacks Tags 0B56, 0GL1 and 0F7B.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Successive proper, open and proper projection, with the canonical composite
pullback comparison. Source: Stacks Tags 0B56, 0GL1 and 0F7B;
node lem-sf-etale-compact-projection-coherence, steps 4--5
(auxiliary; not a blueprint node). -/
def sfGraphWordProjection
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (t : EtaleGraphPresentation f)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj ((t.functor A).obj M)).obj K ⟶
      (t.functor A).obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)) := by
  exact sfGraphProjectionWord (ModuleCat.{u + 1} A) t.a t.e t.p f t.fac M K

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The compactification projection with its tensor endpoints displayed once.
Source: `LowerShriekProjection.lean`, projectionMapOfCompactification
(auxiliary; not a blueprint node). -/
def sfCompactProjection
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M)).obj K ⟶
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)) :=
  ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K

theorem sfCompactProjection_eq
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    sfCompactProjection A c M K =
      ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K := rfl

instance sfCompactProjection_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    IsIso (sfCompactProjection A c M K) := by
  rw [sfCompactProjection_eq]
  exact (sfEtaleAmbientAdjointProjection A c).2 M K

/-- The original graph comparison, with the presentation functor as its target.
Source: `SfGraphCompactSupportComposition.lean`, explicit graph comparison
(auxiliary; not a blueprint node). -/
def sfGraphPresentationComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (t : EtaleGraphPresentation f) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅ t.functor A :=
  sfGraphCompactificationComparison A c t.p t.e t.a t.fac

/-- The first graph word used by the specified composition comparison.
Source: `LowerShriekComposition.lean`, graph construction, first side e1
(auxiliary; not a blueprint node). -/
def sfCompositionGraphPresentation
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cg : Compactification g) (ch : Compactification (f ≫ g)) :
    EtaleGraphPresentation (f ≫ g) := by
  -- `P = V ×_T W`
  let φ := pullback.fst ch.g cg.g
  let ψ := pullback.snd ch.g cg.g
  have : IsProper φ := MorphismProperty.pullback_fst _ _ cg.isProper
  have : IsProper ψ := MorphismProperty.pullback_snd _ _ ch.isProper
  -- `X` in the open `P ×_V X` of `P`
  let e := pullback.fst φ ch.i
  let σ := pullback.snd φ ch.i
  have : IsSeparated σ := MorphismProperty.pullback_snd _ _ inferInstance
  have w₁ : ch.i ≫ ch.g = (f ≫ cg.i) ≫ cg.g := by
    rw [← ch.comm, Category.assoc, ← cg.comm]
  let h : X ⟶ pullback φ ch.i :=
    pullback.lift (pullback.lift ch.i (f ≫ cg.i) w₁) (𝟙 X) (by simp [φ])
  have : IsProper (h ≫ σ) := by rw [show h ≫ σ = 𝟙 X from pullback.lift_snd _ _ _]
                                infer_instance
  have : IsProper h := IsProper.of_comp h σ
  have he : h ≫ e = pullback.lift ch.i (f ≫ cg.i) w₁ := pullback.lift_fst _ _ _
  exact {
    U := pullback φ ch.i
    P := pullback ch.g cg.g
    a := h
    e := e
    p := ψ ≫ cg.g
    fac := by
      rw [reassoc_of% he, pullback.lift_snd_assoc, Category.assoc, ← cg.comm] }

/-- The remaining graph word: lift the proper graph through the further open,
compose open extensions, interchange proper and open, and undo the comparison for f.
Source: `LowerShriekComposition.lean`, graph construction, e3 followed by inverse e2
(auxiliary; not a blueprint node). -/
def sfGraphCompositionTailIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f) (cg : Compactification g)
    (ch : Compactification (f ≫ g)) :
    (sfCompositionGraphPresentation f g cg ch).functor A ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg := by
  let 𝔸 := ModuleCat.{u + 1} A
  -- `P = V ×_T W`
  let φ := pullback.fst ch.g cg.g
  let ψ := pullback.snd ch.g cg.g
  have : IsProper φ := MorphismProperty.pullback_fst _ _ cg.isProper
  have : IsProper ψ := MorphismProperty.pullback_snd _ _ ch.isProper
  -- `X` in the open `P ×_V X` of `P`
  let e := pullback.fst φ ch.i
  let σ := pullback.snd φ ch.i
  have : IsSeparated σ := MorphismProperty.pullback_snd _ _ inferInstance
  have w₁ : ch.i ≫ ch.g = (f ≫ cg.i) ≫ cg.g := by
    rw [← ch.comm, Category.assoc, ← cg.comm]
  let h : X ⟶ pullback φ ch.i :=
    pullback.lift (pullback.lift ch.i (f ≫ cg.i) w₁) (𝟙 X) (by simp [φ])
  have : IsProper (h ≫ σ) := by rw [show h ≫ σ = 𝟙 X from pullback.lift_snd _ _ _]
                                infer_instance
  have : IsProper h := IsProper.of_comp h σ
  have he : h ≫ e = pullback.lift ch.i (f ≫ cg.i) w₁ := pullback.lift_fst _ _ _
  -- `P ×_W Y`, open in `P` and proper over `Y`
  let eY := pullback.fst ψ cg.i
  let πY := pullback.snd ψ cg.i
  have : IsProper πY := MorphismProperty.pullback_snd _ _ inferInstance
  let uY := pullback.fst e eY
  let e' := pullback.snd e eY
  let ρ : X ⟶ pullback ψ cg.i := pullback.lift (h ≫ e) f (by rw [he]; simp [ψ])
  let h' : X ⟶ pullback e eY := pullback.lift h ρ (by simp [ρ, eY])
  have : IsProper (h' ≫ uY) := by rw [show h' ≫ uY = h from pullback.lift_fst _ _ _]
                                  infer_instance
  have : IsProper h' := IsProper.of_comp h' uY
  let e₂ := sfGraphCompactificationComparison A cf πY e' h'
    (by simp [h', e', ρ, πY])
  let eh : R((h')_*[𝔸]) ⋙ D((uY)_!open[𝔸]) ≅ R((h)_*[𝔸]) :=
    rightDerivedLowerStarCompOpenImmersionLowerShriekIso A h' uY h (pullback.lift_fst _ _ _)
  let ex : R((πY)_*[𝔸]) ⋙ D((cg.i)_!open[𝔸]) ≅ D((eY)_!open[𝔸]) ⋙ R((ψ)_*[𝔸]) :=
    openImmersionLowerShriekLowerStarExchangeIso A (IsPullback.of_hasPullback ψ cg.i).flip
  let e₃ : R((h)_*[𝔸]) ⋙ D((e)_!open[𝔸]) ⋙ R((ψ ≫ cg.g)_*[𝔸]) ≅
      (R((h')_*[𝔸]) ⋙ D((e')_!open[𝔸]) ⋙ R((πY)_*[𝔸])) ⋙ D((cg.i)_!open[𝔸]) ⋙
        R((cg.g)_*[𝔸]) :=
    Functor.isoWhiskerRight eh.symm _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          ((mapDerivedCategoryOpenImmersionLowerShriekComp 𝔸 uY e).symm ≪≫
            mapDerivedCategoryOpenImmersionLowerShriekCongr 𝔸 pullback.condition ≪≫
            mapDerivedCategoryOpenImmersionLowerShriekComp 𝔸 e' eY) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
            (rightDerivedLowerStarCompOfEq 𝔸 ψ cg.g _ rfl).symm ≪≫
          (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight ex.symm _ ≪≫
          Functor.associator _ _ _)) ≪≫
      Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.associator _ _ _) _ ≪≫
      Functor.associator _ _ _
  exact e₃ ≪≫ Functor.isoWhiskerRight e₂.symm _

/-- The specified graph compositor factors through its first graph word.
Source: `SfGraphCompactSupportComposition.lean`, defining equation
(auxiliary; not a blueprint node). -/
theorem sfGraphCompactSupportCompIso_factor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f) (cg : Compactification g)
    (ch : Compactification (f ≫ g)) :
    sfGraphCompactSupportCompIso A f g cf cg ch =
      sfGraphPresentationComparison A ch (sfCompositionGraphPresentation f g cg ch) ≪≫
      sfGraphCompositionTailIso A f g cf cg ch := by
  rfl

end AlgebraicGeometry.Etale
