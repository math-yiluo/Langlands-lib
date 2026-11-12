import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismProperties
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! # Common étale chart squares and smooth morphisms of algebraic spaces -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A commuting scheme-chart square for a morphism, with both charts étale.
Surjectivity of the source chart is a separate condition. -/
structure EtaleMorphismChart (f : X ⟶ Y) where
  source : Over S
  target : Over S
  sourceMap : (schemeYoneda S).obj source ⟶ X.presheaf
  targetMap : (schemeYoneda S).obj target ⟶ Y.presheaf
  schemeMap : source ⟶ target
  sourceEtale : IsEtale sourceMap
  targetEtale : IsEtale targetMap
  comm : sourceMap ≫ hom f = (schemeYoneda S).map schemeMap ≫ targetMap

namespace EtaleMorphismChart

variable {f : X ⟶ Y} (c d : EtaleMorphismChart f)

/-- Common represented source of two étale chart squares. -/
abbrev sourceOverlap : Over S := c.sourceEtale.representable.pullback d.sourceMap

abbrev sourceFst : sourceOverlap c d ⟶ c.source :=
  Functor.relativelyRepresentable.fst' c.sourceEtale.representable d.sourceMap

abbrev sourceSnd : sourceOverlap c d ⟶ d.source :=
  c.sourceEtale.representable.snd d.sourceMap

theorem source_isPullback :
    IsPullback ((schemeYoneda S).map (sourceFst c d))
      ((schemeYoneda S).map (sourceSnd c d)) c.sourceMap d.sourceMap :=
  Functor.relativelyRepresentable.isPullback' c.sourceEtale.representable d.sourceMap

/-- Common represented target of two étale chart squares. -/
abbrev targetOverlap : Over S := c.targetEtale.representable.pullback d.targetMap

abbrev targetFst : targetOverlap c d ⟶ c.target :=
  Functor.relativelyRepresentable.fst' c.targetEtale.representable d.targetMap

abbrev targetSnd : targetOverlap c d ⟶ d.target :=
  c.targetEtale.representable.snd d.targetMap

theorem target_isPullback :
    IsPullback ((schemeYoneda S).map (targetFst c d))
      ((schemeYoneda S).map (targetSnd c d)) c.targetMap d.targetMap :=
  Functor.relativelyRepresentable.isPullback' c.targetEtale.representable d.targetMap

/-- The induced scheme map from the common source to the common target. -/
def comparison : sourceOverlap c d ⟶ targetOverlap c d :=
  (schemeYoneda S).preimage ((target_isPullback c d).lift
    ((schemeYoneda S).map (sourceFst c d ≫ c.schemeMap))
    ((schemeYoneda S).map (sourceSnd c d ≫ d.schemeMap)) (by
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
        ← c.comm, ← d.comm, ← Category.assoc, (source_isPullback c d).w, Category.assoc]))

theorem comparison_fst : comparison c d ≫ targetFst c d = sourceFst c d ≫ c.schemeMap := by
  apply (schemeYoneda S).map_injective
  rw [Functor.map_comp, comparison, Functor.map_preimage]
  exact (target_isPullback c d).lift_fst _ _ _

theorem comparison_snd : comparison c d ≫ targetSnd c d = sourceSnd c d ≫ d.schemeMap := by
  apply (schemeYoneda S).map_injective
  rw [Functor.map_comp, comparison, Functor.map_preimage]
  exact (target_isPullback c d).lift_snd _ _ _

/-- A property propagates from a witnessing chart to any other chart if it
composes with étale maps, cancels an étale target map, and descends through a
surjective étale source map. -/
theorem property_of_chart (P : MorphismProperty Scheme.{u})
    (hleft : ∀ {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C),
      Etale a → P b → P (a ≫ b))
    (hright : ∀ {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C),
      P a → Etale b → P (a ≫ b))
    (hcancel : ∀ {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C),
      Etale b → P (a ≫ b) → P a)
    (hdesc : ∀ {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C),
      Etale a → Surjective a → P (a ≫ b) → P b)
    (hc : IsSurjective c.sourceMap) (hP : P c.schemeMap.left) : P d.schemeMap.left := by
  have hq : Etale (sourceFst c d).left :=
    d.sourceEtale.projection c.sourceMap _ _ (source_isPullback c d).flip
  have hp : Etale (sourceSnd c d).left :=
    c.sourceEtale.projection d.sourceMap _ _ (source_isPullback c d)
  have hps : Surjective (sourceSnd c d).left :=
    hc.projection d.sourceMap _ _ (source_isPullback c d)
  have hr : Etale (targetFst c d).left :=
    d.targetEtale.projection c.targetMap _ _ (target_isPullback c d).flip
  have hs : Etale (targetSnd c d).left :=
    c.targetEtale.projection d.targetMap _ _ (target_isPullback c d)
  have htr : P ((comparison c d).left ≫ (targetFst c d).left) := by
    change P (comparison c d ≫ targetFst c d).left
    rw [comparison_fst]
    exact hleft _ _ hq hP
  have ht : P (comparison c d).left := hcancel _ _ hr htr
  have hpsd : P ((sourceSnd c d).left ≫ d.schemeMap.left) := by
    change P (sourceSnd c d ≫ d.schemeMap).left
    rw [← comparison_snd]
    exact hright _ _ ht hs
  exact hdesc _ _ hp hps hpsd

end EtaleMorphismChart

set_option backward.isDefEq.respectTransparency.types false in
/-- Smoothness of a composite cancels an étale second morphism. -/
theorem smooth_of_comp_etale {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W)
    [Etale g] [Smooth (f ≫ g)] : Smooth f := by
  let : MorphismProperty.IsMultiplicative (@Smooth.{u}) :=
    { id_mem := fun _ => by infer_instance
      comp_mem := fun a b ha hb => by let := ha; let := hb; infer_instance }
  have h : MorphismProperty.HasOfPostcompProperty (@Smooth.{u}) (@Etale.{u}) := by
    rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
    intro A B φ hφ
    let := hφ
    change Smooth (pullback.diagonal φ)
    infer_instance
  exact h.of_postcomp f g inferInstance inferInstance

/-- A smooth morphism of spaces is smooth on every commuting étale chart square.
The tested source chart need not be surjective. -/
theorem IsSmoothMorphism.smooth_chart {f : X ⟶ Y} (hf : IsSmoothMorphism f)
    {U V : Over S} (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (b : (schemeYoneda S).obj V ⟶ Y.presheaf) (φ : U ⟶ V)
    (ha : IsEtale a) (hb : IsEtale b)
    (hw : a ≫ hom f = (schemeYoneda S).map φ ≫ b) : Smooth φ.left := by
  obtain ⟨A, B, x, y, ψ, hx, hs, hy, hψ, hcomm⟩ := hf
  let c : EtaleMorphismChart f := ⟨A, B, x, y, ψ, hx, hy, hcomm⟩
  let d : EtaleMorphismChart f := ⟨U, V, a, b, φ, ha, hb, hw⟩
  exact c.property_of_chart d @Smooth
    (fun q r hq hr => by let := hq; let := hr; infer_instance)
    (fun q r hq hr => by let := hq; let := hr; infer_instance)
    (fun q r hr hqr => by let := hr; let := hqr; exact smooth_of_comp_etale q r)
    (fun q r hq hsq hqr =>
      Langlands.AlgebraicGeometry.smoothEtaleSourceDescent _ _ _ q r hq hsq hqr)
    hs hψ

/-- A commuting étale chart square with surjective source tests smoothness exactly. -/
theorem isSmoothMorphism_iff_smooth_chart {f : X ⟶ Y}
    {U V : Over S} (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (b : (schemeYoneda S).obj V ⟶ Y.presheaf) (φ : U ⟶ V)
    (ha : IsEtale a) (hs : IsSurjective a) (hb : IsEtale b)
    (hw : a ≫ hom f = (schemeYoneda S).map φ ≫ b) :
    IsSmoothMorphism f ↔ Smooth φ.left :=
  ⟨fun hf => hf.smooth_chart a b φ ha hb hw,
    fun hφ => ⟨U, V, a, b, φ, ha, hs, hb, hφ, hw⟩⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
