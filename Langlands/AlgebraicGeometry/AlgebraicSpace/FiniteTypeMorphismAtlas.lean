import Langlands.AlgebraicGeometry.AlgebraicSpace.FinitePresentationChartSquares
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismBaseChange
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! # Compact atlases and finite type for morphisms of finitely presented spaces -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

namespace SchemePullbackChart

variable (f : X ⟶ Y) {U T : Over S}
    (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (g : (schemeYoneda S).obj T ⟶ Y.presheaf)

/-- The scheme representing the pullback of the composite source chart and a test map. -/
abbrev scheme : Over S := (Y.representable_from_scheme (a ≫ hom f)).pullback g

abbrev fst : scheme f a g ⟶ U :=
  Functor.relativelyRepresentable.fst' (Y.representable_from_scheme (a ≫ hom f)) g

abbrev snd : scheme f a g ⟶ T :=
  (Y.representable_from_scheme (a ≫ hom f)).snd g

theorem isPullback :
    IsPullback ((schemeYoneda S).map (fst f a g))
      ((schemeYoneda S).map (snd f a g)) (a ≫ hom f) g :=
  Functor.relativelyRepresentable.isPullback'
    (Y.representable_from_scheme (a ≫ hom f)) g

/-- The represented overlap is a scheme chart of the actual presheaf fibre product. -/
def atlas : (schemeYoneda S).obj (scheme f a g) ⟶ Limits.pullback (hom f) g :=
  (isPullback f a g).isoPullback.hom ≫
    pullback.map (a ≫ hom f) g (hom f) g a (𝟙 _) (𝟙 _) (by simp) (by simp)

local instance : (MorphismProperty.inverseImage (@Etale.{u})
    (Over.forget S)).IsStableUnderComposition := by
  have h : MorphismProperty.IsMultiplicative (@Etale.{u}) := inferInstance
  have : MorphismProperty.IsStableUnderComposition (@Etale.{u}) :=
    h.toIsStableUnderComposition
  exact MorphismProperty.IsStableUnderComposition.inverseImage
    (P := @Etale.{u}) (Over.forget S)

local instance : (MorphismProperty.inverseImage (@Surjective.{u})
    (Over.forget S)).IsStableUnderComposition := by
  have h : MorphismProperty.IsMultiplicative (@Surjective.{u}) := inferInstance
  have : MorphismProperty.IsStableUnderComposition (@Surjective.{u}) :=
    h.toIsStableUnderComposition
  exact MorphismProperty.IsStableUnderComposition.inverseImage
    (P := @Surjective.{u}) (Over.forget S)

theorem atlas_isEtale (ha : IsEtale a) : IsEtale (atlas f a g) := by
  have hi : IsEtale (𝟙 ((schemeYoneda S).obj T)) := by
    simpa using isEtale_map (𝟙 T) (by change Etale (𝟙 T.left); infer_instance)
  apply IsEtale.iso_comp (isPullback f a g).isoPullback
  exact MorphismProperty.pullbackMap
    (P := (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).relative
      (schemeYoneda S)) ha hi rfl rfl

theorem atlas_isSurjective (hs : IsSurjective a) : IsSurjective (atlas f a g) := by
  have hi : IsSurjective (𝟙 ((schemeYoneda S).obj T)) := by
    change (MorphismProperty.inverseImage (@Surjective.{u})
      (Over.forget S)).relative (schemeYoneda S) (𝟙 _)
    have : (MorphismProperty.inverseImage (@Surjective.{u})
        (Over.forget S)).IsStableUnderBaseChange := isStableUnderBaseChange_inverseImage_forget
    simpa using (MorphismProperty.relative_map
      (P := MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S))
      (F := schemeYoneda S) (f := 𝟙 T)
      (by change Surjective (𝟙 T.left); infer_instance))
  apply (MorphismProperty.cancel_left_of_respectsIso
    ((MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).relative
      (schemeYoneda S)) _ _).mpr
  exact MorphismProperty.pullbackMap
    (P := (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).relative
      (schemeYoneda S)) hs hi rfl rfl

/-- Quasi-separatedness of the target makes the represented overlap compact
when both chart schemes and the base are affine. -/
theorem compactSpace [IsAffine S] [IsAffine U.left] [IsAffine T.left]
    (hY : IsQuasiSeparated Y) : CompactSpace (scheme f a g).left := by
  have : IsAffine (U ⨯ T).left :=
    IsAffine.of_isIso (Over.prodLeftIsoPullback U T).hom
  have : QuasiCompact (prod.lift (fst f a g) (snd f a g)).left :=
    relative_diagonal_property_chart_pairing @QuasiCompact hY
      (fst f a g) (snd f a g) (a ≫ hom f) g (isPullback f a g)
  exact QuasiCompact.compactSpace_of_compactSpace
    (prod.lift (fst f a g) (snd f a g)).left

end SchemePullbackChart

/-- A compact structural atlas over an affine base and a quasi-separated target
make every morphism quasi-compact. -/
theorem isQuasiCompactMorphism_of_atlas [IsAffine S]
    (hX : HasAtlasProperty (@QuasiCompact.{u}) X)
    (hY : IsQuasiSeparated Y) (f : X ⟶ Y) : IsQuasiCompactMorphism f := by
  obtain ⟨U, a, ha, hs, hU⟩ := hX
  have : QuasiCompact U.hom := hU
  have : CompactSpace U.left := QuasiCompact.compactSpace_of_compactSpace U.hom
  obtain ⟨A, hA, p, hp, hps⟩ := exists_affine_etale_surjective_cover U.left
  let V : Over S := Over.mk (p ≫ U.hom)
  let j : V ⟶ U := Over.homMk p
  have hj : IsEtale ((schemeYoneda S).map j) := isEtale_map j hp
  have hjs : IsSurjective ((schemeYoneda S).map j) := by
    have : (MorphismProperty.inverseImage (@Surjective.{u})
        (Over.forget S)).IsStableUnderBaseChange := isStableUnderBaseChange_inverseImage_forget
    exact MorphismProperty.relative_map
      (P := MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)) hps
  let b := (schemeYoneda S).map j ≫ a
  have hb : IsEtale b := hj.comp ha
  have hbs : IsSurjective b := by
    have : (MorphismProperty.inverseImage (@Surjective.{u})
        (Over.forget S)).IsStableUnderComposition := by
      have h : MorphismProperty.IsMultiplicative (@Surjective.{u}) := inferInstance
      have : MorphismProperty.IsStableUnderComposition (@Surjective.{u}) :=
        h.toIsStableUnderComposition
      exact MorphismProperty.IsStableUnderComposition.inverseImage
        (P := @Surjective.{u}) (Over.forget S)
    exact MorphismProperty.comp_mem
      (W := (MorphismProperty.inverseImage (@Surjective.{u})
        (Over.forget S)).relative (schemeYoneda S)) _ _ hjs hs
  have : IsAffine V.left := hA
  intro T hT g
  have : IsAffine T.left := hT
  exact ⟨SchemePullbackChart.scheme f b g, SchemePullbackChart.atlas f b g,
    SchemePullbackChart.compactSpace f b g hY,
    SchemePullbackChart.atlas_isEtale f b g hb,
    SchemePullbackChart.atlas_isSurjective f b g hbs⟩

/-- The finite-presentation atlas hypotheses give the finite-type chart
required by the published morphism predicate. -/
theorem isLocallyOfFiniteTypeMorphism_of_finitePresentation_atlases [IsAffine S]
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (hY : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y)
    (hYqs : IsQuasiSeparated Y) (f : X ⟶ Y) : IsLocallyOfFiniteTypeMorphism f := by
  obtain ⟨U, V, a, b, φ, _, _, ha, hs, hb, _, hUl, _, hw⟩ :=
    exists_affine_finitePresentation_chart_square hX hY hYqs f
  have : LocallyOfFinitePresentation U.hom := hUl
  have : LocallyOfFiniteType (φ.left ≫ V.hom) := by
    rw [Over.w φ]
    infer_instance
  have hφ : LocallyOfFiniteType φ.left := locallyOfFiniteType_of_comp φ.left V.hom
  exact ⟨U, V, a, b, φ, ha, hs, hb, hφ, hw⟩

/-- Under the atlas hypotheses, properness has only separatedness and
universal closedness left to verify. -/
theorem isProperMorphism_iff_separated_universallyClosed [IsAffine S]
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (hY : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y)
    (hYqs : IsQuasiSeparated Y) (f : X ⟶ Y) :
    IsProperMorphism f ↔ IsSeparatedMorphism f ∧ IsUniversallyClosedMorphism f := by
  constructor
  · intro hf
    exact ⟨hf.1, hf.2.2.2⟩
  · rintro ⟨hs, hc⟩
    exact ⟨hs, isQuasiCompactMorphism_of_atlas
      (hX.mono (fun _ _ _ h => h.2)) hYqs f,
      isLocallyOfFiniteTypeMorphism_of_finitePresentation_atlases hX hY hYqs f, hc⟩

set_option backward.isDefEq.respectTransparency false in
/-- The same properness test applies at every affine scheme base change,
including every stage and the affine limit in the host theorem. -/
theorem isProperMorphism_baseChangeMap_iff_separated_universallyClosed
    {T : Scheme.{u}} [IsAffine T] (g : T ⟶ S)
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (hY : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y)
    (hYqs : IsQuasiSeparated Y) (f : X ⟶ Y) :
    IsProperMorphism (baseChangeMap g f) ↔
      IsSeparatedMorphism (baseChangeMap g f) ∧
        IsUniversallyClosedMorphism (baseChangeMap g f) :=
  isProperMorphism_iff_separated_universallyClosed
    (hX.baseChange (g := g)) (hY.baseChange (g := g)) (hYqs.baseChange (g := g)) _

end Langlands.AlgebraicGeometry.AlgebraicSpace
