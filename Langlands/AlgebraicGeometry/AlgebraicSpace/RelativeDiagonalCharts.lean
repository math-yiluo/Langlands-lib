import Langlands.AlgebraicGeometry.AlgebraicSpace.RepresentedAtlasProperty
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismProperties
import Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent

/-! # Scheme charts of relative diagonals -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

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

/-- The kernel pair of a morphism embeds into the product of its source. -/
def relativeDiagonalTargetMap {F G : Presheaf S} (f : F ⟶ G) :
    Limits.pullback f f ⟶ F ⨯ F :=
  prod.lift (pullback.fst f f) (pullback.snd f f)

instance {F G : Presheaf S} (f : F ⟶ G) : Mono (relativeDiagonalTargetMap f) := by
  constructor
  intro T g h w
  apply pullback.hom_ext
  · simpa [relativeDiagonalTargetMap] using congrArg (fun k => k ≫ prod.fst) w
  · simpa [relativeDiagonalTargetMap] using congrArg (fun k => k ≫ prod.snd) w

/-- The absolute diagonal factors through the relative diagonal. -/
theorem relativeDiagonalTargetMap_fac {F G : Presheaf S} (f : F ⟶ G) :
    pullback.diagonal f ≫ relativeDiagonalTargetMap f = diag F := by
  apply prod.hom_ext <;> simp [relativeDiagonalTargetMap]

/-- Every morphism of algebraic spaces has a representable relative diagonal. -/
theorem relative_diagonal_representable (f : X ⟶ Y) :
    IsRepresentableMorphism (pullback.diagonal (hom f)) := by
  apply (schemeYoneda S).relativelyRepresentable.of_postcomp
    (W' := MorphismProperty.monomorphisms (Presheaf S))
    (pullback.diagonal (hom f)) (relativeDiagonalTargetMap (hom f)) (by infer_instance)
  rw [relativeDiagonalTargetMap_fac]
  exact X.hasRepresentableDiagonal

namespace RelativeDiagonalChart

variable (f : X ⟶ Y) {U : Over S} (a : (schemeYoneda S).obj U ⟶ X.presheaf)

/-- The represented kernel pair of the source chart. -/
abbrev source : Over S := (X.representable_from_scheme a).pullback a

/-- The represented kernel pair of the composite chart into the target. -/
abbrev target : Over S :=
  (Y.representable_from_scheme (a ≫ hom f)).pullback (a ≫ hom f)

abbrev sourceFst : source a ⟶ U :=
  Functor.relativelyRepresentable.fst' (X.representable_from_scheme a) a

abbrev sourceSnd : source a ⟶ U := (X.representable_from_scheme a).snd a

abbrev targetFst : target f a ⟶ U :=
  Functor.relativelyRepresentable.fst'
    (Y.representable_from_scheme (a ≫ hom f)) (a ≫ hom f)

abbrev targetSnd : target f a ⟶ U :=
  (Y.representable_from_scheme (a ≫ hom f)).snd (a ≫ hom f)

theorem source_isPullback :
    IsPullback ((schemeYoneda S).map (sourceFst a))
      ((schemeYoneda S).map (sourceSnd a)) a a :=
  Functor.relativelyRepresentable.isPullback' (X.representable_from_scheme a) a

theorem target_isPullback :
    IsPullback ((schemeYoneda S).map (targetFst f a))
      ((schemeYoneda S).map (targetSnd f a)) (a ≫ hom f) (a ≫ hom f) :=
  Functor.relativelyRepresentable.isPullback'
    (Y.representable_from_scheme (a ≫ hom f)) (a ≫ hom f)

/-- The map of represented kernel pairs induced by a morphism of spaces. -/
def comparison : source a ⟶ target f a :=
  Functor.relativelyRepresentable.lift'
    (Y.representable_from_scheme (a ≫ hom f))
    (sourceFst a) (sourceSnd a) (by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ hom f)
        (source_isPullback a).w)

@[reassoc (attr := simp)]
theorem comparison_fst : comparison f a ≫ targetFst f a = sourceFst a :=
  Functor.relativelyRepresentable.lift'_fst _ _ _ _

@[reassoc (attr := simp)]
theorem comparison_snd : comparison f a ≫ targetSnd f a = sourceSnd a :=
  Functor.relativelyRepresentable.lift'_snd _ _ _ _

/-- The target kernel pair maps to the target of the relative diagonal. -/
def atlas : (schemeYoneda S).obj (target f a) ⟶
    Limits.pullback (hom f) (hom f) :=
  pullback.lift ((schemeYoneda S).map (targetFst f a) ≫ a)
    ((schemeYoneda S).map (targetSnd f a) ≫ a) (by
      simpa only [Category.assoc] using (target_isPullback f a).w)

@[reassoc (attr := simp)]
theorem atlas_fst :
    atlas f a ≫ pullback.fst (hom f) (hom f) =
      (schemeYoneda S).map (targetFst f a) ≫ a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem atlas_snd :
    atlas f a ≫ pullback.snd (hom f) (hom f) =
      (schemeYoneda S).map (targetSnd f a) ≫ a :=
  pullback.lift_snd _ _ _

theorem atlas_eq :
    atlas f a = (target_isPullback f a).isoPullback.hom ≫
      pullback.map (a ≫ hom f) (a ≫ hom f) (hom f) (hom f) a a (𝟙 _)
        (by simp) (by simp) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.map, pullback.lift_fst,
      IsPullback.isoPullback_hom_fst_assoc,
      atlas_fst]
  · simp only [Category.assoc, pullback.map, pullback.lift_snd,
      IsPullback.isoPullback_hom_snd_assoc,
      atlas_snd]

/-- The target kernel pair of an étale source chart is an étale chart
of the target of the relative diagonal. -/
theorem atlas_isEtale (ha : IsEtale a) : IsEtale (atlas f a) := by
  rw [atlas_eq]
  apply IsEtale.iso_comp (target_isPullback f a).isoPullback
  exact MorphismProperty.pullbackMap
    (P := (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).relative
      (schemeYoneda S)) ha ha rfl rfl

/-- Surjectivity of the source chart gives surjectivity of the diagonal-target chart. -/
theorem atlas_isSurjective (hs : IsSurjective a) : IsSurjective (atlas f a) := by
  rw [atlas_eq]
  apply (MorphismProperty.cancel_left_of_respectsIso
    ((MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).relative
      (schemeYoneda S)) _ _).mpr
  exact MorphismProperty.pullbackMap
    (P := (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).relative
      (schemeYoneda S)) hs hs rfl rfl

/-- The map of represented kernel pairs is the pullback of the relative diagonal. -/
theorem comparison_isPullback :
    IsPullback ((schemeYoneda S).map (sourceFst a) ≫ a)
      ((schemeYoneda S).map (comparison f a)) (pullback.diagonal (hom f)) (atlas f a) := by
  have hw : ((schemeYoneda S).map (sourceFst a) ≫ a) ≫ pullback.diagonal (hom f) =
      (schemeYoneda S).map (comparison f a) ≫ atlas f a := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, atlas_fst]
      rw [← Category.assoc, ← Functor.map_comp, comparison_fst]
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, atlas_snd]
      rw [← Category.assoc, ← Functor.map_comp, comparison_snd]
      exact (source_isPullback a).w
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ hw)
  refine PullbackCone.IsLimit.mk _
    (fun s => (source_isPullback a).lift
      (s.snd ≫ (schemeYoneda S).map (targetFst f a))
      (s.snd ≫ (schemeYoneda S).map (targetSnd f a)) ?_) ?_ ?_ ?_
  · have h₁ := congrArg (fun k => k ≫ pullback.fst (hom f) (hom f)) s.condition
    have h₂ := congrArg (fun k => k ≫ pullback.snd (hom f) (hom f)) s.condition
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd,
      Category.comp_id, atlas_fst, atlas_snd] at h₁ h₂
    exact h₁.symm.trans h₂
  · intro s
    rw [← Category.assoc, IsPullback.lift_fst, Category.assoc]
    have h := congrArg (fun k => k ≫ pullback.fst (hom f) (hom f)) s.condition
    simpa using h.symm
  · intro s
    apply (target_isPullback f a).hom_ext
    · simp only [Category.assoc, ← Functor.map_comp, comparison_fst, IsPullback.lift_fst]
    · simp only [Category.assoc, ← Functor.map_comp, comparison_snd, IsPullback.lift_snd]
  · intro s m hm₁ hm₂
    apply (source_isPullback a).hom_ext
    · rw [IsPullback.lift_fst]
      simpa only [Category.assoc, ← Functor.map_comp, comparison_fst] using
        congrArg (fun k => k ≫ (schemeYoneda S).map (targetFst f a)) hm₂
    · rw [IsPullback.lift_snd]
      simpa only [Category.assoc, ← Functor.map_comp, comparison_snd] using
        congrArg (fun k => k ≫ (schemeYoneda S).map (targetSnd f a)) hm₂

/-- A relative property of the diagonal is equivalent to the property of this
one map of scheme kernel pairs, under the usual atlas descent hypothesis. -/
theorem relative_diagonal_iff
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Etale.{u} ⊓ @Surjective.{u})]
    (ha : IsEtale a) (hs : IsSurjective a) :
    (MorphismProperty.inverseImage P (Over.forget S)).relative (schemeYoneda S)
        (pullback.diagonal (hom f)) ↔ P (comparison f a).left := by
  constructor
  · intro h
    exact h.2 (atlas f a) _ _ (comparison_isPullback f a)
  · intro h
    have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
    let hr := relative_diagonal_representable f
    have hc : P (hr.snd (atlas f a)).left := by
      let e := (schemeYoneda S).preimageIso
        ((hr.isPullback (atlas f a)).isoIsPullback _ _ (comparison_isPullback f a))
      have he : e.hom ≫ comparison f a = hr.snd (atlas f a) := by
        apply (schemeYoneda S).map_injective
        simp [e, Functor.map_comp]
      rw [← he]
      have : IsIso e.hom.left := by
        change IsIso ((Over.forget S).map e.hom)
        infer_instance
      exact (P.cancel_left_of_respectsIso _ _).mpr h
    exact relativeProperty_of_etale_atlas P hr (atlas f a)
      (atlas_isEtale f a ha) (atlas_isSurjective f a hs) hc

/-- Separatedness is tested by a closed immersion between the two scheme kernel pairs. -/
theorem isSeparatedMorphism_iff (ha : IsEtale a) (hs : IsSurjective a) :
    IsSeparatedMorphism f ↔ _root_.AlgebraicGeometry.IsClosedImmersion
      (comparison f a).left :=
  relative_diagonal_iff f a @_root_.AlgebraicGeometry.IsClosedImmersion ha hs

end RelativeDiagonalChart

end Langlands.AlgebraicGeometry.AlgebraicSpace
