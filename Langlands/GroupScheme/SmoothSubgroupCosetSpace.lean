import Langlands.GroupScheme.HomogeneousQuotientSheaf
import Langlands.AlgebraicGeometry.SmoothSurjectiveEtaleLocalSections
import Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent
import Langlands.AlgebraicGeometry.AlgebraicSpace.RelativeHelpers
import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasIsoTransport
import Mathlib.CategoryTheory.MorphismProperty.Descent

/-! # Testing a represented relative property on a smooth atlas -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {F G : Presheaf S} {f : F ⟶ G}

/-- Properties detected on etale covers are also detected on smooth covers,
using actual etale local sections of smooth surjections. -/
theorem descendsAlong_smoothSurjective
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Etale.{u} ⊓ @Surjective.{u})] :
    P.DescendsAlong (@Smooth.{u} ⊓ @Surjective.{u}) where
  of_isPullback {A X Y Z fst snd f g} h hf hfst := by
    have : Smooth f := hf.1
    have : Surjective f := hf.2
    obtain ⟨V, e, s, he, hs, hfac⟩ :=
      Langlands.AlgebraicGeometry.smoothSurjectiveEtaleLocalSections X Z f hf.1 hf.2
    have hbig := (IsPullback.of_hasPullback fst s).paste_horiz h.flip
    rw [hfac] at hbig
    exact MorphismProperty.of_isPullback_of_descendsAlong
      (P := P) (Q := @Etale.{u} ⊓ @Surjective.{u}) hbig.flip ⟨he, hs⟩
      (P.of_isPullback (IsPullback.of_hasPullback fst s) hfst)

private theorem prodMap_mem {C : Type*} [Category* C] [HasBinaryProducts C]
    (P : MorphismProperty C) [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'} (hf : P f) (hg : P g) :
    P (prod.map f g) := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hleft : P (prod.map f (𝟙 A')) :=
    P.of_isPullback (IsPullback.of_prod_fst_with_id f A') hf
  have hright : P (prod.map (𝟙 B) g) := by
    have he : prod.map (𝟙 B) g =
        (prod.braiding B A').hom ≫ prod.map g (𝟙 B) ≫ (prod.braiding B' B).hom := by
      ext <;> simp
    rw [he, P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]
    exact P.of_isPullback (IsPullback.of_prod_fst_with_id g B) hg
  have he : prod.map f g = prod.map f (𝟙 A') ≫ prod.map (𝟙 B) g := by
    ext <;> simp
  rw [he]
  exact P.comp_mem _ _ hleft hright

section PairAtlas

variable {U R : Over S} {F : Presheaf S} (a : (schemeYoneda S).obj U ⟶ F)

/-- The doubled scheme presentation of a product presheaf. -/
def pairAtlas : (schemeYoneda S).obj (U ⨯ U) ⟶ F ⨯ F :=
  prodComparison (schemeYoneda S) U U ≫ prod.map a a

@[reassoc (attr := simp)]
lemma pairAtlas_fst : pairAtlas a ≫ prod.fst = (schemeYoneda S).map prod.fst ≫ a := by
  simp [pairAtlas]

@[reassoc (attr := simp)]
lemma pairAtlas_snd : pairAtlas a ≫ prod.snd = (schemeYoneda S).map prod.snd ≫ a := by
  simp [pairAtlas]

lemma pairAtlas_mem (P : MorphismProperty (Over S)) [P.IsStableUnderComposition]
    (ha : P.relative (schemeYoneda S) a) :
    P.relative (schemeYoneda S) (pairAtlas a) := by
  let W := P.relative (schemeYoneda S)
  have : W.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange _
  change W (prodComparison (schemeYoneda S) U U ≫ prod.map a a)
  rw [W.cancel_left_of_respectsIso]
  exact prodMap_mem W ha ha

/-- A scheme kernel pair is the base change of the target diagonal to the
doubled scheme presentation. -/
lemma diagonal_isPullback_of_kernel {s t : R ⟶ U}
    (h : IsPullback ((schemeYoneda S).map s) ((schemeYoneda S).map t) a a) :
    IsPullback ((schemeYoneda S).map s ≫ a)
      ((schemeYoneda S).map (prod.lift s t)) (diag F) (pairAtlas a) := by
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun c => h.lift
    (c.snd ≫ (schemeYoneda S).map prod.fst)
    (c.snd ≫ (schemeYoneda S).map prod.snd) ?_) ?_ ?_ ?_⟩⟩
  · apply prod.hom_ext
    · simp [diag, ← Functor.map_comp_assoc]
    · simpa [diag, ← Functor.map_comp_assoc] using h.w
  · have he1 := c.condition =≫ prod.fst
    have he2 := c.condition =≫ prod.snd
    simp only [Category.assoc, diag, prod.lift_fst, prod.lift_snd, Category.comp_id,
      pairAtlas_fst, pairAtlas_snd] at he1 he2
    exact he1.symm.trans he2
  · intro c
    rw [← Category.assoc, h.lift_fst]
    have he := c.condition =≫ prod.fst
    simpa only [Category.assoc, diag, prod.lift_fst, Category.comp_id, pairAtlas_fst] using he.symm
  · intro c
    apply (cancel_mono (prodComparison (schemeYoneda S) U U)).mp
    apply prod.hom_ext
    · simp only [Category.assoc, prodComparison_fst, ← Functor.map_comp,
        prod.lift_fst, h.lift_fst]
    · simp only [Category.assoc, prodComparison_snd, ← Functor.map_comp,
        prod.lift_snd, h.lift_snd]
  · intro c m hm1 hm2
    apply h.hom_ext
    · have he := hm2 =≫ (schemeYoneda S).map prod.fst
      simpa only [Category.assoc, ← Functor.map_comp, prod.lift_fst, h.lift_fst] using he
    · have he := hm2 =≫ (schemeYoneda S).map prod.snd
      simpa only [Category.assoc, ← Functor.map_comp, prod.lift_snd, h.lift_snd] using he

end PairAtlas

namespace SmoothRepresentedAtlas

variable (hr : IsRepresentableMorphism f) {U T : Over S}
    (a : (schemeYoneda S).obj U ⟶ G) (ha : IsSmooth a)
    (g : (schemeYoneda S).obj T ⟶ G)

/-- The actual scheme over a test scheme representing its pullback of the atlas. -/
abbrev atlasScheme : Over S := ha.rep.pullback g

/-- The projection from the represented pullback of the map to the test scheme. -/
abbrev mapProjection : hr.pullback g ⟶ T := hr.snd g

/-- The projection from the represented pullback of the atlas to the test scheme. -/
abbrev atlasProjection : atlasScheme a ha g ⟶ T := ha.rep.snd g

/-- The pullback of the two represented projections gives a refinement on which
the map's source and the target atlas are both available. -/
abbrev refinement : Over S :=
  Limits.pullback (mapProjection hr g) (atlasProjection a ha g)

/-- The refinement maps to the source presheaf through the first represented projection. -/
abbrev refinementSource : (schemeYoneda S).obj (refinement hr a ha g) ⟶ F :=
  (schemeYoneda S).map (pullback.fst (mapProjection hr g) (atlasProjection a ha g)) ≫ hr.fst g

/-- The refinement maps to the represented pullback of the map along the atlas. -/
def comparison : refinement hr a ha g ⟶ hr.pullback a :=
  hr.lift (refinementSource hr a ha g)
    (pullback.snd (mapProjection hr g) (atlasProjection a ha g) ≫ ha.rep.fst' g) (by
      have h := (((IsPullback.of_hasPullback (mapProjection hr g)
        (atlasProjection a ha g)).map (schemeYoneda S)).paste_horiz (hr.isPullback g)).w
      have hw : (schemeYoneda S).map (atlasProjection a ha g) ≫ g =
          (schemeYoneda S).map (ha.rep.fst' g) ≫ a := (ha.rep.isPullback' g).w.symm
      simpa only [refinementSource, Functor.map_comp, Category.assoc, ← hw] using h)

set_option backward.isDefEq.respectTransparency false in
/-- Both ways to present the fibre product agree: the comparison square is a pullback. -/
theorem comparison_isPullback :
    IsPullback ((schemeYoneda S).map (comparison hr a ha g))
      ((schemeYoneda S).map
        (pullback.snd (mapProjection hr g) (atlasProjection a ha g)))
      ((schemeYoneda S).map (hr.snd a)) ((schemeYoneda S).map (ha.rep.fst' g)) := by
  let j := pullback.snd (mapProjection hr g) (atlasProjection a ha g)
  have houter : IsPullback (refinementSource hr a ha g)
      ((schemeYoneda S).map j) f ((schemeYoneda S).map (ha.rep.fst' g) ≫ a) := by
    have h := ((IsPullback.of_hasPullback (mapProjection hr g)
      (atlasProjection a ha g)).map (schemeYoneda S)).paste_horiz (hr.isPullback g)
    have hw : (schemeYoneda S).map (atlasProjection a ha g) ≫ g =
        (schemeYoneda S).map (ha.rep.fst' g) ≫ a := (ha.rep.isPullback' g).w.symm
    change IsPullback (refinementSource hr a ha g) ((schemeYoneda S).map j) f
      ((schemeYoneda S).map (atlasProjection a ha g) ≫ g) at h
    rwa [hw] at h
  apply IsPullback.of_right _ _ (hr.isPullback a)
  · dsimp only [comparison]
    rw [Functor.relativelyRepresentable.lift_fst]
    exact houter
  · rw [← Functor.map_comp, ← Functor.map_comp]
    exact (schemeYoneda S).congr_map (hr.lift_snd _ _ _)

end SmoothRepresentedAtlas

/-- A represented map has a scheme property once its pullback along one surjective
smooth atlas has that property, provided the property is stable under base change
and descends along surjective smooth scheme maps. Representability is retained
as an explicit premise. -/
theorem relativeProperty_of_smooth_atlas
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Smooth.{u} ⊓ @Surjective.{u})]
    (hr : IsRepresentableMorphism f) {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ G) (ha : IsSmooth a) (hs : IsSurjective a)
    (hP : P (hr.snd a).left) :
    (MorphismProperty.inverseImage P (Over.forget S)).relative (schemeYoneda S) f := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  apply MorphismProperty.relative_of_snd hr
  intro T g
  let q := hr.snd g
  let p := ha.rep.snd g
  have hp : Smooth p.left := ha.property_snd g
  have hps : Surjective p.left := hs.projection g (ha.rep.fst g) p (ha.rep.isPullback g)
  have h : P (pullback.snd q p).left :=
    MorphismProperty.of_isPullback
      ((isPullback_of_map (SmoothRepresentedAtlas.comparison_isPullback hr a ha g)).map
        (Over.forget S)) hP
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := P) (Q := @Smooth.{u} ⊓ @Surjective.{u})
    ((IsPullback.of_hasPullback q p).map (Over.forget S)).flip ⟨hp, hps⟩ h

/-- A smooth surjective scheme presentation with a closed scheme kernel
relation has a closed diagonal. -/
theorem isClosedImmersion_diag_of_smooth_presentation
    {U R : Over S} {F : Presheaf S} (a : (schemeYoneda S).obj U ⟶ F)
    (hd : HasRepresentableDiagonal F) (ha : IsSmooth a) (hs : IsSurjective a)
    {s t : R ⟶ U}
    (hker : IsPullback ((schemeYoneda S).map s) ((schemeYoneda S).map t) a a)
    (hclosed : _root_.AlgebraicGeometry.IsClosedImmersion (prod.lift s t).left) :
    IsClosedImmersion (diag F) := by
  let P : MorphismProperty Scheme.{u} := @_root_.AlgebraicGeometry.IsClosedImmersion
  let : P.DescendsAlong (@Smooth.{u} ⊓ @Surjective.{u}) :=
    descendsAlong_smoothSurjective P
  have hp := diagonal_isPullback_of_kernel a hker
  let e : hd.pullback (pairAtlas a) ≅ R :=
    (schemeYoneda S).preimageIso ((hd.isPullback (pairAtlas a)).isoIsPullback _ _ hp)
  have he : e.hom ≫ prod.lift s t = hd.snd (pairAtlas a) := by
    apply (schemeYoneda S).map_injective
    rw [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage,
      IsPullback.isoIsPullback_hom_snd]
  have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  have : _root_.AlgebraicGeometry.IsClosedImmersion (prod.lift s t).left := hclosed
  have hP : P (hd.snd (pairAtlas a)).left := by
    rw [← he, Over.comp_left]
    infer_instance
  have : (MorphismProperty.inverseImage (@Smooth.{u}) (Over.forget S)).IsStableUnderComposition := {
    comp_mem f g hf hg := by
      have : Smooth f.left := hf
      have : Smooth g.left := hg
      change Smooth (f.left ≫ g.left)
      infer_instance }
  have : (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).IsStableUnderComposition := {
    comp_mem f g hf hg := by
      have : Surjective f.left := hf
      have : Surjective g.left := hg
      change Surjective (f.left ≫ g.left)
      infer_instance }
  exact relativeProperty_of_smooth_atlas P hd (pairAtlas a)
    (pairAtlas_mem a (MorphismProperty.inverseImage (@Smooth.{u}) (Over.forget S)) ha)
    (pairAtlas_mem a (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)) hs) hP

end Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.GroupScheme.HomogeneousQuotientSheaf

open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotient
open Langlands.GroupScheme.HomogeneousQuotientFromEmbedding

variable {S : Scheme.{u}} {G H : GroupScheme S} (i : H ⟶ G) [Mono i.hom.hom]
    [LocallyOfFiniteType G.X.hom] (hH : Smooth H.X.hom)

/-- The actual algebraic space of right cosets by a smooth subgroup, without
affineness or smoothness assumptions on the ambient group. -/
def space : Langlands.AlgebraicGeometry.AlgebraicSpace S := by
  refine ⟨sheaf i hH, ?_⟩
  obtain ⟨_, hd, _, _, _, V, a, he, hs, _⟩ :=
    smoothRelationQuotient S G.X (arrowSpace i) (source i) (target i)
      (isEquivalenceRelation i) (hasSmoothProjections i hH) inferInstance
  exact ⟨hd, V, a, he, hs⟩

include hH in
/-- A closed smooth subgroup has a separated actual coset algebraic space. -/
theorem isClosedImmersion_diagonal (hi : IsClosedSubgroup i) :
    IsClosedImmersion (diag (presheaf i)) := by
  obtain ⟨_, hd, hker, hsm, hs, _⟩ :=
    smoothRelationQuotient S G.X (arrowSpace i) (source i) (target i)
      (isEquivalenceRelation i) (hasSmoothProjections i hH) inferInstance
  let e : (G.X ⊗ G.X) ≅ G.X ⨯ G.X :=
    (CategoryTheory.CartesianMonoidalCategory.tensorProductIsBinaryProduct G.X G.X).conePointUniqueUpToIso
      (limit.isLimit (pair G.X G.X))
  have he : HomogeneousCosetRelation.inclusion i ≫ e.hom =
      prod.lift (HomogeneousCosetRelation.source i) (HomogeneousCosetRelation.target i) := by
    apply prod.hom_ext <;> simp [e]
  have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  have := HomogeneousCosetRelation.inclusion_isClosedImmersion i hi
  have hclosed : _root_.AlgebraicGeometry.IsClosedImmersion
      (prod.lift (HomogeneousCosetRelation.source i) (HomogeneousCosetRelation.target i)).left := by
    rw [← he, Over.comp_left]
    infer_instance
  exact isClosedImmersion_diag_of_smooth_presentation (projection i) hd hsm hs hker hclosed

/-- The actual separated coset algebraic space of a closed smooth subgroup. -/
def separatedSpace (hi : IsClosedSubgroup i) :
    { X : Langlands.AlgebraicGeometry.AlgebraicSpace S // IsClosedImmersion (diag X.presheaf) } :=
  ⟨space i hH, isClosedImmersion_diagonal i hH hi⟩

end Langlands.GroupScheme.HomogeneousQuotientSheaf
