import Langlands.AlgebraicGeometry.AlgebraicSpace.ActionQuotientFinitenessProof
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Diagonal geometry and structural atlases from smooth scheme presentations -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open ActionQuotientFiniteness

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {U R : Over S}

/-- A property of the relation inclusion descends to the space diagonal
along a smooth surjective scheme presentation. -/
theorem relative_diagonal_of_smooth_presentation
    (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (ha : IsSmooth a) (hs : IsSurjective a)
    (t s : R ⟶ U)
    (h : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a)
    (hj : P (prod.lift t s).left) :
    (P.inverseImage (Over.forget S)).relative (schemeYoneda S) (diag X.presheaf) := by
  let Y := schemeYoneda S
  let j : R ⟶ U ⨯ U := prod.lift t s
  let e : Y.obj (U ⨯ U) ≅ Y.obj U ⨯ Y.obj U := PreservesLimitPair.iso Y U U
  let A : Y.obj (U ⨯ U) ⟶ X.presheaf ⨯ X.presheaf := e.hom ≫ prod.map a a
  have hAe : IsSmooth A := by
    change (MorphismProperty.inverseImage (@Smooth.{u}) (Over.forget S)).relative Y A
    exact MorphismProperty.RespectsIso.precomp _ _ _
      (relative_prod_map (@Smooth.{u}) ha ha)
  have hAs : IsSurjective A := by
    change (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).relative Y A
    exact MorphismProperty.RespectsIso.precomp _ _ _
      (relative_prod_map (@Surjective.{u}) hs hs)
  have hjmap : Y.map j ≫ e.hom = prod.lift (Y.map t) (Y.map s) := by
    apply prod.hom_ext <;> simp [e, PreservesLimitPair.iso_hom, j, ← Functor.map_comp]
  have hsq : IsPullback (Y.map t ≫ a) (Y.map j) (diag X.presheaf) A := by
    apply (FinitePresentationRelationQuotient.isPullback_kernel_diagonal h).of_iso'
      (Iso.refl _) (Iso.refl _) e (Iso.refl _)
    · rfl
    · simpa using hjmap.symm
    · simp
    · simp [A]
  exact relative_of_isSmooth_isSurjective P
    X.hasRepresentableDiagonal hAe hAs (Y.map t ≫ a) j hsq hj

/-- Smoothness of the presenting scheme over the base makes every etale
scheme atlas smooth over the base. -/
theorem smooth_atlas_of_smooth_presentation
    (q : (schemeYoneda S).obj U ⟶ X.presheaf)
    (hq : IsSmooth q) (hqs : IsSurjective q) [Smooth U.hom]
    {V : Over S} (a : (schemeYoneda S).obj V ⟶ X.presheaf)
    (ha : IsEtale a) : Smooth V.hom := by
  let Y := schemeYoneda S
  let W := hq.representable.pullback a
  let p : W ⟶ V := hq.representable.snd a
  let r : W ⟶ U := Functor.relativelyRepresentable.fst' hq.representable a
  have h : IsPullback (Y.map r) (Y.map p) q a :=
    Functor.relativelyRepresentable.isPullback' hq.representable a
  let : Smooth p.left := hq.projection a _ p h
  let : Surjective p.left := hqs.projection a _ p h
  let : Etale r.left := ha.projection q _ r h.flip
  have : Smooth (p.left ≫ V.hom) := by
    rw [Over.w p, ← Over.w r]
    infer_instance
  exact Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp
    p.left V.hom

/-- An open diagonal of the space makes the structural map of an etale
scheme chart formally unramified, without any prior schemehood assumption. -/
theorem formallyUnramified_atlas_of_open_diagonal
    (hd : IsOpenImmersion (diag X.presheaf))
    {V : Over S} (a : (schemeYoneda S).obj V ⟶ X.presheaf)
    (ha : IsEtale a) : FormallyUnramified V.hom := by
  let Y := schemeYoneda S
  obtain ⟨E, t, s, h, _⟩ := AtlasRelation.exists_kernelPair a ha.representable
  let j : E ⟶ V ⨯ V := prod.lift t s
  let e : Y.obj (V ⨯ V) ≅ Y.obj V ⨯ Y.obj V := PreservesLimitPair.iso Y V V
  have hjmap : Y.map j ≫ e.hom = prod.lift (Y.map t) (Y.map s) := by
    apply prod.hom_ext <;> simp [e, PreservesLimitPair.iso_hom, j, ← Functor.map_comp]
  have hsq : IsPullback (Y.map t ≫ a) (Y.map j) (diag X.presheaf)
      (e.hom ≫ prod.map a a) := by
    apply (FinitePresentationRelationQuotient.isPullback_kernel_diagonal h).of_iso'
      (Iso.refl _) (Iso.refl _) e (Iso.refl _)
    · rfl
    · simpa using hjmap.symm
    · simp
    · simp
  let : _root_.AlgebraicGeometry.IsOpenImmersion j.left :=
    hd.2 _ _ j hsq
  let : Etale s.left := ha.projection a _ s h
  let d : V ⟶ E := Y.preimage (h.lift (𝟙 _) (𝟙 _) rfl)
  have hdt : d ≫ t = 𝟙 V := by
    apply Y.map_injective
    rw [Functor.map_comp]
    dsimp [d]
    rw [Functor.map_preimage, h.lift_fst]
    exact (Y.map_id V).symm
  have hds : d ≫ s = 𝟙 V := by
    apply Y.map_injective
    rw [Functor.map_comp]
    dsimp [d]
    rw [Functor.map_preimage, h.lift_snd]
    exact (Y.map_id V).symm
  let : MorphismProperty.HasOfPostcompProperty
      @_root_.AlgebraicGeometry.IsOpenImmersion @Etale :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
      (fun _ _ g _ => inferInstanceAs
        (_root_.AlgebraicGeometry.IsOpenImmersion (pullback.diagonal g)))
  have hsection : _root_.AlgebraicGeometry.IsOpenImmersion (d.left ≫ s.left) := by
    rw [← Over.comp_left, hds]
    infer_instance
  let : _root_.AlgebraicGeometry.IsOpenImmersion d.left :=
    MorphismProperty.of_postcomp @_root_.AlgebraicGeometry.IsOpenImmersion
      d.left s.left ‹Etale _› hsection
  have hdj : d ≫ j = diag V := by
    apply prod.hom_ext <;> simp [j, hdt, hds]
  have : _root_.AlgebraicGeometry.IsOpenImmersion (diag V).left := by
    rw [← hdj, Over.comp_left]
    infer_instance
  have heq : (diag V).left ≫ (Over.prodLeftIsoPullback V V).hom =
      pullback.diagonal V.hom := by
    apply pullback.hom_ext <;> simp [← Over.comp_left]
  have : _root_.AlgebraicGeometry.IsOpenImmersion (pullback.diagonal V.hom) := by
    rw [← heq]
    infer_instance
  infer_instance

/-- A smooth presentation by a smooth scheme and an open space diagonal
produce an etale-over-base atlas by actual schemes. -/
theorem etale_structural_atlas_of_smooth_presentation
    (q : (schemeYoneda S).obj U ⟶ X.presheaf)
    (hq : IsSmooth q) (hqs : IsSurjective q) [Smooth U.hom]
    (hd : IsOpenImmersion (diag X.presheaf)) :
    HasAtlasProperty (@Etale.{u}) X := by
  obtain ⟨V, a, _, ha, hs⟩ := X.exists_atlas
  let : Smooth V.hom := smooth_atlas_of_smooth_presentation q hq hqs a ha
  let : FormallyUnramified V.hom := formallyUnramified_atlas_of_open_diagonal hd a ha
  exact ⟨V, a, ha, hs, Etale.of_formallyUnramified_of_flat V.hom⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
