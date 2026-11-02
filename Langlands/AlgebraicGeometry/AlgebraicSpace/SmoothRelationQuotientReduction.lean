import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotientComparison
import Langlands.AlgebraicGeometry.AlgebraicSpace.MonomorphismPairScheme
import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasIsoTransport
import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasRelation
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAlgebraicSpaceQuotientStatement
import Langlands.AlgebraicGeometry.SmoothEquivalenceRelationEtaleSliceStatement
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentStatement

/-! # Reduction of the smooth relation quotient theorem -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A representable map has a scheme property `P` that descends along fppf covers as soon as
its base change along one surjective etale scheme atlas of the target has `P`. -/
theorem relative_of_isEtale_isSurjective (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    {F G : Presheaf S} {f : F ⟶ G} (hf : IsRepresentableMorphism f)
    {W V₀ : Over S} {A : (schemeYoneda S).obj W ⟶ G} (hA : IsEtale A) (hAs : IsSurjective A)
    (b₀ : (schemeYoneda S).obj V₀ ⟶ F) (p₀ : V₀ ⟶ W)
    (h₀ : IsPullback b₀ ((schemeYoneda S).map p₀) f A) (hp₀ : P p₀.left) :
    (P.inverseImage (Over.forget S)).relative (schemeYoneda S) f := by
  refine ⟨hf, ?_⟩
  intro T V g b p hsq
  let Y := schemeYoneda S
  let hA' := hA.representable
  let pT := hA'.snd g
  let fT := Functor.relativelyRepresentable.fst' hA' g
  have hT : IsPullback (Y.map fT) (Y.map pT) A g :=
    Functor.relativelyRepresentable.isPullback' hA' g
  have : Etale pT.left := hA.projection g _ pT hT
  have hpTs : Surjective pT.left := hAs.projection g _ pT hT
  let π₁ := pullback.fst p pT
  let π₂ := pullback.snd p pT
  have hsq₂ : IsPullback π₁ π₂ p pT := IsPullback.of_hasPullback p pT
  have hbig := (hsq₂.map Y).paste_horiz hsq
  rw [← hT.w] at hbig
  let k := h₀.lift (Y.map π₁ ≫ b) (Y.map π₂ ≫ Y.map fT) (by simpa using hbig.w)
  have hleft : IsPullback k (Y.map π₂) (Y.map p₀) (Y.map fT) :=
    IsPullback.of_right (by rwa [h₀.lift_fst]) (h₀.lift_snd _ _ _) h₀
  have hπ₂ : P π₂.left :=
    (MorphismProperty.relative_map (F := Y) (P := P.inverseImage (Over.forget S)) hp₀).property
      _ k π₂ hleft
  change P p.left
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := P)
    (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) (hsq₂.map (Over.forget S)).flip
    ⟨⟨hpTs, (inferInstance : Flat pT.left)⟩,
      (inferInstance : LocallyOfFinitePresentation pT.left)⟩ hπ₂

/-- In a kernel-pair square of presheaves with represented corners, two points have equal
images exactly when an actual arrow joins them. -/
lemma app_eq_iff_of_isPullback {F : Presheaf S} {U R : Over S} (a : (schemeYoneda S).obj U ⟶ F)
    (t s : R ⟶ U)
    (h : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a)
    {T : Over S} (x y : T ⟶ U) :
    a.app (op T) ⟨x⟩ = a.app (op T) ⟨y⟩ ↔ ∃ w : T ⟶ R, w ≫ t = x ∧ w ≫ s = y := by
  let Y := schemeYoneda S
  constructor
  · intro hxy
    have hw : Y.map x ≫ a = Y.map y ≫ a := by
      ext Z z
      exact (NatTrans.naturality_apply a z.down.op ⟨x⟩).trans
        ((congrArg (F.map z.down.op) hxy).trans (NatTrans.naturality_apply a z.down.op ⟨y⟩).symm)
    refine ⟨Y.preimage (h.lift (Y.map x) (Y.map y) hw), ?_, ?_⟩
    · apply Y.map_injective
      rw [Y.map_comp, Y.map_preimage, h.lift_fst]
    · apply Y.map_injective
      rw [Y.map_comp, Y.map_preimage, h.lift_snd]
  · rintro ⟨w, rfl, rfl⟩
    exact congrArg (fun φ ↦ φ.app (op T) ⟨w⟩) h.w

namespace SmoothRelationQuotient

/-- The four prerequisite propositions from which `SmoothRelationQuotientStatement` is derived:
monomorphisms locally of finite type into schemes come from schemes (P1), smooth equivalence
relations have etale slices (P2), smoothness descends along etale surjections of the source
(P4), and etale equivalence relations have algebraic-space quotients (D3). -/
def Prerequisites : Prop :=
  MonomorphismLocallyFiniteTypeSchemeStatement.{u} ∧
    SmoothEquivalenceRelationEtaleSliceStatement.{u} ∧
    SmoothEtaleSourceDescentStatement.{u} ∧
    EtaleEquivalenceRelationAlgebraicSpaceQuotientStatement.{u}

theorem smoothRelationQuotientStatement_of
    (hP1 : MonomorphismLocallyFiniteTypeSchemeStatement.{u})
    (hP2 : SmoothEquivalenceRelationEtaleSliceStatement.{u})
    (hP4 : SmoothEtaleSourceDescentStatement.{u})
    (hD3 : EtaleEquivalenceRelationAlgebraicSpaceQuotientStatement.{u}) :
    SmoothRelationQuotientStatement.{u} := by
  intro S U R s t h ⟨W, b, s₀, t₀, hbE, hbS, hbs, hbt, hs₀, ht₀⟩ hU
  let Y := schemeYoneda S
  let J := Scheme.etaleTopology.over S
  have : LocallyOfFiniteType s₀.left := inferInstance
  -- Step 1: the arrow space is a scheme.
  obtain ⟨R₀, ⟨eR⟩⟩ := MonomorphismPairScheme.isRepresentedByScheme_of_injective_pair hP1 R s t
    (fun T ↦ (h T).1) b s₀ t₀ hbE hbS hbs hbt this
  let s₁ : R₀ ⟶ U := Y.preimage (eR.hom ≫ s)
  let t₁ : R₀ ⟶ U := Y.preimage (eR.hom ≫ t)
  have hs₁ : Y.map s₁ = eR.hom ≫ s := Y.map_preimage _
  have ht₁ : Y.map t₁ = eR.hom ≫ t := Y.map_preimage _
  have hKP : IsPullback (Y.map s₁) (Y.map t₁) (quotientMap R s t h) (quotientMap R s t h) := by
    rw [hs₁, ht₁]
    exact IsPullback.of_iso (isPullback_quotientMap R s t h) eR.symm (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  -- Step 2: both projections of the scheme `R₀` are smooth.
  let e : W ⟶ R₀ := Y.preimage (b ≫ eR.inv)
  have he : Y.map e = b ≫ eR.inv := Y.map_preimage _
  have heE : Etale e.left := by
    have : IsEtale (Y.map e) := by rw [he]; exact hbE.comp_iso eR.symm
    exact MorphismProperty.of_relative_map
      (P := MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)) (F := schemeYoneda S) this
  have heS : Surjective e.left := by
    have : IsSurjective (Y.map e) := by rw [he]; exact hbS.comp_iso eR.symm
    exact MorphismProperty.of_relative_map
      (P := MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)) (F := schemeYoneda S)
      this
  have hes : e ≫ s₁ = s₀ := Y.map_injective (by
    rw [Functor.map_comp, he, hs₁, Category.assoc, eR.inv_hom_id_assoc, hbs])
  have het : e ≫ t₁ = t₀ := Y.map_injective (by
    rw [Functor.map_comp, he, ht₁, Category.assoc, eR.inv_hom_id_assoc, hbt])
  have hs₁S : Smooth s₁.left := hP4 _ _ _ e.left s₁.left heE heS (by
    rw [← Over.comp_left, hes]; exact hs₀)
  have ht₁S : Smooth t₁.left := hP4 _ _ _ e.left t₁.left heE heS (by
    rw [← Over.comp_left, het]; exact ht₀)
  have hEq : AtlasRelation.IsEquivRel s₁.left t₁.left :=
    AtlasRelation.isEquivRel_of_isPullback (quotientMap R s t h) s₁ t₁ hKP
  -- Step 3: an etale slice.
  obtain ⟨U'₀, g, hg, hhE, hhS⟩ := hP2 U.left R₀.left s₁.left t₁.left hEq hs₁S ht₁S
  let U' : Over S := Over.mk (g ≫ U.hom)
  let gO : U' ⟶ U := Over.homMk g
  let prU' := pullback.fst gO s₁
  let ρ := pullback.snd gO s₁
  have hα : IsPullback prU' ρ gO s₁ := IsPullback.of_hasPullback _ _
  let hO := ρ ≫ t₁
  have hα' : IsPullback prU'.left ρ.left g s₁.left := hα.map (Over.forget S)
  have hρ : hα'.isoPullback.hom ≫ pullback.snd g s₁.left = ρ.left := hα'.isoPullback_hom_snd
  have hOE : Etale hO.left := by
    change Etale (ρ.left ≫ t₁.left)
    rw [← hρ, Category.assoc]
    infer_instance
  have hOS : Surjective hO.left := by
    change Surjective (ρ.left ≫ t₁.left)
    rw [← hρ, Category.assoc]
    infer_instance
  -- Step 4: the restricted relation on `U'`.
  let R' := Limits.pullback hO gO
  let fX := pullback.fst hO gO
  let sO := pullback.snd hO gO
  let tO := fX ≫ prU'
  have hβ : IsPullback fX sO hO gO := IsPullback.of_hasPullback _ _
  have hγ : IsPullback (Y.map prU') (Y.map hO) (Y.map gO ≫ quotientMap R s t h)
      (quotientMap R s t h) := by
    have := (hα.map Y).paste_vert hKP
    simpa [hO] using this
  have hKP' : IsPullback (Y.map tO) (Y.map sO) (Y.map gO ≫ quotientMap R s t h)
      (Y.map gO ≫ quotientMap R s t h) := by
    have := (hβ.map Y).paste_horiz hγ
    simpa [tO] using this
  have hsOE : Etale sO.left :=
    MorphismProperty.of_isPullback (P := @Etale) (hβ.map (Over.forget S)) hOE
  have hR'eq : AtlasRelation.IsEquivRel tO.left sO.left :=
    AtlasRelation.isEquivRel_of_isPullback _ tO sO hKP'
  have htOE : Etale tO.left := by
    obtain ⟨σ, hσt, hσs, hσσ⟩ := hR'eq.exists_swap
    have : IsIso σ := ⟨σ, hσσ, hσσ⟩
    rw [← hσs]
    infer_instance
  let E := EtaleEquivalenceRelation.ofKernelPair tO sO _ hKP' htOE hsOE
  have hb : E.t ≫ U'.hom = E.s ≫ U'.hom := by
    change tO.left ≫ U'.hom = sO.left ≫ U'.hom
    rw [Over.w tO, Over.w sO]
  obtain ⟨Q', a, haE, haS, haK⟩ := hD3 S E U'.hom hb
  -- Step 5: the canonical quotient is the algebraic-space quotient of the slice.
  have hker : ∀ (T : Over S) (x y : T ⟶ U'), a.app (op T) ⟨x⟩ = a.app (op T) ⟨y⟩ ↔
      relation R s t T ((Y.map gO).app (op T) ⟨x⟩) ((Y.map gO).app (op T) ⟨y⟩) := by
    intro T x y
    refine (app_eq_iff_of_isPullback a _ _ haK x y).trans (Iff.trans ?_
      ((app_eq_iff_of_isPullback _ tO sO hKP' x y).symm.trans
        (quotientMap_eq_iff R s t h _ _)))
    constructor
    · rintro ⟨w, hw₁, hw₂⟩
      refine ⟨Over.homMk w.left ?_, ?_, ?_⟩
      · rw [← Over.w tO]
        exact Over.w w
      · ext
        exact congrArg CommaMorphism.left hw₁
      · ext
        exact congrArg CommaMorphism.left hw₂
    · rintro ⟨w, hw₁, hw₂⟩
      refine ⟨Over.homMk w.left ?_, ?_, ?_⟩
      · change w.left ≫ tO.left ≫ U'.hom = T.hom
        rw [Over.w tO]
        exact Over.w w
      · ext
        exact congrArg CommaMorphism.left hw₁
      · ext
        exact congrArg CommaMorphism.left hw₂
  have hQ'et : CategoryTheory.Presheaf.IsSheaf J Q'.presheaf :=
    Q'.toSheaf.property.of_le (Sites.etaleTopologyOver_le_fppfTopologyOver S)
  have haLS := isLocallySurjective_etale_of_isEtale_isSurjective a haE haS
  have hgLS : Presheaf.IsLocallySurjective J (Y.map gO ≫ quotientMap R s t h) := by
    have : Etale hO.left := hOE
    have : Surjective hO.left := hOS
    have h₁ := isLocallySurjective_etale_schemeYoneda_map hO
    have h₂ := isLocallySurjective_quotientMap R s t h
    have h₃ : Presheaf.IsLocallySurjective J (Y.map hO ≫ quotientMap R s t h) :=
      Presheaf.isLocallySurjective_comp J _ _
    exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hγ.w
  let eQ := quotientSheafIsoOfPresentation R s t h hQ'et (Y.map gO) a hgLS haLS hker
  have hfac : Y.map gO ≫ quotientMap R s t h ≫ eQ.hom = a :=
    quotientSheafIsoOfPresentation_hom_fac R s t h hQ'et (Y.map gO) a hgLS haLS hker
  -- Step 6: the conclusions.
  have hA : Y.map gO ≫ quotientMap R s t h = a ≫ eQ.inv :=
    (Iso.eq_comp_inv eQ).2 (by rw [Category.assoc]; exact hfac)
  have hdiag : HasRepresentableDiagonal (quotientSheaf R s t h).obj :=
    hasRepresentableDiagonal_of_iso eQ.symm Q'.hasRepresentableDiagonal
  have hqrep : IsRepresentableMorphism (quotientMap R s t h) :=
    Functor.relativelyRepresentable.of_diag hdiag _
  have hAE : IsEtale (Y.map gO ≫ quotientMap R s t h) := by
    rw [hA]
    exact haE.comp_iso eQ.symm
  have hAS : IsSurjective (Y.map gO ≫ quotientMap R s t h) := by
    rw [hA]
    exact haS.comp_iso eQ.symm
  have hprS : Smooth prU'.left := MorphismProperty.of_isPullback (P := @Smooth) hα'.flip hs₁S
  have hs₁surj : Surjective s₁.left := by
    obtain ⟨r, hr, -⟩ := hEq.refl U.left (𝟙 _)
    have : Surjective (r ≫ s₁.left) := by
      rw [hr]
      infer_instance
    exact Surjective.of_comp r s₁.left
  have hprSurj : Surjective prU'.left :=
    MorphismProperty.of_isPullback (P := @Surjective) hα'.flip hs₁surj
  have hdS : MorphismProperty.DescendsAlong @Smooth.{u}
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) := by
    have : IsZariskiLocalAtTarget @Smooth.{u} := HasRingHomProperty.instIsZariskiLocalAtTarget _
    exact instDescendsAlongSchemeMinMorphismPropertySurjectiveFlatLocallyOfFinitePresentationOfQuasiCompactOfIsZariskiLocalAtTarget
      @Smooth
  have hdSu : MorphismProperty.DescendsAlong @Surjective.{u}
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    instDescendsAlongSchemeMinMorphismPropertySurjectiveFlatLocallyOfFinitePresentationOfQuasiCompactOfIsZariskiLocalAtTarget
      @Surjective
  refine ⟨(CategoryTheory.Presheaf.isSheaf_of_iso_iff eQ).mpr Q'.toSheaf.property, hdiag,
    isPullback_quotientMap R s t h, ?_, ?_, ?_⟩
  · exact relative_of_isEtale_isSurjective (@Smooth) hqrep hAE hAS (Y.map hO) prU' hγ.flip hprS
  · exact relative_of_isEtale_isSurjective (@Surjective) hqrep hAE hAS (Y.map hO) prU' hγ.flip
      hprSurj
  · refine ⟨U', a ≫ eQ.inv, haE.comp_iso eQ.symm, haS.comp_iso eQ.symm, ?_⟩
    change LocallyOfFiniteType (g ≫ U.hom)
    infer_instance

theorem smoothRelationQuotientStatement_of_prerequisites (H : Prerequisites.{u}) :
    SmoothRelationQuotientStatement.{u} :=
  smoothRelationQuotientStatement_of H.1 H.2.1 H.2.2.1 H.2.2.2

end SmoothRelationQuotient

end Langlands.AlgebraicGeometry.AlgebraicSpace
