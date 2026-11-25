/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ClassicalContinuityMap
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
import WeilConjectures.RingTheory.IndEtaleSmallIndex

/-! # Sheafification on affine etale presentations

Source: Stacks Project, proetale.tex, Lemmas describe-pullback-from-etale and
limit-pullback (Tag 099S).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

private instance smallUpEquivalence {C : Type*} [Category* C] :
    (AsSmall.up : C ⥤ AsSmall.{w} C).IsEquivalence :=
  (AsSmall.equiv (C := C)).isEquivalence_functor

private instance smallDownEquivalence {C : Type*} [Category* C] :
    (AsSmall.down : AsSmall.{w} C ⥤ C).IsEquivalence :=
  (AsSmall.equiv (C := C)).isEquivalence_inverse

open Scheme in
private theorem modelLanRelative (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (F : (smallModelComparisonEtaleSite.{u, v} X)ᵒᵖ ⥤ ModuleCat.{max v (u + 1)} A) :
    Functor.PreservesRelativeFilteredColimits.{u} (AffineEtale.toAffineProEt X)
      ((AffineProEt.toProEt X ⋙ AsSmall.up).op ⋙
        (smallModelComparisonInclusion.{u, v} X).op.lan.obj F) := by
  constructor
  intro I _ _ K c hc
  let B := smallModelComparisonInclusion.{u, v} X
  let U : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X := AsSmall.up
  let T := K ⋙ AffineEtale.Spec X ⋙
    (AsSmall.up : X.Etale ⥤ smallModelComparisonEtaleSite.{u, v} X)
  let V := AffineProEt.toProEt X
  have : U.IsEquivalence := inferInstanceAs
    ((AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).IsEquivalence)
  have hc₁ : IsLimit (V.mapCone c) := isLimitOfPreserves _ hc
  have hcOver : IsLimit ((ProEt.forget X).mapCone (V.mapCone c)) :=
    isLimitOfReflects (Over.forget X)
      (((AffineProEt.isLimitMapConeToSchemeOfIsLimit c hc).ofIsoLimit
        (Functor.mapConeMapCone c).symm).ofIsoLimit (Functor.mapConeMapCone _).symm)
  let e : T ⋙ B ≅ ((K ⋙ AffineEtale.toAffineProEt X) ⋙ V) ⋙ U :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp; rfl)
  -- Sheaf descent uses small diagrams; the coefficient Hom sets are their ULifts.
  have hpres (Y : (smallModelComparisonEtaleSite.{u, v} X)ᵒᵖ) :
      PreservesColimit (T.op ⋙ B.op) (coyoneda.obj (op (B.op.obj Y))) := by
    let W := (toProEt X).obj (AsSmall.down.obj Y.unop)
    have h₁ {i j : I} (f : i ⟶ j) :
        IsAffineHom ((((K ⋙ AffineEtale.toAffineProEt X) ⋙ V) ⋙
          ProEt.forget X).map f).left :=
      inferInstanceAs (IsAffineHom ((AffineEtale.toAffineProEt X).map (K.map f)).left)
    have h₂ (i : I) : CompactSpace
        ((((K ⋙ AffineEtale.toAffineProEt X) ⋙ V) ⋙ ProEt.forget X).obj i).left :=
      inferInstanceAs (CompactSpace ((AffineEtale.toAffineProEt X).obj (K.obj i)).left)
    have h₃ (i : I) : QuasiSeparatedSpace
        ((((K ⋙ AffineEtale.toAffineProEt X) ⋙ V) ⋙ ProEt.forget X).obj i).left :=
      inferInstanceAs (QuasiSeparatedSpace ((AffineEtale.toAffineProEt X).obj (K.obj i)).left)
    have h₄ : LocallyOfFinitePresentation ((ProEt.forget X).obj W).hom :=
      inferInstanceAs (LocallyOfFinitePresentation (AsSmall.down.obj Y.unop).hom)
    have := Scheme.preservesColimit_yoneda
      (((K ⋙ AffineEtale.toAffineProEt X) ⋙ V) ⋙ ProEt.forget X)
      ((ProEt.forget X).obj W)
    have hyon : IsColimit ((yoneda.obj ((ProEt.forget X).obj W)).mapCocone
        ((ProEt.forget X).mapCone (V.mapCone c)).op) :=
      isColimitOfPreserves _ hcOver.op
    have hy : IsColimit ((yoneda.obj W).mapCocone (V.mapCone c).op) :=
      IsColimit.mapCoconeEquiv (ProEt.forgetOpCompYonedaIso W) hyon
    have hyl : IsColimit ((uliftYoneda.{max v (u + 1)}.obj W).mapCocone
        (V.mapCone c).op) :=
      (isColimitOfPreserves uliftFunctor hy).ofIsoColimit
        (Functor.mapCoconeMapCocone (V.mapCone c).op)
    let eY : U.op ⋙ yoneda.obj (B.obj Y.unop) ≅
        uliftYoneda.{max v (u + 1)}.obj W :=
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)
    have hmodel : IsColimit ((yoneda.obj (B.obj Y.unop)).mapCocone
        (U.mapCone (V.mapCone c)).op) :=
      (IsColimit.mapCoconeEquiv eY.symm hyl).ofIsoColimit
        (Functor.mapCoconeMapCocone (V.mapCone c).op).symm
    have hco : IsColimit ((coyoneda.obj (op (B.op.obj Y))).mapCocone
        (U.mapCone (V.mapCone c)).op) :=
      IsColimit.mapCoconeEquiv (Coyoneda.objOpOp _).symm hmodel
    have : PreservesColimit (((K ⋙ AffineEtale.toAffineProEt X) ⋙ V) ⋙ U).op
        (coyoneda.obj (op (B.op.obj Y))) :=
      preservesColimit_of_preserves_colimit_cocone
        (isLimitOfPreserves U hc₁).op hco
    exact preservesColimit_of_iso_diagram _ (NatIso.op e)
  have : ∀ Y, PreservesColimit (T.op ⋙ B.op) (coyoneda.obj (op (B.op.obj Y))) := hpres
  have : PreservesColimit (T.op ⋙ B.op) (B.op.leftKanExtension F) := inferInstance
  have : PreservesColimit (T ⋙ B).op (B.op.leftKanExtension F) :=
    inferInstanceAs (PreservesColimit (T.op ⋙ B.op) (B.op.leftKanExtension F))
  have : PreservesColimit (((K ⋙ AffineEtale.toAffineProEt X) ⋙ V) ⋙ U).op
      (B.op.leftKanExtension F) :=
    preservesColimit_of_iso_diagram _ (NatIso.op e).symm
  exact ⟨(isColimitOfPreserves (B.op.leftKanExtension F)
    (isLimitOfPreserves U hc₁).op).ofIsoColimit
      (Cocone.ext (Iso.refl _) (fun _ ↦ by simp; rfl))⟩

open Scheme in
private theorem modelLanSheaf (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (G : Sheaf (smallModelComparisonEtaleTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A)) :
    Presheaf.IsSheaf (AffineProEt.topology X)
      ((AffineProEt.toProEt X ⋙ AsSmall.up).op ⋙
        (smallModelComparisonInclusion.{u, v} X).op.lan.obj G.obj) := by
  have := modelLanRelative X A G.obj
  have : HasFilteredColimitsOfSize.{u, u} (ModuleCat.{max v (u + 1)} A) :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, max v (u + 1), max v (u + 1)}
  have : AB5OfSize.{u, u} (ModuleCat.{max v (u + 1)} A) :=
    AB5OfSize_of_univLE.{u, u, max v (u + 1), max v (u + 1)} _
  apply Presheaf.isSheaf_of_generates_of_isRelativelyPresentable
    (AffineEtale.toAffineProEt X) (AffineProEt.minimalPrecoverage X)
    (AffineEtale.topology X)
  · let Q := AffineEtale.Spec X ⋙
      (AsSmall.up : X.Etale ⥤ smallModelComparisonEtaleSite.{u, v} X)
    let B := smallModelComparisonInclusion.{u, v} X
    let e : Q ⋙ B ≅ AffineEtale.toAffineProEt X ⋙ AffineProEt.toProEt X ⋙
        (AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X) :=
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp; rfl)
    let iso : (AffineEtale.toAffineProEt X).op ⋙
        (AffineProEt.toProEt X ⋙ AsSmall.up).op ⋙ B.op.lan.obj G.obj ≅ Q.op ⋙ G.obj :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Functor.opComp _ _).symm _ ≪≫
        Functor.isoWhiskerRight (NatIso.op e) _ ≪≫
        Functor.isoWhiskerRight (Functor.opComp _ _) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (asIso (B.op.lanUnit.app G.obj)).symm
    rw [Presheaf.isSheaf_of_iso_iff iso]
    have : (AsSmall.up : X.Etale ⥤ smallModelComparisonEtaleSite.{u, v} X).IsContinuous
        X.smallEtaleTopology (smallModelComparisonEtaleTopology.{u, v} X) :=
      inferInstanceAs
        ((AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).functor.IsContinuous
          X.smallEtaleTopology
          ((AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).inverse.inducedTopology
            X.smallEtaleTopology))
    have hG := Functor.op_comp_isSheaf_of_isSheaf
      (AsSmall.up : X.Etale ⥤ smallModelComparisonEtaleSite.{u, v} X)
      X.smallEtaleTopology (smallModelComparisonEtaleTopology.{u, v} X) G.obj G.property
    exact Functor.op_comp_isSheaf_of_isSheaf (AffineEtale.Spec X)
      (AffineEtale.topology X) X.smallEtaleTopology _ hG
  · exact AffineProEt.generates_minimalPrecoverage X
  · exact AffineProEt.minimalPrecoverage_le_relativelyPresentable X
  · exact AffineProEt.minimalPrecoverage_le_finite X

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
open Scheme in
private theorem modelBasisToSheafify (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (G : Sheaf (smallModelComparisonEtaleTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A)) (Y : X.ProEt) (hY : proAffineEtale Y.hom) :
    IsIso ((toSheafify (coefficientProEtaleModelTopology.{u, v} X)
      ((smallModelComparisonInclusion.{u, v} X).op.lan.obj G.obj)).app
        (op (AsSmall.up.obj Y))) := by
  let U : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X := AsSmall.up
  let B := AffineProEt.toProEt X ⋙ U
  let J := AffineProEt.topology X
  let K := coefficientProEtaleModelTopology.{u, v} X
  have hU : U.IsDenseSubsite (ProEt.topology X) K := by
    change (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).functor.IsDenseSubsite
      (ProEt.topology X)
      ((AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).inverse.inducedTopology
        (ProEt.topology X))
    infer_instance
  have htop : U.inducedTopology K = ProEt.topology X := by
    ext V S
    rw [Functor.mem_inducedTopology_iff_of_isCoverDense]
    exact U.functorPushforward_mem_iff (ProEt.topology X) K
  have : B.IsCoverDense K := by
    dsimp [B]
    rw [Functor.IsCoverDense.comp_iff_of_isCoverDense, htop]
    infer_instance
  have : B.IsDenseSubsite J K :=
    { functorPushforward_mem_iff := by
        intro V S
        change S.functorPushforward (AffineProEt.toProEt X ⋙ U) ∈ _ ↔ _
        rw [Sieve.functorPushforward_comp]
        exact (U.functorPushforward_mem_iff (ProEt.topology X) K).trans
          ((AffineProEt.toProEt X).functorPushforward_mem_iff J (ProEt.topology X)) }
  have : HasLimitsOfSize.{u, max v (u + 1)} (ModuleCat.{max v (u + 1)} A) :=
    hasLimitsOfSizeShrink.{u, max v (u + 1), max v (u + 1), max v (u + 1)} _
  have : HasSheafify
      ((AsSmall.down : AsSmall.{max v (u + 1)} X.AffineProEt ⥤ X.AffineProEt).inducedTopology J)
      (ModuleCat.{max v (u + 1)} A) :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  have : (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.AffineProEt)).inverse.IsDenseSubsite
      ((AsSmall.down : AsSmall.{max v (u + 1)} X.AffineProEt ⥤ X.AffineProEt).inducedTopology J)
      J :=
    inferInstanceAs ((AsSmall.down :
      AsSmall.{max v (u + 1)} X.AffineProEt ⥤ X.AffineProEt).IsDenseSubsite
        ((AsSmall.down : AsSmall.{max v (u + 1)} X.AffineProEt ⥤ X.AffineProEt).inducedTopology J)
        J)
  have : HasSheafify J (ModuleCat.{max v (u + 1)} A) :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.AffineProEt)).hasSheafify J
      ((AsSmall.down : AsSmall.{max v (u + 1)} X.AffineProEt ⥤ X.AffineProEt).inducedTopology J)
      (ModuleCat.{max v (u + 1)} A)
  have : ∀ Z : (coefficientProEtaleSiteModel.{u, v} X)ᵒᵖ,
      HasLimitsOfShape (StructuredArrow Z B.op) (ModuleCat.{max v (u + 1)} A) :=
    fun _ ↦ inferInstance
  have : (B.sheafPushforwardContinuous (ModuleCat.{max v (u + 1)} A) J K).IsEquivalence :=
    inferInstance
  have hη : IsIso (B.op.whiskerLeft
      (toSheafify K ((smallModelComparisonInclusion.{u, v} X).op.lan.obj G.obj))) :=
    Functor.IsDenseSubsite.isIso_whiskerLeft_toSheafify J K B
      (ModuleCat.{max v (u + 1)} A) _ (modelLanSheaf X A G)
  exact inferInstanceAs (IsIso ((B.op.whiskerLeft
    (toSheafify K ((smallModelComparisonInclusion.{u, v} X).op.lan.obj G.obj))).app
      (op (AffineProEt.mk Y.hom hY))))

private noncomputable def affineSectionsColimit {J : Type*} [Category J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, IsAffine (D.obj j)] [IsAffine c.pt] :
    IsColimit (Scheme.Γ.mapCocone c.op) := by
  let α : D ≅ (D.op ⋙ Scheme.Γ).rightOp ⋙ Scheme.Spec :=
    NatIso.ofComponents (fun j ↦ (D.obj j).isoSpec)
      (fun f ↦ (Scheme.isoSpec_hom_naturality (D.map f)).symm)
  have hs : IsLimit (Scheme.Spec.mapCone
      (coneRightOpOfCocone (Scheme.Γ.mapCocone c.op))) := by
    refine IsLimit.equivOfNatIsoOfIso α c _ ?_ hc
    refine Cone.ext c.pt.isoSpec ?_
    intro j
    exact (Scheme.isoSpec_hom_naturality (X := c.pt) (Y := D.obj j) (c.π.app j)).symm
  exact isColimitOfConeRightOpOfCocone (D.op ⋙ Scheme.Γ)
    (isLimitOfReflects Scheme.Spec hs)

private theorem presentationVertexProAffineEtale {X : Scheme.{u}}
    {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
    (P : AffinePresentation X I) : proAffineEtale P.cone.pt.hom := by
  classical
  -- This restricted ring presentation is used only to prove basis membership.
  let i : I := IsCofiltered.nonempty.some
  have : IsAffine P.cone.pt.left := P.affineVertex
  have (j : I) : IsAffine (P.diagram.obj j).left := P.affine j
  have (j : I) : Etale (P.diagram.obj j).hom := P.etale j
  let V := Scheme.ProEt.forget X ⋙ Over.forget X
  let D := Over.forget i ⋙ P.diagram ⋙ V
  let c := (V.mapCone P.cone).whisker (Over.forget i)
  have hc : IsLimit c :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) _).symm
      (isLimitOfPreserves (Over.forget X) P.isLimit)
  have (j : Over i) : IsAffine (D.obj j) := P.affine j.left
  have : IsAffine c.pt := P.affineVertex
  let F := D.op ⋙ Scheme.Γ
  let t : (Functor.const (Over i)ᵒᵖ).obj Γ((P.diagram.obj i).left, ⊤) ⟶ F :=
    { app j := (P.diagram.map j.unop.hom).left.appTop
      naturality {j k} f := by
        dsimp [F, D, V]
        rw [Category.id_comp, ← Scheme.Hom.comp_appTop]
        congr 1
        change (P.diagram ⋙ V).map k.unop.hom =
          (P.diagram ⋙ V).map f.unop.left ≫ (P.diagram ⋙ V).map j.unop.hom
        rw [← Functor.map_comp, Over.w f.unop] }
  have hring : MorphismProperty.ind.{u + 1} CommRingCat.etale.{u}
      (P.cone.π.app i).left.appTop := by
    refine ⟨(Over i)ᵒᵖ, inferInstance, inferInstance, F, t,
      (Scheme.Γ.mapCocone c.op).ι, affineSectionsColimit D c hc, ?_⟩
    intro j
    have hf : Etale (P.diagram.map j.unop.hom).left := by
      have : Etale ((P.diagram.map j.unop.hom).left ≫ (P.diagram.obj i).hom) := by
        rw [MorphismProperty.Over.w]
        exact P.etale j.unop.left
      exact Etale.of_comp (P.diagram.map j.unop.hom).left (P.diagram.obj i).hom
    refine ⟨?_, ?_⟩
    · exact (HasRingHomProperty.iff_of_isAffine (P := @Etale)
        (f := (P.diagram.map j.unop.hom).left)).mp hf
    · change (P.diagram.map j.unop.hom).left.appTop ≫
        (P.cone.π.app j.unop.left).left.appTop = (P.cone.π.app i).left.appTop
      rw [← Scheme.Hom.comp_appTop]
      exact congrArg (fun f ↦ f.left.appTop) (P.cone.w j.unop.hom)
  let p : P.cone.pt.left ⟶ (P.diagram.obj i).left := (P.cone.π.app i).left
  have hπ : proAffineEtale p := by
    rw [proAffineEtale_iff_appTop, RingHom.IndEtale.iff_ind_etale]
    exact CommRingCat.ind_etale_small_index _ hring
  have hw : p ≫ (P.diagram.obj i).hom = P.cone.pt.hom :=
    MorphismProperty.Over.w (P.cone.π.app i)
  rw [← hw]
  exact proAffineEtale.comp_mem _ _ hπ
    (proAffineEtale.of_isAffine (X := (P.diagram.obj i).left) (P.diagram.obj i).hom)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Sheafification of the coefficient-sized comparison Kan extension changes
neither the vertex nor the stages of an affine etale presentation.

Source: Stacks Project, proetale.tex, lemma-describe-pullback-from-etale and
lemma-limit-pullback (Tag 099S)
(auxiliary; not a blueprint node).

Proof: the presheaf inverse image is the left Kan extension. On the affine
ind-etale basis it is already a sheaf: present each object by affine etale
objects, compute its sections by the filtered colimit formula, and descend a
finite covering and its pairwise intersections to finite stages. The sheaf
condition at those stages and exactness of filtered colimits of A-modules give
the sheaf condition on the basis. The dense-subsite sheafification theorem
therefore makes the unit invertible on the basis. Each stage is affine etale,
hence belongs to this basis. For the vertex, fix a stage and restrict to the
cofiltered category over that stage; the global-sections cocone of affine
schemes is a ring colimit, by full faithfulness of Spec. It exhibits the vertex
as ind-etale over the affine stage. Shrink this ring presentation using
lem-pe-ind-etale-small-index. Composing with the stage's etale map to X gives
an affine ind-etale presentation over X, so the vertex also belongs to the
basis. This shrinking is used only for basis membership, not for identifying
the original projection cocone. Transport basis sheaves, sheafification and
its unit along the two AsSmall equivalences. Module colimits and finite limits
exist at the displayed coefficient size, and filtered colimits are exact there.
The zero module sheaf and the empty affine object are included in this argument. -/
theorem coefficientComparison_presentation_toSheafify_isIso (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (G : Sheaf (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A))
    {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
    (P : AffinePresentation X I) :
    let L := (Scheme.smallModelComparisonInclusion.{u, v} X).op.lan.obj G.obj
    let η := toSheafify (Scheme.coefficientProEtaleModelTopology.{u, v} X) L
    IsIso (η.app (op (AsSmall.up.obj P.cone.pt))) ∧
      ∀ i : I, IsIso (η.app (op (AsSmall.up.obj (P.diagram.obj i)))) := by
  refine ⟨modelBasisToSheafify X A G P.cone.pt (presentationVertexProAffineEtale P), ?_⟩
  intro i
  have : IsAffine (P.diagram.obj i).left := P.affine i
  have : Etale (P.diagram.obj i).hom := P.etale i
  exact modelBasisToSheafify X A G (P.diagram.obj i)
    (proAffineEtale.of_isAffine (X := (P.diagram.obj i).left) (P.diagram.obj i).hom)

end AlgebraicGeometry.ProEtale
