/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Relative.RelativeCocycleCoordinates
import Mathlib.CategoryTheory.Whiskering

/-!
# Naturality of the explicit relative torsor classification

## References

* Stacks Project, Tag 03AJ
* Tag 0G78
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- An equivariant map of pointed torsors gives the coefficient map on relative H1. -/
theorem relativeTorsorEquiv_coefficient
    (T : Scheme.{u}) (U : T.Etale)
    {G G' : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}} (f : G ⟶ G')
    (I : InjectiveResolution G) (J : InjectiveResolution G') (a : I.Hom J f)
    (P : Sheaf.Torsor.WithSection G U) (Q : Sheaf.Torsor G')
    (σ : P.1.sheaf.obj ⟶ Q.sheaf.obj)
    (hσ : ∀ A g t, σ.app A (P.1.vadd A g t) = Q.vadd A (f.hom.app A g) (σ.app A t))
    (h : HomologicalComplex.extendMap
        (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex _).map a.hom)
        ComplexShape.embeddingUpNat ≫ relativeSectionRestriction T U J.cocomplex =
      relativeSectionRestriction T U I.cocomplex ≫ HomologicalComplex.extendMap
        (((etaleSectionFunctor U).mapHomologicalComplex _).map a.hom)
        ComplexShape.embeddingUpNat) :
    HomologicalComplex.homologyMap (relativeFiberMap _ _
        (HomologicalComplex.extendMap
          (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex _).map a.hom)
          ComplexShape.embeddingUpNat)
        (HomologicalComplex.extendMap
          (((etaleSectionFunctor U).mapHomologicalComplex _).map a.hom)
          ComplexShape.embeddingUpNat) h) 1
        (relativeTorsorEquiv T U I (Quotient.mk _ P)) =
      relativeTorsorEquiv T U J (Quotient.mk _ ⟨Q, σ.app (op U) P.2⟩) := by
  let hT := MorphismProperty.Over.mkIdTerminal @Etale T
  let : Injective (I.cocomplex.X 0) := I.injective 0
  let : Injective (J.cocomplex.X 0) := J.injective 0
  obtain ⟨s, ⟨e⟩⟩ := Sheaf.Torsor.exists_equiv_lifts hT
    (resolutionLiftSequence_shortExact T I) P.1
  obtain ⟨s', ⟨e'⟩⟩ := Sheaf.Torsor.exists_equiv_lifts hT
    (resolutionLiftSequence_shortExact T J) Q
  rw [relativeTorsorEquiv_presentation T U I P s e,
    relativeTorsorEquiv_presentation T U J ⟨Q, σ.app (op U) P.2⟩ s' e']
  let b := resolutionPresentationMap T I P.1 s e
  let b' := resolutionPresentationMap T J Q s' e'
  let μ := b ≫ Functor.whiskerRight (a.hom.f 0).hom (forget AddCommGrpCat.{u + 1})
  let ν := σ ≫ b'
  let φ := I.ι.f 0 ≫ a.hom.f 0
  let s₁ := (I.cocomplex.iCycles 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) s
  let s₁' := (J.cocomplex.iCycles 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) s'
  have haug (A : T.Etaleᵒᵖ) (g : G.obj.obj A) :
      (a.hom.f 0).hom.app A ((I.ι.f 0).hom.app A g) =
        (J.ι.f 0).hom.app A (f.hom.app A g) :=
    congrArg (fun k : G ⟶ J.cocomplex.X 0 => k.hom.app A g) a.ι_f_zero_comp_hom_f_zero
  obtain ⟨x, hd, hr⟩ := Sheaf.Torsor.difference_of_equivariant_lifts hT P.1
    (J.cocomplex.X 0) (J.cocomplex.X 1) (J.cocomplex.d 0 1) φ μ ν
    (fun A g t => by
      change (a.hom.f 0).hom.app A (b.app A (P.1.vadd A g t)) = _
      rw [resolutionPresentationMap_vadd, map_add]
      rfl)
    (fun A g t => by
      change b'.app A (σ.app A (P.1.vadd A g t)) = _
      rw [hσ, resolutionPresentationMap_vadd, ← haug]
      rfl)
    ((a.hom.f 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) s₁) s₁'
    (fun A t => by
      change (J.cocomplex.d 0 1).hom.app A
        ((a.hom.f 0).hom.app A (b.app A t)) = _
      have hc := congrArg (fun k => k.hom.app A) (a.hom.comm 0 1)
      have hh := congrArg (fun k => k (b.app A t)) hc
      change _ = (a.hom.f 1).hom.app A ((I.cocomplex.d 0 1).hom.app A (b.app A t)) at hh
      rw [resolutionPresentationMap_d] at hh
      exact hh.trans (congrArg (fun k => k s₁)
        ((a.hom.f 1).hom.naturality (hT.from A.unop).op)))
    (fun A t => resolutionPresentationMap_d T J Q s' e' A (σ.app A t))
  apply relativeFrameClass_map_eq T U I U J _ _ h _ _ x hd
  exact (hr (op U) P.2)

/-- Pullback of a pointed torsor gives the transfer on relative H1. -/
theorem relativeTorsorEquiv_transfer
    {T T' : Scheme.{u}} (h : T' ⟶ T) (W : T.Opens)
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {G' : Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (f : G ⟶ (lowerStar AddCommGrpCat.{u + 1} h).obj G')
    (I : InjectiveResolution G) (J : InjectiveResolution G')
    (a : I.cocomplex ⟶
      ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
    (ha : I.ι.f 0 ≫ a.f 0 = f ≫ (lowerStar AddCommGrpCat.{u + 1} h).map (J.ι.f 0))
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk W.ι)) (Q : Sheaf.Torsor G')
    (b : P.1.sheaf.obj ⟶ (MorphismProperty.Over.pullback @Etale ⊤ h).op ⋙ Q.sheaf.obj)
    (hb : ∀ A g t, b.app A (P.1.vadd A g t) =
      Q.vadd (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj A.unop))
        (f.hom.app A g) (b.app A t))
    (hsquare : HomologicalComplex.extendMap
        (globalResolutionSectionTransfer h I.cocomplex J.cocomplex a)
        ComplexShape.embeddingUpNat ≫
        relativeSectionRestriction T' (Scheme.Etale.mk (h ⁻¹ᵁ W).ι) J.cocomplex =
      relativeSectionRestriction T (Scheme.Etale.mk W.ι) I.cocomplex ≫
        HomologicalComplex.extendMap
          (openResolutionSectionTransfer h I.cocomplex J.cocomplex a W)
          ComplexShape.embeddingUpNat) :
    HomologicalComplex.homologyMap (relativeFiberMap _ _
        (HomologicalComplex.extendMap
          (globalResolutionSectionTransfer h I.cocomplex J.cocomplex a)
          ComplexShape.embeddingUpNat)
        (HomologicalComplex.extendMap
          (openResolutionSectionTransfer h I.cocomplex J.cocomplex a W)
          ComplexShape.embeddingUpNat) hsquare) 1
        (relativeTorsorEquiv T (Scheme.Etale.mk W.ι) I (Quotient.mk _ P)) =
      relativeTorsorEquiv T' (Scheme.Etale.mk (h ⁻¹ᵁ W).ι) J (Quotient.mk _
        ⟨Q, Q.sheaf.obj.map (openSectionPullback h W).op
          (b.app (op (Scheme.Etale.mk W.ι)) P.2)⟩) := by
  let hT := MorphismProperty.Over.mkIdTerminal @Etale T
  let hT' := MorphismProperty.Over.mkIdTerminal @Etale T'
  let F := lowerStar AddCommGrpCat.{u + 1} h
  let L := MorphismProperty.Over.pullback @Etale ⊤ h
  let U := Scheme.Etale.mk W.ι
  let U' := Scheme.Etale.mk (h ⁻¹ᵁ W).ι
  let : Injective (I.cocomplex.X 0) := I.injective 0
  let : Injective (J.cocomplex.X 0) := J.injective 0
  obtain ⟨s, ⟨e⟩⟩ := Sheaf.Torsor.exists_equiv_lifts hT
    (resolutionLiftSequence_shortExact T I) P.1
  obtain ⟨s', ⟨e'⟩⟩ := Sheaf.Torsor.exists_equiv_lifts hT'
    (resolutionLiftSequence_shortExact T' J) Q
  rw [relativeTorsorEquiv_presentation T U I P s e,
    relativeTorsorEquiv_presentation T' U' J _ s' e']
  let β := resolutionPresentationMap T I P.1 s e
  let β' := resolutionPresentationMap T' J Q s' e'
  let μ : P.1.sheaf.obj ⟶ (F.obj (J.cocomplex.X 0)).obj ⋙
      forget AddCommGrpCat.{u + 1} :=
    β ≫ Functor.whiskerRight (a.f 0).hom (forget AddCommGrpCat.{u + 1})
  let ν : P.1.sheaf.obj ⟶ (F.obj (J.cocomplex.X 0)).obj ⋙
      forget AddCommGrpCat.{u + 1} := b ≫ Functor.whiskerLeft L.op β'
  let φ := I.ι.f 0 ≫ a.f 0
  let s₁ := (I.cocomplex.iCycles 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) s
  let s₁' := (J.cocomplex.iCycles 1).hom.app (op (Scheme.Etale.mk (𝟙 T'))) s'
  let t₁ := (J.cocomplex.X 1).obj.map
    (hT'.from (L.obj (Scheme.Etale.mk (𝟙 T)))).op s₁'
  have haug (A : T.Etaleᵒᵖ) (g : G.obj.obj A) :
      (a.f 0).hom.app A ((I.ι.f 0).hom.app A g) =
        (J.ι.f 0).hom.app (op (L.obj A.unop)) (f.hom.app A g) :=
    congrArg (fun k : G ⟶ F.obj (J.cocomplex.X 0) => k.hom.app A g) ha
  have hconst (A : T.Etaleᵒᵖ) :
      (F.obj (J.cocomplex.X 1)).obj.map (hT.from A.unop).op t₁ =
        (J.cocomplex.X 1).obj.map (hT'.from (L.obj A.unop)).op s₁' := by
    change (J.cocomplex.X 1).obj.map (L.map (hT.from A.unop)).op
      ((J.cocomplex.X 1).obj.map (hT'.from (L.obj (Scheme.Etale.mk (𝟙 T)))).op s₁') = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    exact congrArg (fun k => (J.cocomplex.X 1).obj.map k.op s₁') (hT'.hom_ext _ _)
  obtain ⟨x, hd, hr⟩ := Sheaf.Torsor.difference_of_equivariant_lifts hT P.1
    (F.obj (J.cocomplex.X 0)) (F.obj (J.cocomplex.X 1)) (F.map (J.cocomplex.d 0 1))
    φ μ ν
    (fun A g t => by
      change (a.f 0).hom.app A (β.app A (P.1.vadd A g t)) = _
      rw [resolutionPresentationMap_vadd, map_add]
      rfl)
    (fun A g t => by
      change β'.app (op (L.obj A.unop)) (b.app A (P.1.vadd A g t)) = _
      rw [hb, resolutionPresentationMap_vadd, ← haug]
      rfl)
    ((a.f 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) s₁) t₁
    (fun A t => by
      have hc := congrArg (fun k => k.hom.app A) (a.comm 0 1)
      have hh := congrArg (fun k => k (β.app A t)) hc
      change (J.cocomplex.d 0 1).hom.app (op (L.obj A.unop))
        ((a.f 0).hom.app A (β.app A t)) = _
      change _ = (a.f 1).hom.app A ((I.cocomplex.d 0 1).hom.app A (β.app A t)) at hh
      rw [resolutionPresentationMap_d] at hh
      exact hh.trans (congrArg (fun k => k s₁)
        ((a.f 1).hom.naturality (hT.from A.unop).op)))
    (fun A t => by
      change (J.cocomplex.d 0 1).hom.app (op (L.obj A.unop))
        (β'.app (op (L.obj A.unop)) (b.app A t)) = _
      rw [resolutionPresentationMap_d, hconst])
  let x' := (J.cocomplex.X 0).obj.map (terminalSectionPullback h).op x
  apply relativeFrameClass_map_eq T U I U' J _ _ hsquare _ _ x'
  · have hh := congrArg ((J.cocomplex.X 1).obj.map (terminalSectionPullback h).op) hd
    change (J.cocomplex.X 1).obj.map (terminalSectionPullback h).op
      ((J.cocomplex.d 0 1).hom.app (op (L.obj (Scheme.Etale.mk (𝟙 T)))) x) = _ at hh
    erw [← ConcreteCategory.comp_apply, ← (J.cocomplex.d 0 1).hom.naturality,
      ConcreteCategory.comp_apply, map_sub] at hh
    have ht : (J.cocomplex.X 1).obj.map (terminalSectionPullback h).op t₁ = s₁' := by
      dsimp only [t₁]
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      have hid : terminalSectionPullback h ≫
          hT'.from (L.obj (Scheme.Etale.mk (𝟙 T))) = 𝟙 _ := hT'.hom_ext _ _
      rw [hid, op_id]
      erw [CategoryTheory.Functor.map_id]
      rfl
    rw [ht] at hh
    exact hh
  · have hh := congrArg ((J.cocomplex.X 0).obj.map (openSectionPullback h W).op)
      (hr (op U) P.2)
    change (J.cocomplex.X 0).obj.map (openSectionPullback h W).op
      ((J.cocomplex.X 0).obj.map (L.map (hT.from U)).op x) = _ at hh
    have hs : hT'.from U' ≫ terminalSectionPullback h =
        openSectionPullback h W ≫ L.map (hT.from U) := by
      have h₁ : hT.from U = MorphismProperty.Over.homMk W.ι (Category.comp_id _) :=
        hT.hom_ext _ _
      have h₂ : hT'.from U' =
          MorphismProperty.Over.homMk (h ⁻¹ᵁ W).ι (Category.comp_id _) := hT'.hom_ext _ _
      rw [h₁, h₂]
      exact terminalSectionPullback_naturality h W
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, ← hs,
      op_comp, Functor.map_comp, ConcreteCategory.comp_apply, map_sub] at hh
    have hn := ConcreteCategory.congr_hom (β'.naturality (openSectionPullback h W).op)
      (b.app (op U) P.2)
    change β'.app (op U') (Q.sheaf.obj.map (openSectionPullback h W).op
      (b.app (op U) P.2)) =
      (J.cocomplex.X 0).obj.map (openSectionPullback h W).op
        (β'.app (op (L.obj U)) (b.app (op U) P.2)) at hn
    change (J.cocomplex.X 0).obj.map (hT'.from U').op x' =
      (J.cocomplex.X 0).obj.map (openSectionPullback h W).op
        (β'.app (op (L.obj U)) (b.app (op U) P.2)) -
      (J.cocomplex.X 0).obj.map (openSectionPullback h W).op
        ((a.f 0).hom.app (op U) (β.app (op U) P.2)) at hh
    erw [← hn] at hh
    exact hh

end AlgebraicGeometry.Etale

-- Check the axioms of the completed construction.
