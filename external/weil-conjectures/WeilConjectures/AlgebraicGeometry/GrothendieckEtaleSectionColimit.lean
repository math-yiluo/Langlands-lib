/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.GrothendieckHypercoverStageMaps
import WeilConjectures.AlgebraicGeometry.GrothendieckEtaleRelativeSectionColimit
import WeilConjectures.SixFunctors.BaseChange.Pasting
/-! # Coherent-site continuity with Grothendieck coefficients -/
@[expose] public section
universe u' u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.FiniteSplitEtaleHypercover
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
variable {S : Scheme.{u}} {I : Type u} [SmallCategory I] (D : I ⥤ Over S)
  [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]
  (c : Cone D) [CompactSpace c.pt.left] [QuasiSeparatedSpace c.pt.left]

/-- Restrict the later-stage coefficients to the étale site of a fixed stage. -/
noncomputable def tailSections (F : Sheaf S.smallEtaleTopology A) (i : I)
    (j : Over i) : (D.obj i).left.Etaleᵒᵖ ⥤ A :=
  (D.map j.hom).left.Etale.op ⋙ ((Etale.upperStar A (D.obj j.left).hom).obj F).obj

/-- The canonical unit and pasting map to sections over the limit scheme. -/
noncomputable def tailSectionMap (F : Sheaf S.smallEtaleTopology A) (i : I)
    (j : Over i) : tailSections A D F i j ⟶
      (coneProjection D c i).Etale.op ⋙ ((Etale.upperStar A c.pt.hom).obj F).obj :=
  Functor.whiskerLeft (D.map j.hom).left.Etale.op
      ((Etale.upperStarLowerStarAdjunction A (coneProjection D c j.left)).unit.app
        ((Etale.upperStar A (D.obj j.left).hom).obj F)).hom ≫
    Functor.whiskerLeft
      ((D.map j.hom).left.Etale ⋙ (coneProjection D c j.left).Etale).op
      (coneCoefficientMap A D c F j.left).hom ≫
    Functor.whiskerRight (NatTrans.op
      (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
        (coneProjection D c j.left) (D.map j.hom).left (coneProjection D c i)
        (congrArg (fun t ↦ t.left) (c.w j.hom)).symm).hom)
      ((Etale.upperStar A c.pt.hom).obj F).obj

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Sections on a descended qcqs étale object form the canonical filtered colimit.
Source: blueprint étale cohomology continuity, detailed proof paragraph 2, and
Stacks Project, Étale Cohomology, Tag 09YQ; the coefficient-category generalization
uses finite-limit exactness of filtered colimits.

Proof: the over category of i is cofiltered and its forgetful functor is initial,
so the restricted cone is still limiting. Form the presheaf diagram with objects
(j→i)_* F_j; for a morphism k→j its map is the inverse-image unit for D_k→D_j,
followed by the inverse-image composition isomorphism and pullback pasting. The
unit equation and associativity of these isomorphisms prove the functor laws and
naturality of the displayed limit comparison, giving P, e and ν.

Restrict all sites to the qcqs finite-presentation étale basis. Descent of étale
objects, maps, their equalities, and finite covering families identifies the
limit basis with the filtered colimit of the stage bases. The inverse-image
presheaf on this basis is therefore the pointwise filtered colimit. To see that
it is already a sheaf, refine a cover of a qcqs object to a finite cover. Its
matching diagram consists of a finite product of section objects and a finite
product over overlaps; the overlaps are qcqs. AB5 commutes the filtered colimit
with the finite equalizer describing matching families. Thus the pointwise
colimit satisfies the sheaf condition on the basis. The universal property of
inverse image identifies it with the restriction of the limit sheaf. The unit
normalization makes the colimit legs exactly tailSectionMap. This construction
is natural in the étale object. An empty cover gives the terminal, hence zero,
section object, so empty schemes and empty étale objects are included.
(auxiliary; not a blueprint node) -/
theorem exists_tail_section_colimit
    [IsCofiltered I] [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g).left]
    (F : Sheaf S.smallEtaleTopology A)
    (hc : IsLimit ((Over.forget S).mapCone c)) (i : I) :
    ∃ (P : (Over i)ᵒᵖ ⥤ ((D.obj i).left.Etaleᵒᵖ ⥤ A))
      (e : ∀ j, P.obj j ≅ tailSections A D F i j.unop)
      (ν : P ⟶ (Functor.const (Over i)ᵒᵖ).obj
        ((coneProjection D c i).Etale.op ⋙ ((Etale.upperStar A c.pt.hom).obj F).obj)),
      (∀ j, ν.app j = (e j).hom ≫ tailSectionMap A D c F i j.unop) ∧
        ∀ (U : (D.obj i).left.Etale), CompactSpace U.left → QuasiSeparatedSpace U.left →
          Nonempty (IsColimit (((evaluation _ A).obj (op U)).mapCocone
            (Cocone.mk _ ν))) := by
  let E := D ⋙ Over.forget S
  let c' := (Over.forget S).mapCone c
  have : ∀ j, CompactSpace (E.obj j) := fun j ↦ inferInstanceAs
    (CompactSpace (D.obj j).left)
  have : ∀ j, QuasiSeparatedSpace (E.obj j) := fun j ↦ inferInstanceAs
    (QuasiSeparatedSpace (D.obj j).left)
  have : ∀ {j k} (a : j ⟶ k), IsAffineHom (E.map a) := fun a ↦ inferInstanceAs
    (IsAffineHom (D.map a).left)
  have : CompactSpace c'.pt := inferInstanceAs (CompactSpace c.pt.left)
  have : QuasiSeparatedSpace c'.pt := inferInstanceAs (QuasiSeparatedSpace c.pt.left)
  let G := (Etale.upperStar A (D.obj i).hom).obj F
  let P := Etale.relativeSectionDiagram A E i G
  let s := Etale.relativeSectionCocone A E c' i G
  let e (j : (Over i)ᵒᵖ) : P.obj j ≅ tailSections A D F i j.unop :=
    Functor.isoWhiskerLeft (D.map j.unop.hom).left.Etale.op
      ((sheafToPresheaf _ A).mapIso
        ((Etale.upperStarComp A (D.map j.unop.hom).left (D.obj i).hom
          (D.obj j.unop.left).hom (Over.w (D.map j.unop.hom)).symm).symm.app F))
  let eL : s.pt ≅ (coneProjection D c i).Etale.op ⋙
      ((Etale.upperStar A c.pt.hom).obj F).obj :=
    Functor.isoWhiskerLeft (coneProjection D c i).Etale.op
      ((sheafToPresheaf _ A).mapIso
        ((Etale.upperStarComp A (coneProjection D c i) (D.obj i).hom
          c.pt.hom (Over.w (c.π.app i)).symm).symm.app F))
  let ν := s.ι ≫ (Functor.const _).map eL.hom
  refine ⟨P, e, ν, ?_, ?_⟩
  · intro j
    ext U
    have hn := NatTrans.congr_app (congrArg (fun t ↦ t.hom)
      ((Etale.upperStarLowerStarAdjunction A (coneProjection D c j.unop.left)).unit.naturality
        ((Etale.upperStarComp A (D.map j.unop.hom).left (D.obj i).hom
          (D.obj j.unop.left).hom (Over.w (D.map j.unop.hom)).symm).inv.app F)))
            (op ((D.map j.unop.hom).left.Etale.obj U.unop))
    have hc' := NatTrans.congr_app (Etale.upperStarComp_assoc' A
      (coneProjection D c j.unop.left) (D.map j.unop.hom).left (D.obj i).hom
      (coneProjection D c i) (D.obj j.unop.left).hom c.pt.hom
      (congrArg (fun t ↦ t.left) (c.w j.unop.hom)).symm
      (Over.w (D.map j.unop.hom)).symm (Over.w (c.π.app i)).symm) F
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_obj] at hc'
    have he :
        ((Etale.upperStarComp A (coneProjection D c j.unop.left)
          (D.obj j.unop.left).hom c.pt.hom (Over.w (c.π.app j.unop.left)).symm).app F ≪≫
          (Etale.upperStar A (coneProjection D c j.unop.left)).mapIso
            ((Etale.upperStarComp A (D.map j.unop.hom).left (D.obj i).hom
              (D.obj j.unop.left).hom (Over.w (D.map j.unop.hom)).symm).app F)) =
        ((Etale.upperStarComp A (coneProjection D c i) (D.obj i).hom c.pt.hom
          (Over.w (c.π.app i)).symm).app F ≪≫
          (Etale.upperStarComp A (coneProjection D c j.unop.left) (D.map j.unop.hom).left
            (coneProjection D c i)
            (congrArg (fun t ↦ t.left) (c.w j.unop.hom)).symm).app G) := Iso.ext hc'
    have hi := congrArg Iso.inv he
    simp only [Iso.trans_inv, Functor.mapIso_inv] at hi
    have hci := NatTrans.congr_app (congrArg (fun t ↦ t.hom) hi)
      (op ((coneProjection D c j.unop.left).Etale.obj
        ((D.map j.unop.hom).left.Etale.obj U.unop)))
    have hl := (((Etale.upperStarComp A (coneProjection D c i) (D.obj i).hom
      c.pt.hom (Over.w (c.π.app i)).symm).inv.app F).hom.naturality
        ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
          (coneProjection D c j.unop.left) (D.map j.unop.hom).left
          (coneProjection D c i)
          (congrArg (fun t ↦ t.left) (c.w j.unop.hom)).symm).hom.app U.unop).op)
    dsimp [ν, e, eL, s, Etale.relativeSectionCocone, Etale.grothendieckRelativeSectionMap,
      tailSectionMap, coneCoefficientMap]
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hn hci
    simp only [Category.assoc]
    erw [reassoc_of% hn, reassoc_of% hci]
    exact congrArg (fun t ↦
      ((Etale.upperStarLowerStarAdjunction A (coneProjection D c j.unop.left)).unit.app
        ((Etale.upperStar A (D.map j.unop.hom).left).obj G)).hom.app
          (op ((D.map j.unop.hom).left.Etale.obj U.unop)) ≫
      ((Etale.upperStarComp A (coneProjection D c j.unop.left) (D.map j.unop.hom).left
        (coneProjection D c i)
        (congrArg (fun t ↦ t.left) (c.w j.unop.hom)).symm).inv.app G).hom.app
          (op ((coneProjection D c j.unop.left).Etale.obj
            ((D.map j.unop.hom).left.Etale.obj U.unop))) ≫ t) hl
  · intro U hU hU'
    have := hU
    have := hU'
    obtain ⟨hs⟩ := Etale.relativeSectionCocone_isColimit A E c' hc i G U
    exact ⟨IsColimit.ofIsoColimit hs
      (Cocone.ext (((evaluation _ A).obj (op U)).mapIso eL) (fun j ↦ by
        rfl))⟩

end AlgebraicGeometry.FiniteSplitEtaleHypercover
