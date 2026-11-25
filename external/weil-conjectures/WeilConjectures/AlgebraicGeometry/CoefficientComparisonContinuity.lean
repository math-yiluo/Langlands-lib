/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ClassicalContinuityMap
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonPresentationSheafification
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonRepresentableContinuity

/-! # Affine continuity of coefficient-sized etale inverse images

Source: blueprint continuity-map detail and Stacks Project, proetale.tex,
lemma-limit-pullback (Tag 099S), and its affine section formula.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

private def presentationEtaleDiagram {X : Scheme.{u}}
    {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
    (P : AffinePresentation X I) : I ⥤ Scheme.smallModelComparisonEtaleSite.{u, v} X :=
  let D : I ⥤ X.Etale :=
    { obj i := @Scheme.Etale.mk _ _ (P.diagram.obj i).hom (P.etale i)
      map f := MorphismProperty.Over.homMk (P.diagram.map f).left
        (MorphismProperty.Over.w _) trivial }
  D ⋙ AsSmall.up

private def presentationDiagramIso {X : Scheme.{u}}
    {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
    (P : AffinePresentation X I) :
    presentationEtaleDiagram.{u, v} P ⋙ Scheme.smallModelComparisonInclusion.{u, v} X ≅
      P.diagram ⋙ AsSmall.up :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro i j f; rfl)

private def presentationModelIsLimit {X : Scheme.{u}}
    {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
    (P : AffinePresentation X I) :
    IsLimit ((AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).mapCone
      P.cone) := by
  let _ : (AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).IsRightAdjoint :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).symm.isRightAdjoint_inverse
  exact isLimitOfPreserves _ (isLimitOfReflects (Scheme.ProEt.forget X) P.isLimit)

private def presentationLanColimit {X : Scheme.{u}}
    (A : Type (max v (u + 1))) [CommRing A]
    (G : Sheaf (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A))
    {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
    (P : AffinePresentation X I)
    (hrep : ∀ V : (Scheme.smallModelComparisonEtaleSite.{u, v} X)ᵒᵖ,
      PreservesColimit (P.diagram ⋙ AsSmall.up).op
        (coyoneda.obj (op ((Scheme.smallModelComparisonInclusion.{u, v} X).op.obj V)))) :
    IsColimit (((Scheme.smallModelComparisonInclusion.{u, v} X).op.lan.obj G.obj).mapCocone
      ((AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).mapCone
        P.cone).op) := by
  let B := Scheme.smallModelComparisonInclusion.{u, v} X
  let E := presentationEtaleDiagram.{u, v} P
  let e := presentationDiagramIso.{u, v} P
  let hpres (V : (Scheme.smallModelComparisonEtaleSite.{u, v} X)ᵒᵖ) :
      PreservesColimit (E.op ⋙ B.op) (coyoneda.obj (op (B.op.obj V))) := by
    let _ := hrep V
    exact preservesColimit_of_iso_diagram _ (NatIso.op e)
  let _ : (AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, v} X ⥤
      X.Etale).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).isEquivalence_inverse
  let _ : (AsSmall.up : X.ProEt ⥤
      Scheme.coefficientProEtaleSiteModel.{u, v} X).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).symm.isEquivalence_inverse
  have : B.op.Full := inferInstance
  have : B.op.Faithful := inferInstance
  have : ∀ (H : (Scheme.smallModelComparisonEtaleSite.{u, v} X)ᵒᵖ ⥤
      ModuleCat.{max v (u + 1)} A), B.op.HasPointwiseLeftKanExtension H := by
    intro H
    infer_instance
  have : PreservesColimit (E ⋙ B).op (B.op.leftKanExtension G.obj) :=
    inferInstanceAs (PreservesColimit (E.op ⋙ B.op) (B.op.leftKanExtension G.obj))
  have : PreservesColimit (P.diagram ⋙ AsSmall.up).op
      (B.op.leftKanExtension G.obj) :=
    preservesColimit_of_iso_diagram (B.op.leftKanExtension G.obj) (NatIso.op e).symm
  change IsColimit ((B.op.leftKanExtension G.obj).mapCocone _)
  exact isColimitOfPreserves _ (presentationModelIsLimit.{u, v} P).op

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The restriction cocone of an etale inverse image is a colimit on every
specified affine etale presentation. No finite-generation hypothesis is needed.

Source: blueprint det-pe-classical-definition-continuity-map and the affine
comparison section formula; Stacks Project, Tag 099S, lemma-limit-pullback
(auxiliary; not a blueprint node).

Proof: before sheafification inverse image is the left Kan extension along the
opposite inclusion of etale objects. Maps from an affine cofiltered scheme limit
to an etale scheme factor through a stage, and equalities of maps are detected at
a later stage, by local finite presentation. This says the representables used
in the Kan extension turn the given limit into a colimit. The colimit expression
for Kan extension then gives the same assertion for every module presheaf.
For an etale sheaf this Kan extension is already a sheaf on the affine ind-etale
basis, by descent of coverings and their finite intersections to finite stages.
Thus the sheafification unit is invertible on every stage and on the vertex.
Naturality transports the colimit cocone to the sheafified inverse image. These
are exactly the projection restriction maps in sectionCocone. AsSmall changes
neither the objects nor the projections; uniqueness of comparison left adjoints
identifies the transported construction with the displayed functor. The argument
works for index size u+1 by the same finite-presentation factorization argument:
a map and an equality involve finitely much algebraic data, hence occur at a stage
of the original filtered diagram. One may compute the affine-basis sheafification
using a small ind-etale presentation (lem-pe-ind-etale-small-index); naturality of
the Kan-extension formula then gives the original projection cocone. No claim
that index shrinking itself supplies a cofinal functor is needed. Colimits of modules
exist in the coefficient universe and preserve the scalar action. The zero sheaf
and the empty affine scheme give the zero colimit by the same argument. -/
theorem coefficientFixedComparison_isColimit (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (G : Sheaf (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A))
    {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
    (P : AffinePresentation X I) :
    Nonempty (IsColimit (sectionCocone P
      ((AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).op ⋙
        ((Functor.sheafPullbackConstruction.sheafPullback
          (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
          (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
          (Scheme.coefficientProEtaleModelTopology.{u, v} X)).obj G).obj))) := by
  let B := Scheme.smallModelComparisonInclusion.{u, v} X
  let L := B.op.lan.obj G.obj
  let K := Scheme.coefficientProEtaleModelTopology.{u, v} X
  let η := toSheafify K L
  let c := (AsSmall.up : X.ProEt ⥤
    Scheme.coefficientProEtaleSiteModel.{u, v} X).mapCone P.cone
  obtain ⟨hvertex, hstage⟩ := coefficientComparison_presentation_toSheafify_isIso X A G P
  have : IsIso (η.app c.op.pt) := hvertex
  have (i : Iᵒᵖ) : IsIso (η.app ((P.diagram ⋙ AsSmall.up).op.obj i)) := hstage i.unop
  have hL := presentationLanColimit A G P
    (coefficientComparison_representable_preservesColimit X P)
  have h := isColimitMapCoconeOfNatTrans L (sheafify K L) η c.op hL
  exact ⟨h⟩

end AlgebraicGeometry.ProEtale
