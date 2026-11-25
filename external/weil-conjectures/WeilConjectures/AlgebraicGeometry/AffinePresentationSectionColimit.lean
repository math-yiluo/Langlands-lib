/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ClassicalContinuityMap
import WeilConjectures.AlgebraicGeometry.AffineEtaleLargeLimitMaps
import WeilConjectures.RingTheory.IndEtaleSmallIndex
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful

/-! # Continuity on affine presentations with a larger index

Source: Bhatt--Scholze, Lemma 5.1.1, and the universe reduction in the
continuity-map definition of classical sheaves.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

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

private theorem affineEtale_smallLimit_preservesColimit {X : Scheme.{u}}
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ X.ProEt) (haff : ∀ j, IsAffine (D.obj j).left)
    (c : Cone D) (hc : IsLimit ((Scheme.ProEt.forget X).mapCone c))
    (V : X.ProEt) [Etale V.hom] :
    PreservesColimit D.op (coyoneda.obj (op (op V))) := by
  let D' := D ⋙ Scheme.ProEt.forget X
  have (j : J) : IsAffine (D'.obj j).left := haff j
  have {i j : J} (f : i ⟶ j) : IsAffineHom (D'.map f).left := by
    dsimp [D']
    infer_instance
  have (j : J) : CompactSpace (D'.obj j).left := inferInstance
  have (j : J) : QuasiSeparatedSpace (D'.obj j).left := inferInstance
  have : LocallyOfFinitePresentation ((Scheme.ProEt.forget X).obj V).hom :=
    inferInstanceAs (LocallyOfFinitePresentation V.hom)
  have := Scheme.preservesColimit_yoneda D' ((Scheme.ProEt.forget X).obj V)
  have hyon : IsColimit
      ((yoneda.obj ((Scheme.ProEt.forget X).obj V)).mapCocone
        ((Scheme.ProEt.forget X).mapCone c).op) := isColimitOfPreserves _ hc.op
  have hy : IsColimit ((yoneda.obj V).mapCocone c.op) :=
    IsColimit.mapCoconeEquiv (Scheme.ProEt.forgetOpCompYonedaIso V) (by exact hyon)
  have hco : IsColimit ((coyoneda.obj (op (op V))).mapCocone c.op) :=
    IsColimit.mapCoconeEquiv (Coyoneda.objOpOp _).symm hy
  exact preservesColimit_of_preserves_colimit_cocone
    (isLimitOfReflects (Scheme.ProEt.forget X) hc).op hco

/-- Small filtered continuity on the affine ind-etale site gives the actual section
colimit for every affine etale presentation in the site universe.

Source: Bhatt--Scholze, Lemma 5.1.1; the final paragraph of the blueprint's
continuity-map definition (auxiliary; not a blueprint node).

Proof: First work over an affine stage of the presentation, by restriction to the
cofiltered over-category of that stage. Global sections turn the given affine
limit into a filtered ring colimit. Finite presentation of etale algebras implies
that maps to every affine etale object factor through a stage, and equality of two
such maps is detected at a later stage. This argument uses only finitely many
algebra generators and relations, and hence also works for the larger index.
The small-index theorem for ind-etale algebras supplies a universe-u etale
presentation Q of the same vertex. Its section cocone is a colimit by the
hypothesis. Maps from the vertex to every stage of Q factor through the original
presentation, so each section on Q comes from an original stage. Conversely,
sections from two original stages which agree on the vertex agree after passing
to a stage of Q. Factor its projection through an original stage; eventual
equality of maps to the two original etale stages, supplied by finite
presentation, makes the two sections equal at a common original stage. Thus the
canonical section map is surjective and injective. The filtered-colimit
criterion for sets identifies this with the stated colimit cocone. Working over
an affine stage and composing its structure morphism back to X gives the same
restriction maps, so the argument applies to an arbitrary base scheme. Empty
spectra and zero rings are included in the ring-colimit and finite-presentation
arguments; a cofiltered category is nonempty. -/
theorem affinePresentation_sectionCocone_isColimit {X : Scheme.{u}}
    (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (hF : PreservesFilteredColimitsOfSize.{u, u}
      ((Scheme.AffineProEt.toProEt X).op ⋙ F.obj))
    {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
    (P : AffinePresentation X I) :
    Nonempty (IsColimit (sectionCocone P F.obj)) := by
  let := hF
  let U : X.AffineProEt :=
    Scheme.AffineProEt.mk P.cone.pt.hom (presentationVertexProAffineEtale P)
  obtain ⟨J, _, _, ⟨p⟩⟩ := U.exists_relativeLimitPresentation
  let T := Scheme.AffineProEt.toProEt X
  let Q := (p.diag ⋙ Scheme.AffineEtale.toAffineProEt X) ⋙ T
  have hQa (j : J) : IsAffine (Q.obj j).left :=
    inferInstanceAs (IsAffine
      ((Scheme.AffineEtale.toAffineProEt X).obj (p.diag.obj j)).left)
  have hQe (j : J) : Etale (Q.obj j).hom :=
    inferInstanceAs (Etale
      ((Scheme.AffineEtale.toAffineProEt X).obj (p.diag.obj j)).hom)
  let d := T.mapCone p.cone
  have hd : IsLimit ((Scheme.ProEt.forget X).mapCone d) := by
    apply isLimitOfReflects (Over.forget X)
    exact ((Scheme.AffineProEt.isLimitMapConeToSchemeOfIsLimit p.cone p.isLimit).ofIsoLimit
      (Functor.mapConeMapCone p.cone).symm).ofIsoLimit (Functor.mapConeMapCone d).symm
  have hdF : IsColimit (F.obj.mapCocone d.op) := by
    exact isColimitOfPreserves (T.op ⋙ F.obj) p.isLimit.op
  let E : ObjectProperty X.ProEt := fun V ↦ IsAffine V.left ∧ Etale V.hom
  let L := E.ι.op
  let K := (E.lift P.diagram (fun i ↦ ⟨P.affine i, P.etale i⟩)).op
  let K' := (E.lift Q (fun j ↦ ⟨hQa j, hQe j⟩)).op
  let hP (V : E.FullSubcategoryᵒᵖ) :
      PreservesColimit (K ⋙ L) (coyoneda.obj (op (L.obj V))) := by
    have : IsAffine V.unop.obj.left := V.unop.property.1
    have : Etale V.unop.obj.hom := V.unop.property.2
    exact affineEtale_largeLimit_preservesColimit P.diagram P.affine P.etale
      P.cone P.isLimit V.unop.obj
  let hQ (V : E.FullSubcategoryᵒᵖ) :
      PreservesColimit (K' ⋙ L) (coyoneda.obj (op (L.obj V))) := by
    have : IsAffine V.unop.obj.left := V.unop.property.1
    have : Etale V.unop.obj.hom := V.unop.property.2
    exact affineEtale_smallLimit_preservesColimit Q hQa
      d hd V.unop.obj
  let A := CostructuredArrow.lift K (L := L) P.cone.op.ι
  let B := CostructuredArrow.lift K' (L := L) d.op.ι
  have : A.Final := final_costructuredArrowLift_of_isFinitelyPresentable L K
    (isLimitOfReflects (Scheme.ProEt.forget X) P.isLimit).op
  have : B.Final := final_costructuredArrowLift_of_isFinitelyPresentable L K'
    (isLimitOfReflects (Scheme.ProEt.forget X) hd).op
  let cc : Cocone (CostructuredArrow.proj L (op P.cone.pt) ⋙ L ⋙ F.obj) :=
    { pt := F.obj.obj (op P.cone.pt)
      ι :=
        { app V := F.obj.map V.hom
          naturality {V W} f := by
            dsimp
            rw [Category.comp_id, ← F.obj.map_comp]
            exact congrArg F.obj.map f.w } }
  have hcc : IsColimit cc := Functor.Final.isColimitWhiskerEquiv B cc hdF
  exact ⟨(Functor.Final.isColimitWhiskerEquiv A cc).symm hcc⟩

end AlgebraicGeometry.ProEtale
