/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSmallGenerator
import Mathlib.Algebra.Category.Grp.LargeColimits

/-! Auxiliary cardinal bound for the concrete etale generator.
(blueprint: lem-sc-etale-small-generator-sections-surjective)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- An abelian-group colimit is a quotient of the small direct sum of its values. -/
private theorem small_colimit {I : Type u} [Category.{u} I]
    (F : I ⥤ AddCommGrpCat.{u + 1}) [HasColimit F]
    (h : ∀ i, Small.{u} (F.obj i)) : Small.{u} ↥(colimit F) := by
  classical
  let _ (i : I) : Small.{u} (F.obj i) := h i
  have : Small.{u} (AddCommGrpCat.Colimits.Quot F) :=
    small_of_surjective (QuotientAddGroup.mk'_surjective _)
  exact small_of_surjective
    ((AddCommGrpCat.isColimit_iff_bijective_desc (colimit.cocone F)).mp
      ⟨colimit.isColimit F⟩).2

/-- Matching families form a small type; every plus section has a matching-family representative. -/
private theorem small_plus {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (h : ∀ V, Small.{u} (P.obj V)) (V : Cᵒᵖ) :
    Small.{u} ((J.plusObj P).obj V) := by
  classical
  let : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let _ (W : Cᵒᵖ) : Small.{u} (P.obj W) := h W
  let f : (Σ S : J.Cover V.unop, Meq P S) → ((J.plusObj P).obj V) :=
    fun x ↦ GrothendieckTopology.Plus.mk x.2
  have (S : J.Cover V.unop) : Small.{u} (Meq P S) := by
    unfold Meq
    infer_instance
  exact small_of_surjective (f := f) (by
    intro x
    obtain ⟨S, y, hy⟩ := GrothendieckTopology.Plus.exists_rep x
    exact ⟨⟨S, y⟩, hy.symm⟩)

/-- Apply the plus bound twice and use uniqueness of the sheafification left adjoint. -/
private theorem small_sheafify {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (h : ∀ V, Small.{u} (P.obj V)) (V : Cᵒᵖ) :
    Small.{u} ((sheafify J P).obj V) := by
  let : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : Small.{u} ((J.sheafify P).obj V) :=
    small_plus J _ (small_plus J P h) V
  let i := (plusPlusIsoSheafify J AddCommGrpCat P).app V
  exact small_map i.addCommGroupIsoToAddEquiv.toEquiv.symm

/-- Compute a sheaf colimit by sheafifying the pointwise presheaf colimit. -/
private theorem small_sheaf_colimit {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    {I : Type u} [SmallCategory I] (F : I ⥤ Sheaf J AddCommGrpCat.{u + 1})
    (h : ∀ i V, Small.{u} ((F.obj i).obj.obj V)) (V : Cᵒᵖ) :
    Small.{u} ((colimit F).obj.obj V) := by
  let P := F ⋙ sheafToPresheaf J AddCommGrpCat.{u + 1}
  have hP (W : Cᵒᵖ) : Small.{u} ((colimit P).obj W) := by
    have : Small.{u} ↥(colimit (P ⋙ (CategoryTheory.evaluation _ _).obj W)) :=
      small_colimit _ (fun i ↦ h i W)
    exact small_map (colimitObjIsoColimitCompEvaluation P W).addCommGroupIsoToAddEquiv.toEquiv
  have : Small.{u} ((Sheaf.sheafifyCocone (F := F) (colimit.cocone P)).pt.obj.obj V) := by
    change Small.{u} ((sheafify J (colimit P)).obj V)
    exact small_sheafify J _ hP V
  let e := (colimit.isColimit F).coconePointUniqueUpToIso
    (Sheaf.isColimitSheafifyCocone (F := F) (colimit.cocone P) (colimit.isColimit P))
  let eV := ((sheafToPresheaf J AddCommGrpCat.{u + 1}).mapIso e).app V
  exact @small_map _ _ this eV.addCommGroupIsoToAddEquiv.toEquiv

/-- Free Yoneda is a small coproduct followed by sheafification. -/
private theorem small_freeYoneda {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    (c : C) (M : AddCommGrpCat.{u + 1}) [Small.{u} M] (V : Cᵒᵖ) :
    Small.{u} ((Sheaf.freeYoneda J c M).obj.obj V) := by
  apply small_sheafify
  intro W
  exact small_colimit _ (fun _ ↦ show Small.{u} M from inferInstance)

/-- A section is detected by its restrictions to the objects of the small dense site. -/
private theorem small_dense_extension {C : Type u} [SmallCategory C]
    {D : Type (u + 1)} [Category.{u} D] (K : GrothendieckTopology D)
    (G : C ⥤ D) [G.IsCoverDense K] (F : Sheaf K AddCommGrpCat.{u + 1})
    (h : ∀ c, Small.{u} (F.obj.obj (Opposite.op (G.obj c)))) (V : Dᵒᵖ) :
    Small.{u} (F.obj.obj V) := by
  let _ (c : C) : Small.{u} (F.obj.obj (Opposite.op (G.obj c))) := h c
  let f : F.obj.obj V → ∀ c : C, (G.obj c ⟶ V.unop) →
      F.obj.obj (Opposite.op (G.obj c)) := fun s c g ↦ F.obj.map g.op s
  apply small_of_injective (f := f)
  intro s t hst
  apply Functor.IsCoverDense.ext G
    ((sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F) V.unop
  intro c g
  exact congr_fun (congr_fun hst c) g

/-- Index restrictions by a small model, then use cover-density to detect sections. -/
private theorem small_dense_extension_essentiallySmall
    {B D : Type (u + 1)} [Category.{u} B] [Category.{u} D]
    [EssentiallySmall.{u} B] (K : GrothendieckTopology D)
    (G : B ⥤ D) [G.IsCoverDense K] (F : Sheaf K AddCommGrpCat.{u + 1})
    (h : ∀ b, Small.{u} (F.obj.obj (Opposite.op (G.obj b)))) (V : Dᵒᵖ) :
    Small.{u} (F.obj.obj V) := by
  let e := equivSmallModel.{u} B
  let _ (b : B) : Small.{u} (F.obj.obj (Opposite.op (G.obj b))) := h b
  let f : F.obj.obj V → ∀ c : SmallModel.{u} B,
      (G.obj (e.inverse.obj c) ⟶ V.unop) → F.obj.obj (Opposite.op (G.obj (e.inverse.obj c))) :=
    fun s c g ↦ F.obj.map g.op s
  apply small_of_injective (f := f)
  intro s t hst
  apply Functor.IsCoverDense.ext G
    ((sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F) V.unop
  intro b g
  have hi := congr_fun (congr_fun hst (e.functor.obj b))
    (G.map (e.unitIso.app b).inv ≫ g)
  change F.obj.map (G.map (e.unitIso.app b).inv ≫ g).op s =
    F.obj.map (G.map (e.unitIso.app b).inv ≫ g).op t at hi
  have hi' := congrArg (fun z ↦ F.obj.map (G.map (e.unitIso.app b).hom).op z) hi
  change F.obj.map g.op s = F.obj.map g.op t
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← F.obj.map_comp, ← op_comp, ← Category.assoc, ← G.map_comp,
    Iso.hom_inv_id, G.map_id, Category.id_comp] at hi'
  exact hi'

/-- The section type of the concrete generator is a quotient of a u-small type.
Source: Stacks Project, Tags 00W1 and 01DO; Mathlib's concrete plus construction
and dense-subsite comparison.
(blueprint: lem-sc-etale-small-generator-sections-surjective)

Proof: An abelian-group colimit is a quotient of the direct sum of its values,
so small diagrams of small groups have small colimits. On the small model,
matching families and the set of covers are u-small. Every plus section is
represented by a matching family, so plus preserves pointwise smallness.
Apply this twice and compare with the chosen sheafification by uniqueness of
left adjoints. Thus free-Yoneda sheaves and their small coproduct have small
sections. The unit isomorphisms of the two comparison equivalences identify
restrictions of the transported generator with these sections. Cover-density
makes restriction into the product over model objects and maps injective;
this product is u-small. Finally, the inverse of `equivShrink` is the required
surjection. Empty objects and empty covering families need no separate choice:
the matching-family and restriction products also include these cases.
-/
theorem etaleSmallGenerator_sections_surjective (X : Scheme.{u}) (U : X.Etaleᵒᵖ) :
    ∃ α : Type u, ∃ f : α → ((etaleSmallGenerator X).obj.obj U),
      Function.Surjective f := by
  let C := SmallModel.{u} X.AffineEtale
  let e := equivSmallModel.{u} X.AffineEtale
  let J := e.inverse.inducedTopology (AffineEtale.topology X)
  let : HasSheafify J AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_of_essentiallySmall AddCommGrpCat.{u + 1} J
  let : HasColimitsOfSize.{u, u} AddCommGrpCat.{u + 1} :=
    hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  let : HasColimitsOfSize.{u, u} (Sheaf J AddCommGrpCat.{u + 1}) :=
    Sheaf.instHasColimitsOfSize
  let Q : C × Unit → Sheaf J AddCommGrpCat.{u + 1} :=
    fun (⟨c, _⟩ : C × Unit) ↦ Sheaf.freeYoneda J c (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let : HasColimitsOfShape (Discrete (C × Unit)) (Sheaf J AddCommGrpCat.{u + 1}) :=
    HasColimitsOfSize.has_colimits_of_shape (C := Sheaf J AddCommGrpCat.{u + 1}) _
  let : HasColimit (Discrete.functor Q) := HasColimitsOfShape.has_colimit _
  let G := ∐ Q
  let e₁ := e.inverse.sheafInducedTopologyEquivOfIsCoverDense
    (AffineEtale.topology X) AddCommGrpCat.{u + 1}
  let e₂ := (AffineEtale.Spec X).sheafInducedTopologyEquivOfIsCoverDense
    X.smallEtaleTopology AddCommGrpCat.{u + 1}
  have hG (V : Cᵒᵖ) : Small.{u} (G.obj.obj V) := by
    apply small_sheaf_colimit
    intro i W
    exact small_freeYoneda J i.as.1 _ W
  have hA (V : X.AffineEtaleᵒᵖ) : Small.{u} ((e₁.functor.obj G).obj.obj V) := by
    apply small_dense_extension (AffineEtale.topology X) e.inverse
    intro c
    let i := ((sheafToPresheaf J AddCommGrpCat.{u + 1}).mapIso
      (e₁.unitIso.app G)).app (Opposite.op c)
    have : Small.{u} (G.obj.obj (Opposite.op c)) := hG (Opposite.op c)
    exact @small_map _ _ this i.symm.addCommGroupIsoToAddEquiv.toEquiv
  have hF : Small.{u} ((e₂.functor.obj (e₁.functor.obj G)).obj.obj U) := by
    apply small_dense_extension_essentiallySmall X.smallEtaleTopology (AffineEtale.Spec X)
    intro V
    let i := ((sheafToPresheaf (AffineEtale.topology X) AddCommGrpCat.{u + 1}).mapIso
      (e₂.unitIso.app (e₁.functor.obj G))).app (Opposite.op V)
    have : Small.{u} ((e₁.functor.obj G).obj.obj (Opposite.op V)) := hA (Opposite.op V)
    exact @small_map _ _ this i.symm.addCommGroupIsoToAddEquiv.toEquiv
  change ∃ α : Type u, ∃ f : α → ((e₂.functor.obj (e₁.functor.obj G)).obj.obj U),
    Function.Surjective f
  exact ⟨Shrink _, (equivShrink _).symm, (equivShrink _).symm.surjective⟩

end AlgebraicGeometry.Scheme
