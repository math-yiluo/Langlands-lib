/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Basic.Finite.Prod

/-!
# Continuity of locally classical pro-etale sheaves

Source: Bhatt--Scholze, Lemma 5.1.4. The finite-presieve argument generalizes
`WeilConjectures.CategoryTheory.FinitePresieveFilteredColimit` to a locally small
site whose objects and section sets lie in the next universe.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory Opposite

namespace CategoryTheory

private theorem finite_sections_lift
    {C : Type v} [Category.{u} C]
    {Λ : Type u} [SmallCategory Λ] [IsFiltered Λ]
    (D : Λ ⥤ Cᵒᵖ ⥤ Type (u + 1)) (c : Cocone D) (hc : IsColimit c)
    {I : Type*} [Finite I] (Y : I → C) (x : ∀ i, c.pt.obj (op (Y i))) :
    ∃ (k : Λ) (y : ∀ i, (D.obj k).obj (op (Y i))),
      ∀ i, (c.ι.app k).app (op (Y i)) (y i) = x i := by
  classical
  have : Fintype I := Fintype.ofFinite I
  have hs (i : I) := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ _).obj (op (Y i))) hc) (x i)
  choose j y hy using hs
  obtain ⟨s⟩ := IsFiltered.cocone_nonempty (Discrete.functor j)
  refine ⟨s.pt, fun i ↦ (D.map (s.ι.app ⟨i⟩)).app _ (y i), fun i ↦ ?_⟩
  have hw := congrArg (fun t ↦ t.app (op (Y i))) (c.w (s.ι.app ⟨i⟩))
  exact (congr_hom hw (y i)).trans (hy i)

private theorem finite_sections_equal
    {C : Type v} [Category.{u} C]
    {Λ : Type u} [SmallCategory Λ] [IsFiltered Λ]
    (D : Λ ⥤ Cᵒᵖ ⥤ Type (u + 1)) (c : Cocone D) (hc : IsColimit c)
    {I : Type*} [Finite I] (Y : I → C) (j : Λ)
    (x y : ∀ i, (D.obj j).obj (op (Y i)))
    (h : ∀ i, (c.ι.app j).app _ (x i) = (c.ι.app j).app _ (y i)) :
    ∃ (k : Λ) (f : j ⟶ k), ∀ i,
      (D.map f).app (op (Y i)) (x i) = (D.map f).app (op (Y i)) (y i) := by
  classical
  have hs (i : I) := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves ((evaluation _ _).obj (op (Y i))) hc) (x i) (y i)).mp (h i)
  choose k f hf using hs
  obtain ⟨l, g, q, hq⟩ := IsFiltered.wideSpan f
  refine ⟨l, g, fun i ↦ ?_⟩
  rw [← hq i]
  simp only [Functor.map_comp, NatTrans.comp_app, types_comp_apply]
  exact congrArg ((D.map (q i)).app _) (hf i)

/-- A filtered colimit of presheaves satisfying the sheaf condition for one finite
presieve with pairwise pullbacks satisfies that same condition.
Source: Stacks Project, Sites, Tag 0738(4) and Tag 00VM; Categories, Tag 002W
(auxiliary; not a blueprint node).

Proof: Index the arrows of R by its finite subtype of uncurried arrows. Evaluation
preserves presheaf colimits. For separatedness, lift two sections over X to a common
stage. Their restrictions agree in the colimit over each arrow of R, so each such
equality holds after a transition. The finite wide-span lemma for filtered categories
makes all of these transitions factor through a single transition. Separatedness at
that stage identifies the two sections, hence their images in the colimit agree.

For existence, lift the finitely many members of a compatible family to stages of
the diagram, and take a cocone over the finite discrete diagram of those stages.
This gives a family at one stage. For each pair of arrows of R, compatibility of its
image implies equality of the two restrictions over the pairwise pullback after a
transition. There are finitely many pairs, so the finite wide-span lemma again gives
one transition making every compatibility equation hold. At that stage the sheaf
condition provides an amalgamation. Its image amalgamates the original family by
naturality and the cocone equations. Empty R causes no exception: the finite discrete
cocone and the wide-span construction also apply to empty index sets, and the
stagewise empty-presieve sheaf condition supplies the unique section over X.

This is the finite-stage argument of Sites Tag 0738(4), applied directly to the
sectionwise presheaf colimit and the sheaf condition of Tag 00VM. -/
private theorem finitePresieveSheafFilteredColimit
    {C : Type v} [Category.{u} C]
    {Λ : Type u} [SmallCategory Λ] [IsFiltered Λ]
    (D : Λ ⥤ Cᵒᵖ ⥤ Type (u + 1)) (c : Cocone D) (hc : IsColimit c)
    {X : C} (R : Presieve X) [R.HasPairwisePullbacks]
    (hfinite : R.uncurry.Finite)
    (hD : ∀ i, R.IsSheafFor (D.obj i)) : R.IsSheafFor c.pt := by
  classical
  let I := R.uncurry
  have : Finite I := Set.finite_coe_iff.mpr hfinite
  let Y : I → C := fun i ↦ i.val.1
  let f : ∀ i : I, Y i ⟶ X := fun i ↦ i.val.2
  have hf (i : I) : R (f i) := i.property
  rw [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  have hsep : R.IsSeparatedFor c.pt := by
    intro z a b haz hbz
    have hab {Z : C} {h : Z ⟶ X} (hh : R h) :
        c.pt.map h.op a = c.pt.map h.op b := (haz h hh).trans (hbz h hh).symm
    obtain ⟨j, a', b', ha, hb⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂
      (isColimitOfPreserves ((evaluation _ _).obj (op X)) hc) a b
    change (c.ι.app j).app (op X) a' = a at ha
    change (c.ι.app j).app (op X) b' = b at hb
    have heq (i : I) :
        (c.ι.app j).app (op (Y i)) ((D.obj j).map (f i).op a') =
        (c.ι.app j).app (op (Y i)) ((D.obj j).map (f i).op b') := by
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply, ha, hb]
      exact hab (hf i)
    obtain ⟨k, g, hg⟩ := finite_sections_equal D c hc Y j
      (fun i ↦ (D.obj j).map (f i).op a')
      (fun i ↦ (D.obj j).map (f i).op b') heq
    have he : (D.map g).app (op X) a' = (D.map g).app (op X) b' := by
      apply (hD k).isSeparatedFor.ext
      intro Z h hh
      have eq := hg (⟨⟨Z, h⟩, hh⟩ : I)
      simpa only [Y, f, NatTrans.naturality_apply] using eq
    have hw := congrArg (fun t ↦ t.app (op X)) (c.w g)
    calc
      a = (c.ι.app j).app (op X) a' := ha.symm
      _ = (c.ι.app k).app (op X) ((D.map g).app (op X) a') :=
        (congr_hom hw a').symm
      _ = (c.ι.app k).app (op X) ((D.map g).app (op X) b') := congrArg _ he
      _ = (c.ι.app j).app (op X) b' := congr_hom hw b'
      _ = b := hb
  refine ⟨hsep, ?_⟩
  intro x hx
  obtain ⟨j, y, hy⟩ := finite_sections_lift D c hc Y (fun i ↦ x (f i) (hf i))
  have hp (ij : I × I) : HasPullback (f ij.1) (f ij.2) :=
    Presieve.HasPairwisePullbacks.has_pullbacks (hf ij.1) (hf ij.2)
  let Z : I × I → C := fun ij ↦ @pullback _ _ _ _ _ (f ij.1) (f ij.2) (hp ij)
  let a : ∀ ij : I × I, (D.obj j).obj (op (Z ij)) := fun ij ↦
    have := hp ij
    (D.obj j).map (pullback.fst (f ij.1) (f ij.2)).op (y ij.1)
  let b : ∀ ij : I × I, (D.obj j).obj (op (Z ij)) := fun ij ↦
    have := hp ij
    (D.obj j).map (pullback.snd (f ij.1) (f ij.2)).op (y ij.2)
  have heq (ij : I × I) :
      (c.ι.app j).app (op (Z ij)) (a ij) = (c.ι.app j).app (op (Z ij)) (b ij) := by
    have := hp ij
    dsimp [a, b, Z]
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
    exact (congrArg (c.pt.map (pullback.fst (f ij.1) (f ij.2)).op) (hy ij.1)).trans
      (((Presieve.pullbackCompatible_iff x).mp hx (hf ij.1) (hf ij.2)).trans
        (congrArg (c.pt.map (pullback.snd (f ij.1) (f ij.2)).op) (hy ij.2)).symm)
  obtain ⟨k, g, hg⟩ := finite_sections_equal D c hc Z j a b heq
  let z : R.FamilyOfElements (D.obj k) := fun T h hh ↦
    (D.map g).app (op T) (y (⟨⟨T, h⟩, hh⟩ : I))
  have hz : z.Compatible := by
    rw [Presieve.pullbackCompatible_iff]
    intro T₁ T₂ h₁ h₂ hh₁ hh₂
    let i₁ : I := ⟨⟨T₁, h₁⟩, hh₁⟩
    let i₂ : I := ⟨⟨T₂, h₂⟩, hh₂⟩
    have := hp (i₁, i₂)
    have eq := hg (i₁, i₂)
    simpa only [a, b, z, Z, i₁, i₂, Y, f, NatTrans.naturality_apply] using eq
  obtain ⟨s, hs, _⟩ := hD k z hz
  refine ⟨(c.ι.app k).app (op X) s, ?_⟩
  intro T h hh
  let i : I := ⟨⟨T, h⟩, hh⟩
  have hw := congrArg (fun t ↦ t.app (op T)) (c.w g)
  calc
    c.pt.map h.op ((c.ι.app k).app (op X) s) =
        (c.ι.app k).app (op T) ((D.obj k).map h.op s) :=
      (NatTrans.naturality_apply (c.ι.app k) h.op s).symm
    _ = (c.ι.app k).app (op T) ((D.map g).app (op T) (y i)) :=
      congrArg _ (hs h hh)
    _ = (c.ι.app j).app (op T) (y i) := congr_hom hw (y i)
    _ = x h hh := hy i


private theorem finiteGeneratedSheafFilteredColimit
    {C : Type (u + 1)} [Category.{u} C] [HasPullbacks C]
    (K : Precoverage C) (T : GrothendieckTopology C)
    (hK : K.Generates T) (hfinite : K ≤ Precoverage.finite C)
    {Λ : Type u} [SmallCategory Λ] [IsFiltered Λ]
    (D : Λ ⥤ Cᵒᵖ ⥤ Type (u + 1)) (c : Cocone D) (hc : IsColimit c)
    (hD : ∀ i, Presheaf.IsSheaf T (D.obj i)) : Presheaf.IsSheaf T c.pt := by
  rw [isSheaf_iff_isSheaf_of_type]
  apply hK.isSheaf_of_forall
  intro X R hR
  apply finitePresieveSheafFilteredColimit D c hc R (hfinite X hR)
  intro i
  exact (hK.isSheaf_type_iff.mp
    ((isSheaf_iff_isSheaf_of_type T (D.obj i)).mp (hD i))) R hR


private noncomputable def productSections
    {C : Type (u + 1)} [Category.{u} C] [HasBinaryProducts C]
    (F : Cᵒᵖ ⥤ Type (u + 1)) : Cᵒᵖ ⥤ Cᵒᵖ ⥤ Type (u + 1) :=
  (Limits.prod.functor : C ⥤ C ⥤ C).op ⋙
    Functor.opHom C C ⋙ (Functor.whiskeringRight _ _ _).obj F

private theorem productSections_isSheaf {C : Type (u + 1)} [Category.{u} C] [HasBinaryProducts C]
    (T : GrothendieckTopology C) (F : Sheaf T (Type (u + 1))) (B : C) :
    Presheaf.IsSheaf T ((productSections F.obj).obj (op B)) := by
  have hi : (Over.star B ⋙ Over.forget B).IsContinuous T T :=
    Functor.isContinuous_comp _ _ _ (T.over B) _
  have he : Over.star B ⋙ Over.forget B ≅ Limits.prod.functor.obj B := Iso.refl _
  have hi' : (Limits.prod.functor.obj B).IsContinuous T T :=
    Functor.isContinuous_of_iso he T T
  exact (Limits.prod.functor.obj B).op_comp_isSheaf T T F


private theorem productContinuity_of_cover
    {C : Type (u + 1)} [Category.{u} C] [HasBinaryProducts C] [HasPullbacks C]
    (K : Precoverage C) (T : GrothendieckTopology C)
    (hK : K.Generates T) (hfinite : K ≤ Precoverage.finite C)
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ C) (c : Cone D) (F : Sheaf T (Type (u + 1)))
    {I : Type*} (U : I → C) (hU : T.CoversTop U)
    (hlocal : ∀ i (V : C) (_ : V ⟶ U i), Nonempty (IsColimit
      (F.obj.mapCocone ((Limits.prod.functor.flip.obj V).mapCone c).op))) :
    ∀ V : C, Nonempty (IsColimit
      (F.obj.mapCocone ((Limits.prod.functor.flip.obj V).mapCone c).op)) := by
  let B := productSections F.obj
  let Q := B.mapCocone c.op
  let P := D.op ⋙ B
  let a := colimit.desc P Q
  have hP : Presheaf.IsSheaf T (colimit P) :=
    finiteGeneratedSheafFilteredColimit K T hK hfinite P _ (colimit.isColimit P)
      (fun j ↦ productSections_isSheaf T F (D.obj j.unop))
  have hQ : Presheaf.IsSheaf T Q.pt := productSections_isSheaf T F c.pt
  let a' : (⟨colimit P, hP⟩ : Sheaf T (Type (u + 1))) ⟶ ⟨Q.pt, hQ⟩ := ⟨a⟩
  have hlocal' (i : I) (V : C) (f : V ⟶ U i) : IsIso (a.app (op V)) := by
    let E := (evaluation Cᵒᵖ (Type (u + 1))).obj (op V)
    let hc := isColimitOfPreserves E (colimit.isColimit P)
    obtain ⟨hd⟩ : Nonempty (IsColimit (E.mapCocone Q)) := hlocal i V f
    have heq : a.app (op V) = (hc.coconePointUniqueUpToIso hd).hom := by
      apply hc.hom_ext
      intro j
      change (colimit.ι P j).app (op V) ≫ a.app (op V) = _
      rw [← NatTrans.comp_app, colimit.ι_desc]
      exact (hc.comp_coconePointUniqueUpToIso_hom hd j).symm
    rw [heq]
    infer_instance
  have ha' : IsIso a' := by
    apply Sheaf.isIso_of_coversTop hU
    intro i
    rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
    intro V
    exact hlocal' i V.unop.left V.unop.hom
  have ha : IsIso a := (sheafToPresheaf T (Type (u + 1))).map_isIso a'
  have : IsIso ((colimit.isColimit P).desc Q) := ha
  have hQcolim : IsColimit Q := IsColimit.ofPointIso (colimit.isColimit P)
  intro V
  exact ⟨isColimitOfPreserves ((evaluation Cᵒᵖ (Type (u + 1))).obj (op V)) hQcolim⟩

end CategoryTheory

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def restrictionInverseImageIso (X : Scheme.{u}) (U : X.ProEt) :
    ProEtale.proEtaleComparisonPullback (Type (u + 1)) U.hom ≅
      @Functor.sheafPushforwardContinuous U.left.ProEt _ X.ProEt _
        (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ U.prop)
        (Type (u + 1)) _ (ProEt.topology U.left) (ProEt.topology X)
        (ProEt.isContinuous_overMap U.prop) := by
  letI hMap := ProEt.isContinuous_overMap U.prop
  letI hPull := ProEt.isContinuous_overPullback U.hom
  have hMap' : (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ U.prop).IsContinuous
      (ProEt.topology U.left) (ProEt.topology X) := ProEt.isContinuous_overMap U.prop
  let adj : (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ U.prop) ⊣
      MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom :=
    MorphismProperty.Over.mapPullbackAdj (@WeaklyEtale) ⊤ U.hom U.prop _root_.trivial
  exact (ProEtale.proEtaleComparisonAdjunction (Type (u + 1)) U.hom).leftAdjointUniq
    (@Adjunction.sheafPushforwardContinuous _ _ _ _ _ _ _ _ adj
      (ProEt.topology U.left) (ProEt.topology X) hMap' hPull)

private noncomputable def classicalRestrictionIso (X : Scheme.{u}) (U : X.ProEt) :
    ProEtale.comparisonCoefficientPullback (Type (u + 1)) X ⋙
      @Functor.sheafPushforwardContinuous U.left.ProEt _ X.ProEt _
        (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ U.prop)
        (Type (u + 1)) _ (ProEt.topology U.left) (ProEt.topology X)
        (ProEt.isContinuous_overMap U.prop) ≅
    ProEtale.etaleComparisonPullback (Type (u + 1)) U.hom ⋙
      ProEtale.comparisonCoefficientPullback (Type (u + 1)) U.left :=
  (Functor.isoWhiskerLeft _ (restrictionInverseImageIso X U)).symm ≪≫
    (ProEtale.comparisonCoefficientPullbackIso (Type (u + 1)) U.hom).symm


private abbrev restriction (X : Scheme.{u}) (U : X.ProEt) :=
  @Functor.sheafPushforwardContinuous U.left.ProEt _ X.ProEt _
    (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ U.prop)
    (Type (u + 1)) _ (ProEt.topology U.left) (ProEt.topology X)
    (ProEt.isContinuous_overMap U.prop)

private noncomputable def refinedDiagram (X : Scheme.{u}) (U : X.AffineProEt)
    {J : Type u} [SmallCategory J] (D : J ⥤ X.AffineProEt)
    (s : D ⟶ (Functor.const J).obj U) : J ⥤ U.left.AffineProEt :=
  MorphismProperty.Over.iteratedLift D s (fun j ↦ AffineProEt.proAffineEtale_hom _)

private noncomputable def refinedCone (X : Scheme.{u}) (U : X.AffineProEt)
    {J : Type u} [SmallCategory J] {D : J ⥤ X.AffineProEt}
    (s : D ⟶ (Functor.const J).obj U) (c : Cone D) (t : c.pt ⟶ U)
    (ht : ∀ j, c.π.app j ≫ s.app j = t) : Cone (refinedDiagram X U D s) where
  pt := AffineProEt.mk t.left (AffineProEt.proAffineEtale_hom t)
  π.app j := MorphismProperty.Over.homMk (c.π.app j).left
    (congrArg (fun f ↦ f.left) (ht j))
  π.naturality i j f := by
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun f ↦ f.left) (c.π.naturality f)

private noncomputable def refinedConeIsLimit (X : Scheme.{u}) (U : X.AffineProEt)
    {J : Type u} [SmallCategory J] [IsCofiltered J] {D : J ⥤ X.AffineProEt}
    (s : D ⟶ (Functor.const J).obj U) (c : Cone D) (t : c.pt ⟶ U)
    (ht : ∀ j, c.π.app j ≫ s.app j = t) (hc : IsLimit c) :
    IsLimit (refinedCone X U s c t ht) := by
  apply isLimitOfReflects (AffineProEt.toScheme U.left)
  exact AffineProEt.isLimitMapConeToSchemeOfIsLimit c hc


private noncomputable def refinedDiagramIso (X : Scheme.{u}) (U : X.AffineProEt)
    {J : Type u} [SmallCategory J] (D : J ⥤ X.AffineProEt)
    (s : D ⟶ (Functor.const J).obj U) :
    refinedDiagram X U D s ⋙ AffineProEt.toProEt U.left ⋙
        MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
          ((AffineProEt.toProEt X).obj U).prop ≅ D ⋙ AffineProEt.toProEt X :=
  NatIso.ofComponents (fun j ↦ MorphismProperty.Over.isoMk (Iso.refl _)
    (MorphismProperty.Over.w (s.app j)).symm)
    (fun f ↦ MorphismProperty.Over.Hom.ext (by simp; rfl))

private noncomputable def refinedConeIso (X : Scheme.{u}) (U : X.AffineProEt)
    {J : Type u} [SmallCategory J] {D : J ⥤ X.AffineProEt}
    (s : D ⟶ (Functor.const J).obj U) (c : Cone D) (t : c.pt ⟶ U)
    (ht : ∀ j, c.π.app j ≫ s.app j = t) :
    (Cone.postcompose (refinedDiagramIso X U D s).hom).obj
      (((AffineProEt.toProEt U.left) ⋙
        MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
          ((AffineProEt.toProEt X).obj U).prop).mapCone
            (refinedCone X U s c t ht)) ≅
      (AffineProEt.toProEt X).mapCone c := by
  let ep : ((MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
      ((AffineProEt.toProEt X).obj U).prop).obj
      ((AffineProEt.toProEt U.left).obj (refinedCone X U s c t ht).pt)) ≅
      (AffineProEt.toProEt X).obj c.pt :=
    MorphismProperty.Over.isoMk (Iso.refl _) (MorphismProperty.Over.w t).symm
  refine Cone.ext ep ?_
  intro j
  apply MorphismProperty.Over.Hom.ext
  change (c.π.app j).left ≫ 𝟙 _ = 𝟙 _ ≫ (c.π.app j).left
  simp

private theorem continuity_over_basis_object (X : Scheme.{u}) (U : X.AffineProEt)
    (F : Sheaf (ProEt.topology X) (Type (u + 1)))
    (hF : PreservesFilteredColimitsOfSize.{u, u}
      ((AffineProEt.toProEt U.left).op ⋙
        ((restriction X ((AffineProEt.toProEt X).obj U)).obj F).obj))
    {J : Type u} [SmallCategory J] [IsCofiltered J] {D : J ⥤ X.AffineProEt}
    (s : D ⟶ (Functor.const J).obj U) (c : Cone D) (t : c.pt ⟶ U)
    (ht : ∀ j, c.π.app j ≫ s.app j = t) (hc : IsLimit c) :
    Nonempty (IsColimit
      (F.obj.mapCocone ((AffineProEt.toProEt X).mapCone c).op)) := by
  let c' := refinedCone X U s c t ht
  have hc' := refinedConeIsLimit X U s c t ht hc
  have := hF
  let R := (restriction X ((AffineProEt.toProEt X).obj U)).obj F
  have hR : IsColimit (((AffineProEt.toProEt U.left).op ⋙ R.obj).mapCocone c'.op) :=
    isColimitOfPreserves _ hc'.op
  let iD := refinedDiagramIso X U D s
  let iC := refinedConeIso X U s c t ht
  let cNew := ((AffineProEt.toProEt U.left) ⋙
    MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
      ((AffineProEt.toProEt X).obj U).prop).mapCone c'
  have hR' : IsColimit (F.obj.mapCocone cNew.op) := hR
  refine ⟨(IsColimit.equivOfNatIsoOfIso
    (Functor.isoWhiskerRight (NatIso.op iD.symm) F.obj) (F.obj.mapCocone cNew.op) _ ?_).toFun hR'⟩
  refine Cocone.ext (F.obj.mapIso ((Cone.forget _).mapIso iC).op).symm ?_
  intro j
  change F.obj.map (iD.hom.app j.unop).op ≫
    F.obj.map (cNew.π.app j.unop).op ≫ F.obj.map iC.inv.hom.op =
      F.obj.map (((AffineProEt.toProEt X).mapCone c).π.app j.unop).op
  rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp]
  congr 2


private theorem affineHasTerminal (X : Scheme.{u}) [IsAffine X] :
    HasTerminal X.AffineProEt := by
  apply IsTerminal.hasTerminal (X := AffineProEt.ofEtale (𝟙 X))
  exact IsTerminal.ofUniqueHom
    (fun U ↦ MorphismProperty.Over.homMk U.hom (Category.comp_id _))
    (fun U f ↦ MorphismProperty.Over.Hom.ext (by
      change f.left = U.hom
      have hw : f.left ≫ 𝟙 X = U.hom := MorphismProperty.Over.w f
      exact (Category.comp_id _).symm.trans hw))

private noncomputable def rightProdIso {C : Type*} [Category* C] [HasBinaryProducts C] (V : C) :
    Limits.prod.functor.flip.obj V ≅ Limits.prod.functor.obj V :=
  NatIso.ofComponents (fun W ↦ Limits.prod.braiding W V) (by
    intro W W' f
    apply Limits.prod.hom_ext <;> simp)

private theorem affine_continuity (X : Scheme.{u}) [IsAffine X]
    (F : Sheaf (ProEt.topology X) (Type (u + 1)))
    (I : Type (u + 1)) (U : I → X.AffineProEt)
    (hU : (AffineProEt.topology X).CoversTop U)
    (hF : ∀ i, ∃ G : Sheaf (U i).left.smallEtaleTopology (Type (u + 1)), Nonempty
      ((restriction X ((AffineProEt.toProEt X).obj (U i))).obj F ≅
        (ProEtale.comparisonCoefficientPullback (Type (u + 1)) (U i).left).obj G)) :
    PreservesFilteredColimitsOfSize.{u, u} ((AffineProEt.toProEt X).op ⋙ F.obj) := by
  have := affineHasTerminal X
  have : HasFiniteLimits X.AffineProEt := hasFiniteLimits_of_hasTerminal_and_pullbacks
  constructor
  intro J _ _
  have : IsConnected Jᵒᵖ := IsCofiltered.isConnected _
  constructor
  intro K
  constructor
  intro d hd
  let D := K.leftOp
  let c := coneLeftOpOfCocone d
  have hc : IsLimit c := isLimitConeLeftOpOfCocone K hd
  let F' := ((AffineProEt.toProEt X).sheafPushforwardContinuous (Type (u + 1))
    (AffineProEt.topology X) (ProEt.topology X)).obj F
  have hall := CategoryTheory.productContinuity_of_cover
    (AffineProEt.minimalPrecoverage X) (AffineProEt.topology X)
    (AffineProEt.generates_minimalPrecoverage X) (AffineProEt.minimalPrecoverage_le_finite X)
    D c F' U hU (fun i V f ↦ ?_)
  · obtain ⟨hT⟩ := hall (⊤_ X.AffineProEt)
    let ep : Limits.prod.functor.flip.obj (⊤_ X.AffineProEt) ≅ 𝟭 X.AffineProEt :=
      NatIso.ofComponents (fun W ↦ Limits.prod.rightUnitor W)
        (fun f ↦ Limits.prod.rightUnitor_hom_naturality f)
    have hC : IsColimit (F'.obj.mapCocone c.op) :=
      IsColimit.mapCoconeEquiv (Functor.isoWhiskerRight (NatIso.op ep.symm) F'.obj) hT
    exact ⟨by exact hC.whiskerEquivalence (opOpEquivalence J).symm⟩
  · let cV := (Limits.prod.functor.flip.obj V).mapCone c
    have : PreservesLimitsOfShape Jᵒᵖ (Limits.prod.functor.obj V) :=
      prod_preservesConnectedLimits V
    have : PreservesLimitsOfShape Jᵒᵖ (Limits.prod.functor.flip.obj V) :=
      preservesLimitsOfShape_of_natIso (rightProdIso V).symm
    have hcV : IsLimit cV := isLimitOfPreserves _ hc
    let s : D ⋙ Limits.prod.functor.flip.obj V ⟶ (Functor.const Jᵒᵖ).obj (U i) :=
      { app j := Limits.prod.snd ≫ f
        naturality j k a := by simp }
    let t : cV.pt ⟶ U i := Limits.prod.snd ≫ f
    have ht : ∀ j, cV.π.app j ≫ s.app j = t := by
      intro j
      change Limits.prod.map (c.π.app j) (𝟙 V) ≫ Limits.prod.snd ≫ f = _
      rw [Limits.prod.map_snd_assoc, Category.id_comp]
      rfl
    obtain ⟨G, ⟨e⟩⟩ := hF i
    have hClass : PreservesFilteredColimitsOfSize.{u, u}
        ((AffineProEt.toProEt (U i).left).op ⋙
          ((ProEtale.comparisonCoefficientPullback (Type (u + 1)) (U i).left).obj G).obj) :=
      proEtaleComparisonSets_continuous (U i).left G
    have hres : PreservesFilteredColimitsOfSize.{u, u}
        ((AffineProEt.toProEt (U i).left).op ⋙
          ((restriction X ((AffineProEt.toProEt X).obj (U i))).obj F).obj) := by
      constructor
      intro L _ _
      let ep := Functor.isoWhiskerLeft (AffineProEt.toProEt (U i).left).op
        ((sheafToPresheaf _ (Type (u + 1))).mapIso e.symm)
      exact @preservesColimitsOfShape_of_natIso _ _ _ _ L _ _ _ ep
        (hClass.preserves_filtered_colimits L)
    exact continuity_over_basis_object X (U i) F hres s cV t ht hcV


private theorem global_continuity (X : Scheme.{u})
    (F : Sheaf (ProEt.topology X) (Type (u + 1)))
    (hF : ∀ U : X.AffineProEt,
      PreservesFilteredColimitsOfSize.{u, u}
        ((AffineProEt.toProEt U.left).op ⋙
          ((restriction X ((AffineProEt.toProEt X).obj U)).obj F).obj)) :
    Functor.PreservesRelativeFilteredColimits.{u} (AffineEtale.toAffineProEt X)
      ((AffineProEt.toProEt X).op ⋙ F.obj) := by
  constructor
  intro J _ _ D c hc
  classical
  let j₀ : J := IsCofiltered.nonempty.some
  let D₀ := CategoryTheory.Over.forget j₀ ⋙ D ⋙ AffineEtale.toAffineProEt X
  let c₀ := c.whisker (CategoryTheory.Over.forget j₀)
  let U := (D ⋙ AffineEtale.toAffineProEt X).obj j₀
  let s : D₀ ⟶ (Functor.const (CategoryTheory.Over j₀)).obj U :=
    Functor.whiskerRight (CategoryTheory.Over.forgetCocone j₀).ι
      (D ⋙ AffineEtale.toAffineProEt X) ≫ (Functor.constComp _ _ _).hom
  let t : c₀.pt ⟶ U := c.π.app j₀
  have ht : ∀ j, c₀.π.app j ≫ s.app j = t := by
    intro j
    exact c.w j.hom
  have hc₀ : IsLimit c₀ := (Functor.Initial.isLimitWhiskerEquiv _ _).symm hc
  obtain ⟨h⟩ := continuity_over_basis_object X U F (hF U) s c₀ t ht hc₀
  exact ⟨(Functor.Final.isColimitWhiskerEquiv
    (CategoryTheory.Over.forget j₀).op _).toFun h⟩


private theorem affineClassicalCover (X : Scheme.{u})
    (F : Sheaf (ProEt.topology X) (Type (u + 1)))
    (I : Type (u + 1)) (U : I → X.ProEt) (hU : (ProEt.topology X).CoversTop U)
    (hF : ∀ i, ∃ G : Sheaf (U i).left.smallEtaleTopology (Type (u + 1)), Nonempty
      ((restriction X (U i)).obj F ≅
        (ProEtale.comparisonCoefficientPullback (Type (u + 1)) (U i).left).obj G))
    (V : X.AffineProEt) :
    ∃ (A : Type (u + 1)) (W : A → V.left.AffineProEt),
      (AffineProEt.topology V.left).CoversTop W ∧
      ∀ a, ∃ G : Sheaf (W a).left.smallEtaleTopology (Type (u + 1)), Nonempty
        ((restriction V.left ((AffineProEt.toProEt V.left).obj (W a))).obj
          ((restriction X ((AffineProEt.toProEt X).obj V)).obj F) ≅
            (ProEtale.comparisonCoefficientPullback (Type (u + 1)) (W a).left).obj G) := by
  let V' := (AffineProEt.toProEt X).obj V
  let M := MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ V'.prop
  let E := AffineProEt.toProEt V.left ⋙ M
  have hm : M.IsCocontinuous (ProEt.topology V.left) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap V'.prop
  have he : E.IsCocontinuous (AffineProEt.topology V.left) (ProEt.topology X) :=
    isCocontinuous_comp _ _ _ (ProEt.topology V.left)
  let A := Σ Z : V.left.AffineProEt, Σ i : I, E.obj Z ⟶ U i
  refine ⟨A, Sigma.fst, ?_, ?_⟩
  · intro T
    apply (AffineProEt.topology V.left).superset_covering _
      (E.cover_lift _ _ (hU (E.obj T)))
    rintro Z f ⟨i, ⟨g⟩⟩
    exact ⟨⟨Z, i, g⟩, ⟨𝟙 Z⟩⟩
  · rintro ⟨Z, i, g⟩
    have hcomp : WeaklyEtale (g.left ≫ (U i).hom) := by
      rw [MorphismProperty.Over.w g]
      exact (E.obj Z).prop
    have hg : WeaklyEtale g.left := WeaklyEtale.of_comp g.left (U i).hom
    let Zg : (U i).left.ProEt := ProEt.mk g.left
    obtain ⟨G, ⟨e⟩⟩ := hF i
    let Z' := (AffineProEt.toProEt V.left).obj Z
    let Mg := MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ Zg.prop
    let Mi := MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ (U i).prop
    let Mz := MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ Z'.prop
    let eMaps : Mz ⋙ M ≅ Mg ⋙ Mi := NatIso.ofComponents
      (fun W ↦ MorphismProperty.Over.isoMk (Iso.refl _) (by
        change 𝟙 W.left ≫ ((W.hom ≫ g.left) ≫ (U i).hom) =
          (W.hom ≫ Z.hom) ≫ V.hom
        simp only [Category.id_comp, Category.assoc]
        exact congrArg (fun a ↦ W.hom ≫ a) (MorphismProperty.Over.w g)))
      (fun f ↦ MorphismProperty.Over.Hom.ext (by simp; rfl))
    let eR : (restriction V.left Z').obj ((restriction X V').obj F) ≅
        (restriction (U i).left Zg).obj ((restriction X (U i)).obj F) :=
      { hom := ⟨Functor.whiskerRight (NatTrans.op eMaps.inv) F.obj⟩
        inv := ⟨Functor.whiskerRight (NatTrans.op eMaps.hom) F.obj⟩
        hom_inv_id := by ext W; simp [← F.obj.map_comp, ← op_comp]; rfl
        inv_hom_id := by ext W; simp [← F.obj.map_comp, ← op_comp]; rfl }
    refine ⟨(ProEtale.etaleComparisonPullback (Type (u + 1)) g.left).obj G, ⟨?_⟩⟩
    exact eR ≪≫ (restriction (U i).left Zg).mapIso e ≪≫
      (classicalRestrictionIso (U i).left Zg).app G


/-- Local etale presentations imply continuity on affine ind-etale presentations.
Source: Bhatt--Scholze, Lemma 5.1.4, using the continuity criterion of Lemma 5.1.2.
(auxiliary; not a blueprint node).

Proof: Refine the given cover over each affine basis object by all affine ind-etale
objects admitting a map to one of its members. Cocontinuity of localization and of
the dense affine inclusion proves that these objects cover. Raw restriction is the
scheme inverse image, by the map/pullback adjunction, so comparison/pullback
compatibility preserves the local etale presentations on this refinement.

Over an affine base, form the diagram of sheaves V |-> F(C_j times V) and its
canonical cocone V |-> F(C times V). These are sheaves because product with a
fixed object is continuous. Their pointwise filtered colimit is again a sheaf:
the affine pro-etale topology is generated by finite presieves with pairwise
pullbacks, and finitely many representatives and equality witnesses move to a
single stage. Over each refined cover member the classical-continuity theorem
makes the cocone limiting in the required colimit sense, including on every
object mapping to that member. Thus the comparison from the pointwise colimit
to the cocone point is an isomorphism locally, hence globally. Evaluate at the
terminal affine object to obtain section continuity over the affine base.

For a general base, pass to the cofinal over-category of any stage of the affine
etale presentation. Regard this diagram as an affine ind-etale diagram over that
affine stage. The affine result applies to the restriction of F there, and finality
of the opposite over-category returns the original section colimit. Empty covers
are included in the finite-presieve argument; filtered categories are nonempty. -/
theorem proEtale_locallyClassical_continuity (X : Scheme.{u})
    (F : Sheaf (ProEt.topology X) (Type (u + 1)))
    (I : Type (u + 1)) (U : I → X.ProEt) (hU : (ProEt.topology X).CoversTop U)
    (hF : ∀ i, ∃ G : Sheaf (U i).left.smallEtaleTopology (Type (u + 1)), Nonempty
      (((@Functor.sheafPushforwardContinuous (U i).left.ProEt _ X.ProEt _
          (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ (U i).prop)
          (Type (u + 1)) _ (ProEt.topology (U i).left) (ProEt.topology X)
          (ProEt.isContinuous_overMap (U i).prop)).obj F) ≅
        (Functor.sheafPullbackConstruction.sheafPullback (toProEt (U i).left)
          (Type (u + 1)) (U i).left.smallEtaleTopology
          (ProEt.topology (U i).left)).obj G)) :
    Functor.PreservesRelativeFilteredColimits.{u} (AffineEtale.toAffineProEt X)
      ((AffineProEt.toProEt X).op ⋙ F.obj) := by
  apply global_continuity X F
  intro V
  obtain ⟨A, W, hW, hG⟩ := affineClassicalCover X F I U hU hF V
  exact affine_continuity V.left
    ((restriction X ((AffineProEt.toProEt X).obj V)).obj F) A W hW hG


end AlgebraicGeometry.Scheme
