/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.FixedAbelianDescendedSectionLift
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.AlgebraicGeometry.EtaleSectionsFilteredColimit

/-! # Scalar continuity for descended qcqs étale objects

Source: Stacks Project, Tags 09YN and 09YQ.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

private theorem abelian_sections_colimit
    (X : Scheme.{u}) (U : X.Etale) [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    {F : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone F}
    (hc : IsColimit c) :
    Nonempty (IsColimit
      (((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U)).mapCocone
        c)) := by
  let R := ULift.{u + 1} ℤ
  let V := ModuleCat.restrictScalars (ULift.ringEquiv (R := ℤ)).symm.toRingHom ⋙
    forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let e := V.asEquivalence
  let S := sheafCompose X.smallEtaleTopology V
  have : S.EssSurj := ⟨fun P ↦ by
    let Q := (sheafCompose X.smallEtaleTopology e.inverse).obj P
    refine ⟨Q, ⟨?_⟩⟩
    exact ObjectProperty.isoMk _ (Functor.isoWhiskerLeft P.obj e.counitIso)⟩
  have : S.IsEquivalence := {}
  let T := S.asEquivalence.inverse
  let G := F ⋙ T
  let d := T.mapCocone c
  have hd : IsColimit d := isColimitOfPreserves T hc
  let E := (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj (op U)
  have hbij := AlgebraicGeometry.etale_sections_filtered_colimit X R U I G d hd
  have hE : IsColimit (E.mapCocone d) := by
    exact (colimit.isColimit (G ⋙ E)).ofPointIso (t := E.mapCocone d)
      (i := (ConcreteCategory.isIso_iff_bijective _).2 hbij)
  let Eab := (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U)
  have hEV := isColimitOfPreserves V hE
  change IsColimit ((T ⋙ S ⋙ Eab).mapCocone c) at hEV
  exact ⟨IsColimit.mapCoconeEquiv
    (Functor.isoWhiskerRight S.asEquivalence.counitIso Eab) hEV⟩

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- This helper is the representative half of scalar section continuity. The affine étale
site colimit identifies sections on the limit with filtered stage sections, so every
limit section has a stage representative. Source: Stacks Tags 09YN and 09YQ.
Source: Stacks Project, Sites, Tag 09YN, proof of lemma-colimit; Étale Cohomology,
Tag 09YQ, qcqs inverse-limit realization; Cohomology on Sites, Tag 09YP.
(blueprint: lem-weil-pbc-etale-limit-scalar-section-representatives).

Proof: Base change T₀ along the tail of D. Affine-transition base-change limits
identify its limit with Tlim. The first-projection equations, together with the
already fixed base projections, uniquely identify γ and δ with pullback pasting.
On an affine piece, use the full affine étale site and its topos comparison to
apply 09YM to each inverse image in G. Insert these filtered presentations into
the sectionwise colimit of G. Objects, arrows and equalities in the affine site
all descend, so simultaneous refinements are filtered and the diagonal is final.
This identifies the iterated colimit with the stage section groups. Transposing
through the inverse-image adjunction identifies its transitions with the units
followed by φ and γ inverse, and its legs with the units followed by eG inverse,
L.ι and δ inverse. For qcqs T₀, take a finite affine cover, and finite affine
covers of its pairwise intersections; filtered colimits commute with the finite
matching-family equalizers. Thus the same comparison holds for T₀ itself.
The tail is final, so restricting G does not change the colimit supplied by hL.
Every element of a filtered colimit of abelian groups has a stage representative.
Equality of a representative with zero holds after one later transition. These
are the two conclusions below, with the prescribed maps. The empty scheme and
zero coefficients give zero groups; no nonempty-object hypothesis is needed.
This statement concerns one object, with no products or cochain complexes. -/
theorem etale_limit_scalar_sections_representatives
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : IsColimit L)
    (i₀ : I) (T₀ : (D.obj (op i₀)).Etale)
    [CompactSpace T₀.left] [QuasiSeparatedSpace T₀.left] :
    let J := {j : I // i₀ ≤ j}
    let Tj := fun j : J ↦
      (MorphismProperty.Over.pullback @Etale ⊤
        (D.map (homOfLE j.property).op)).obj T₀
    let Tlim := (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj T₀
    ∀ (γ : ∀ (j k : J) (a : j ⟶ k),
        (MorphismProperty.Over.pullback @Etale ⊤
          (D.map (show j.val ⟶ k.val from a).op)).obj (Tj j) ≅ Tj k)
      (δ : ∀ j : J,
        (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op j.val))).obj (Tj j) ≅ Tlim),
      (∀ (j k : J) (a : j ⟶ k),
        (γ j k a).hom.left ≫ pullback.fst T₀.hom (D.map (homOfLE k.property).op) =
          pullback.fst (Tj j).hom (D.map (show j.val ⟶ k.val from a).op) ≫
            pullback.fst T₀.hom (D.map (homOfLE j.property).op)) →
      (∀ j : J,
        (δ j).hom.left ≫ pullback.fst T₀.hom (c.π.app (op i₀)) =
          pullback.fst (Tj j).hom (c.π.app (op j.val)) ≫
            pullback.fst T₀.hom (D.map (homOfLE j.property).op)) →
    let ρ := fun (j k : J) (a : j ⟶ k) ↦
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (D.map (show j.val ⟶ k.val from a).op)).unit.app (F j.val)).hom.app (op (Tj j)) ≫
        (φ (show j.val ⟶ k.val from a)).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤
            (D.map (show j.val ⟶ k.val from a).op)).obj (Tj j))) ≫
        (F k.val).obj.map (γ j k a).inv.op
    let μ := fun j : J ↦
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (c.π.app (op j.val))).unit.app (F j.val)).hom.app (op (Tj j)) ≫
        (eG j.val).inv.hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤
            (c.π.app (op j.val))).obj (Tj j))) ≫
        (L.ι.app j.val).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤
            (c.π.app (op j.val))).obj (Tj j))) ≫
        L.pt.obj.map (δ j).inv.op
    (∀ x : L.pt.obj.obj (op Tlim),
      ∃ (j : J) (z : (F j.val).obj.obj (op (Tj j))), μ j z = x) := by
  classical
  dsimp only
  intro γ δ hγ hδ x
  let J := {j : I // i₀ ≤ j}
  let Tj (j : J) : (D.obj (op j.val)).Etale :=
    (MorphismProperty.Over.pullback @Etale ⊤
      (D.map (homOfLE j.property).op)).obj T₀
  let Tlim : c.pt.Etale := (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj T₀
  have : IsAffineHom (c.π.app (op i₀)) := isAffineHom_π_app D c hc (op i₀)
  have : CompactSpace Tlim.left := by dsimp [Tlim]; infer_instance
  have : QuasiSeparatedSpace Tlim.left := by
    dsimp [Tlim]
    exact @quasiSeparatedSpace_of_quasiSeparated _ T₀.left
      (pullback.fst T₀.hom (c.π.app (op i₀))) inferInstance inferInstance
  let E := (sheafSections c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op Tlim)
  obtain ⟨hE⟩ := abelian_sections_colimit c.pt Tlim hL
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  obtain ⟨b, t, ht⟩ := Concrete.isColimit_exists_rep (G ⋙ E) hE x
  obtain ⟨j, h₀, hb⟩ := exists_ge_ge i₀ b
  let i : J := ⟨j, h₀⟩
  let ti : (G.obj i.val).obj.obj (op Tlim) :=
    (G.map (homOfLE hb)).hom.app (op Tlim) t
  have hti : (L.ι.app i.val).hom.app (op Tlim) ti = x := by
    have h := congrArg (fun f ↦ (f.hom.app (op Tlim)) t) (L.w (homOfLE hb))
    exact h.trans ht
  let H := F i.val
  let Pi := (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i.val))).obj H
  let y : Pi.obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤
        (c.π.app (op i.val))).obj (Tj i))) :=
    Pi.obj.map (δ i).hom.op ((eG i.val).hom.hom.app (op Tlim) ti)
  obtain ⟨k, a, s, hs⟩ := fixed_abelian_descended_section_lift
    D c hc i₀ T₀ γ δ hγ hδ i H y
  let p : D.obj (op k.val) ⟶ D.obj (op i.val) := D.map (show i.val ⟶ k.val from a).op
  let q : c.pt ⟶ D.obj (op k.val) := c.π.app (op k.val)
  let B : (D.obj (op k.val)).Etale := (MorphismProperty.Over.pullback @Etale ⊤ p).obj (Tj i)
  let C : c.pt.Etale := (MorphismProperty.Over.pullback @Etale ⊤ q).obj B
  let P := (upperStar AddCommGrpCat.{u + 1} p).obj H
  let Pk := (upperStar AddCommGrpCat.{u + 1} q).obj (F k.val)
  let χ := upperStarComp AddCommGrpCat.{u + 1} q p (c.π.app (op i.val))
    (c.w (show i.val ⟶ k.val from a).op).symm
  let A : Pi ⟶ L.pt := (eG i.val).inv ≫ L.ι.app i.val
  let A' : Pk ⟶ L.pt := (eG k.val).inv ≫ L.ι.app k.val
  let β := (δ i).hom ≫ (δ k).inv ≫
    (MorphismProperty.Over.pullback @Etale ⊤ q).map (γ i k a).inv
  let η := ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} q).unit.app P).hom.app
    (op B)
  let z : (F k.val).obj.obj (op (Tj k)) :=
    (F k.val).obj.map (γ i k a).inv.op
      ((φ (show i.val ⟶ k.val from a)).hom.app (op B) s)
  refine ⟨k, z, ?_⟩
  have hA : (χ.inv.app H) ≫ A =
      (upperStar AddCommGrpCat.{u + 1} q).map (φ (show i.val ⟶ k.val from a)) ≫ A' := by
    have hw := L.w (show i.val ⟶ k.val from a)
    rw [hG] at hw
    dsimp only [A, A', χ, q, p, H]
    rw [← cancel_epi (χ.hom.app (F i.val))]
    have h := congrArg (fun f ↦ (eG i.val).inv ≫ f) hw
    simpa only [χ, q, p, H, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.hom_inv_id_app_assoc] using h.symm
  have hmaps : η ≫ (χ.inv.app H).hom.app (op C) ≫ Pi.obj.map β.op ≫
      A.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤
        (c.π.app (op i.val))).obj (Tj i))) ≫ L.pt.obj.map (δ i).inv.op =
      (φ (show i.val ⟶ k.val from a)).hom.app (op B) ≫
        (F k.val).obj.map (γ i k a).inv.op ≫
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} q).unit.app
          (F k.val)).hom.app (op (Tj k)) ≫
        A'.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ q).obj (Tj k))) ≫
        L.pt.obj.map (δ k).inv.op := by
    erw [A.hom.naturality_assoc]
    have happ := congrArg (fun f ↦ f.hom.app (op C)) hA
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at happ
    erw [reassoc_of% happ]
    simp only [β, op_comp, Functor.map_comp, Category.assoc]
    rw [← L.pt.obj.map_comp, ← op_comp, Iso.inv_hom_id,
      op_id, CategoryTheory.Functor.map_id, Category.comp_id]
    have hu := congrArg (fun f ↦ f.hom.app (op B))
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} q).unit_naturality
        (φ (show i.val ⟶ k.val from a)))
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hu
    erw [reassoc_of% hu]
    dsimp only [Pk, C] at A' ⊢
    erw [← A'.hom.naturality_assoc]
    have hn := ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} q).unit.app
      (F k.val)).hom.naturality (γ i k a).inv.op
    erw [← reassoc_of% hn]
  have hy : (A.hom.app _ ≫ L.pt.obj.map (δ i).inv.op) y = x := by
    have hnat := A.hom.naturality (δ i).hom.op
    have he : Pi.obj.map (δ i).hom.op ≫ A.hom.app _ ≫
        L.pt.obj.map (δ i).inv.op = A.hom.app (op Tlim) := by
      rw [reassoc_of% hnat]
      rw [← Functor.map_comp, ← op_comp, Iso.inv_hom_id, op_id,
        CategoryTheory.Functor.map_id, Category.comp_id]
    change (Pi.obj.map (δ i).hom.op ≫ A.hom.app _ ≫
      L.pt.obj.map (δ i).inv.op) ((eG i.val).hom.hom.app (op Tlim) ti) = x
    rw [he]
    have he' := congrArg (fun f ↦ f.hom.app (op Tlim))
      ((eG i.val).hom_inv_id_assoc (L.ι.app i.val))
    change (A.hom.app (op Tlim)) ((eG i.val).hom.hom.app (op Tlim) ti) = x
    rw [← AddCommGrpCat.comp_apply]
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at he'
    rw [show (eG i.val).hom.hom.app (op Tlim) ≫ A.hom.app (op Tlim) =
      (L.ι.app i.val).hom.app (op Tlim) from he']
    exact hti
  have hh := ConcreteCategory.congr_hom hmaps s
  change (η ≫ (χ.inv.app H).hom.app (op C) ≫ Pi.obj.map β.op) s = y at hs
  simp only [AddCommGrpCat.comp_apply] at hh hs hy
  rw [hs] at hh
  change (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} q).unit.app
    (F k.val)).hom.app (op (Tj k)) ≫
      A'.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ q).obj (Tj k))) ≫
      L.pt.obj.map (δ k).inv.op) z = x
  dsimp only [z]
  simp only [AddCommGrpCat.comp_apply]
  exact hh.symm.trans hy



end AlgebraicGeometry.Etale
