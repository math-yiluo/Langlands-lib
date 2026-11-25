/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionLift
import all WeilConjectures.AlgebraicGeometry.AbelianPullbackGlobalSectionsComparison

/-! # Fixed-coefficient lifting on a descended qcqs étale object

Source: Stacks Project, Sites Tags 09YM and 09YN, and Étale Cohomology Tag 09YQ.
(blueprint: lem-weil-pbc-fixed-abelian-descended-section-lift).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

private lemma pullbackComp_first {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) (A : Z.Etale) :
    ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g fg hfg).hom.app A).left ≫
        pullback.fst (pullback.snd A.hom g) f ≫ pullback.fst A.hom g =
      pullback.fst A.hom fg := by
  subst fg
  exact MorphismProperty.Over.pullbackComp_left_fst_fst f g A

/-- A section of the inverse image of one stage sheaf lifts to a later stage.
Source: Stacks Project, Sites Tag 09YN, proof of lemma-colimit, and Étale
Cohomology Tag 09YQ, degree-zero affine-site comparison.
(blueprint: lem-weil-pbc-fixed-abelian-descended-section-lift).

Proof: Restrict the scheme diagram to the directed upper tail of i. Its limit
is the same scheme, since the tail is cofinal. Present its full affine étale
sites by the category colimit, using descent of finitely presented objects,
arrows, and equalities. The affine-site topos equivalence identifies inverse
images with their affine-site inverse images. The section formula of 09YN
for the single coefficient sheaf H expresses each inverse-image section as a
filtered colimit of its stage inverse-image sections. The first-projection
conditions on gamma and delta, and their equations over the base schemes,
uniquely identify their composites with the pullback-pasting comparison.
Uniqueness of adjoints identifies the section-colimit legs with the unit for
the limit projection followed by the inverse of upperStarComp and restriction
along that pasting comparison. Thus every affine section has a representative.
For a qcqs object, choose a finite affine cover and finite affine covers of its
pairwise intersections. Lift the finitely many sections on the cover to a
common stage; descend their overlap equalities to one further stage, using
the eventual equality assertion in the same filtered section colimits. The
sheaf condition glues the resulting matching family, and separatedness
identifies its limit image with the original section. The empty cover yields
the zero section; a nonempty tail supplies its stage. No varying coefficients,
transition maps between different coefficient sheaves, or sheaf colimit occur
in this assertion. -/
theorem fixed_abelian_descended_section_lift
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
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
    ∀ (i : J) (H : Sheaf (D.obj (op i.val)).smallEtaleTopology AddCommGrpCat.{u + 1})
      (y : ((upperStar AddCommGrpCat.{u + 1} (c.π.app (op i.val))).obj H).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤
          (c.π.app (op i.val))).obj (Tj i)))),
      ∃ (k : J) (a : i ⟶ k)
        (s : ((upperStar AddCommGrpCat.{u + 1}
          (D.map (show i.val ⟶ k.val from a).op)).obj H).obj.obj
            (op ((MorphismProperty.Over.pullback @Etale ⊤
              (D.map (show i.val ⟶ k.val from a).op)).obj (Tj i)))),
        (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
          (c.π.app (op k.val))).unit.app
            ((upperStar AddCommGrpCat.{u + 1}
              (D.map (show i.val ⟶ k.val from a).op)).obj H)).hom.app
                (op ((MorphismProperty.Over.pullback @Etale ⊤
                  (D.map (show i.val ⟶ k.val from a).op)).obj (Tj i))) ≫
          ((upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op k.val))
            (D.map (show i.val ⟶ k.val from a).op) (c.π.app (op i.val))
              (c.w (show i.val ⟶ k.val from a).op).symm).inv.app H).hom.app
                (op ((MorphismProperty.Over.pullback @Etale ⊤
                  (c.π.app (op k.val))).obj
                    ((MorphismProperty.Over.pullback @Etale ⊤
                      (D.map (show i.val ⟶ k.val from a).op)).obj (Tj i)))) ≫
          ((upperStar AddCommGrpCat.{u + 1} (c.π.app (op i.val))).obj H).obj.map
            ((δ i).hom ≫ (δ k).inv ≫
              (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op k.val))).map
                (γ i k a).inv).op) s = y := by
  classical
  intro J Tj Tlim γ δ hγ hδ i H y
  let : CompactSpace ((𝟭 Scheme).obj T₀.left) := ‹CompactSpace T₀.left›
  let : QuasiSeparatedSpace ((𝟭 Scheme).obj T₀.left) := ‹QuasiSeparatedSpace T₀.left›
  let : QuasiSeparatedSpace ((Functor.fromPUnit (D.obj (op i₀))).obj T₀.right) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj (op i₀)))
  let : QuasiCompact T₀.hom := quasiCompact_of_compactSpace T₀.hom
  let : QuasiSeparated T₀.hom := QuasiSeparated.of_quasiSeparatedSpace T₀.hom
  let : CompactSpace (Tj i).left := by
    change CompactSpace (pullback T₀.hom (D.map (homOfLE i.property).op) : Scheme)
    infer_instance
  let : QuasiSeparatedSpace (Tj i).left := by
    change QuasiSeparatedSpace (pullback T₀.hom (D.map (homOfLE i.property).op) : Scheme)
    exact quasiSeparatedSpace_of_quasiSeparated
      (pullback.snd T₀.hom (D.map (homOfLE i.property).op))
  let : QuasiCompact (Tj i).hom := by
    change QuasiCompact (pullback.snd T₀.hom (D.map (homOfLE i.property).op))
    infer_instance
  let : QuasiSeparated (Tj i).hom := by
    change QuasiSeparated (pullback.snd T₀.hom (D.map (homOfLE i.property).op))
    infer_instance
  obtain ⟨e, he⟩ := exists_abelianPullbackSectionComparison (D.obj (op i.val)) H
  let G := (sheafForget (D.obj (op i.val)).smallEtaleTopology).obj H
  obtain ⟨j, t, ht⟩ := etaleSetSectionLift D c hc i.val G (Tj i)
    (e c.pt (c.π.app (op i.val)) (Tj i) y)
  let k : J := ⟨j.left.unop, i.property.trans (leOfHom j.hom.unop)⟩
  let a : i ⟶ k := homOfLE (leOfHom j.hom.unop)
  let s := (e (D.obj j.left) (D.map j.hom) (Tj i)).symm t
  refine ⟨k, a, s, ?_⟩
  have hs := he (D.obj j.left) c.pt (c.π.app j.left) (D.map j.hom)
    (c.π.app (op i.val)) (c.w j.hom) (Tj i) s
  rw [Equiv.apply_symm_apply] at hs
  have hs' := (e c.pt (c.π.app (op i.val)) (Tj i)).injective (hs.trans ht)
  let b := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
    (c.π.app (op k.val)) (D.map (show i.val ⟶ k.val from a).op)
      (c.π.app (op i.val)) (c.w (show i.val ⟶ k.val from a).op).symm).hom.app (Tj i)
  let P := MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op k.val))
  have hb : b ≫ P.map (γ i k a).hom ≫ (δ k).hom = (δ i).hom := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · change b.left ≫ (P.map (γ i k a).hom).left ≫ (δ k).hom.left ≫
        pullback.fst T₀.hom (c.π.app (op i₀)) =
          (δ i).hom.left ≫ pullback.fst T₀.hom (c.π.app (op i₀))
      rw [hδ k, hδ i]
      simp only [P, MorphismProperty.Over.pullback_map_left, Category.assoc,
        pullback.lift_fst_assoc]
      rw [hγ i k a]
      have hfirst := pullbackComp_first (c.π.app (op k.val))
        (D.map (show i.val ⟶ k.val from a).op) (c.π.app (op i.val))
        (c.w (show i.val ⟶ k.val from a).op).symm (Tj i)
      exact congrArg (fun z ↦ z ≫ pullback.fst T₀.hom
        (D.map (homOfLE i.property).op)) hfirst
    · exact (b ≫ P.map (γ i k a).hom ≫ (δ k).hom).w.trans (δ i).hom.w.symm
  have hbeta : (δ i).hom ≫ (δ k).inv ≫ P.map (γ i k a).inv = b := by
    rw [← hb]
    calc
      _ = b ≫ P.map (γ i k a).hom ≫ P.map (γ i k a).inv := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
      _ = b ≫ P.map ((γ i k a).hom ≫ (γ i k a).inv) := by
        simp only [P.map_comp]
      _ = b := by
        rw [Iso.hom_inv_id, P.map_id]
        exact Category.comp_id _
  rw [hbeta]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStar_map_hom_app, lowerStarComp,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app] at hs'
  have hn := ((upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op k.val))
    (D.map (show i.val ⟶ k.val from a).op) (c.π.app (op i.val))
      (c.w (show i.val ⟶ k.val from a).op).symm).inv.app H).hom.naturality b.op
  have hn' := congrArg
    (fun q ↦ ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      (c.π.app (op k.val))).unit.app
        ((upperStar AddCommGrpCat.{u + 1} (D.map (show i.val ⟶ k.val from a).op)).obj H)).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤
            (D.map (show i.val ⟶ k.val from a).op)).obj (Tj i))) ≫ q) hn
  exact (ConcreteCategory.congr_hom hn' s).symm.trans hs'

end AlgebraicGeometry.Etale
