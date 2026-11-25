/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocalStalkSectionsComparisonMap
import WeilConjectures.AlgebraicGeometry.LocalStalkSectionsCoconeColimit
import WeilConjectures.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Descent of sections from the local scheme

Source: Stacks Project, Tag 03Q6, degree zero of Lemma 59.51.5.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

set_option backward.isDefEq.respectTransparency false in
/-- Descent of sections from the local scheme.
Source: Stacks Project, Tag 03Q6, degree zero and proof steps (1)-(3).
(blueprint: new-local-stalk-sections-descent-sections)

Proof: Choose an affine neighbourhood V of x. Principal opens of V containing x
are cofinal among neighbourhoods of x: intersect any neighbourhood with V and use
the principal-open basis of V. The colimit of their coordinate rings is O_X,x.
Apply the degree-zero section assertion of Tag 03Q6 to the identity of V, which is
quasi-compact and quasi-separated, and to the restriction of F to V. Every section
of the inverse-image sheaf on Spec(O_X,x) descends to a section on one of these
principal opens. This gives the required neighbourhood U and section t. The maps
are the pullback maps given by the inverse-image unit and the local-scheme maps to
the neighbourhoods. Identify the standard inverse image with the displayed H by
uniqueness of left adjoints to the same direct image. This identification respects
the units and therefore identifies its pullback maps with LocalStalkSections.comparison.
Transport the descended section through that isomorphism to obtain the requested
representative. The zero sheaf is included; no henselian or global qcqs hypothesis is needed.
Small affine presentations keep the coefficient universe fixed; empty X has no x. -/
theorem localStalkSections_descent_sections
    {X : Scheme.{u + 1}} (i : X.Opens ⥤ X.Etale)
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor) (x : X)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (Spec (X.presheaf.stalk x)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H ⊣ (X.fromSpecStalk x).Etale.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology
      (Spec (X.presheaf.stalk x)).smallEtaleTopology)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (s : (H.obj F).obj.obj (op (Scheme.Etale.mk (𝟙 _)))) :
    ∃ (U : (OpenNhds x)ᵒᵖ) (t : (LocalStalkSections.neighbourhoodDiagram i x F).obj U),
      (LocalStalkSections.cocone i hi x H hH F).ι.app U t = s := by
  classical
  obtain ⟨_, _, _, _, _, _, _, _, _, hlim⟩ :=
    Scheme.fromSpecStalk_limit_affine_neighbourhoods X x
  let affine : ObjectProperty (OpenNhds x) := fun U ↦ IsAffineOpen U.1
  let A := affine.FullSubcategory
  let j : A ⥤ OpenNhds x := affine.ι
  have hsmall : ∀ U, ∃ V : A, Nonempty (j.obj V ⟶ U) := by
    intro U
    obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset U.2
    exact ⟨⟨⟨W, hxW⟩, hW⟩, ⟨homOfLE hWU⟩⟩
  have : IsCofiltered A :=
    IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful j hsmall
  let D : A ⥤ X.Etale := j ⋙ OpenNhds.inclusion x ⋙ i
  have (U : A) : IsAffine (D.obj U).left := by
    have : IsAffine (X.restrictFunctor.obj U.obj.1).left := U.property
    exact IsAffine.of_isIso (LocalStalkSections.openIso i hi U.obj.1).hom.left
  have hw (U : A) : (LocalStalkSections.openIso i hi U.obj.1).hom.left ≫
      Scheme.Opens.ι (X := X) U.obj.1 = (i.obj U.obj.1).hom :=
    (LocalStalkSections.openIso i hi U.obj.1).hom.w
  have (U : A) : IsOpenImmersion (D.obj U).hom := by
    change IsOpenImmersion (i.obj U.obj.1).hom
    rw [← hw U]
    infer_instance
  have hmap {U V : A} (f : U ⟶ V) :
      (D.map f).left ≫ (LocalStalkSections.openIso i hi V.obj.1).hom.left =
        (LocalStalkSections.openIso i hi U.obj.1).hom.left ≫ X.homOfLE f.hom.le := by
    apply (cancel_mono (Scheme.Opens.ι (X := X) V.obj.1)).mp
    rw [Category.assoc, hw V,
      Category.assoc, X.homOfLE_ι]
    exact (D.map f).w.trans (hw U).symm
  let c : Cone (D ⋙ Scheme.Etale.forget X ⋙ Over.forget X) :=
    { pt := Spec (X.presheaf.stalk x)
      π :=
        { app := fun U ↦ LocalStalkSections.lift i hi x U.obj
          naturality := by
            intro U V f
            change LocalStalkSections.lift i hi x V.obj =
              LocalStalkSections.lift i hi x U.obj ≫ (D.map f).left
            exact (LocalStalkSections.lift_naturality i hi x f.hom).symm } }
  have hcanonical (U : A) : c.π.app U ≫
      (LocalStalkSections.openIso i hi U.obj.1).hom.left =
        Scheme.Opens.fromSpecStalkOfMem (X := X) U.obj.1 x U.obj.2 := by
    apply (cancel_mono (Scheme.Opens.ι (X := X) U.obj.1)).mp
    rw [Category.assoc, hw U]
    exact (LocalStalkSections.lift_fac i hi x U.obj).trans
      (Scheme.Opens.fromSpecStalkOfMem_ι U.obj.1 x U.obj.2).symm
  have hc : IsLimit c := by
    apply IsLimit.ofExistsUnique
    intro a
    let toA := fun W : {W : X.Opens // IsAffineOpen W ∧ x ∈ W} ↦
      (⟨⟨W.1, W.2.2⟩, W.2.1⟩ : A)
    obtain ⟨t, ht, huniq⟩ := hlim a.pt
      (fun W ↦ a.π.app (toA W) ≫ (LocalStalkSections.openIso i hi W.1).hom.left) (by
        intro W V hVW
        let f : toA V ⟶ toA W := ObjectProperty.homMk (homOfLE hVW)
        rw [Category.assoc, ← hmap f, ← Category.assoc]
        exact congrArg (fun g ↦ g ≫ (LocalStalkSections.openIso i hi W.1).hom.left)
          (a.w f))
    refine ⟨t, ?_, ?_⟩
    · intro U
      apply (cancel_mono (LocalStalkSections.openIso i hi U.obj.1).hom.left).mp
      rw [Category.assoc, hcanonical]
      exact ht ⟨U.obj.1, U.property, U.obj.2⟩
    · intro t' ht'
      apply huniq t'
      intro W
      rw [← hcanonical (toA W), ← Category.assoc, ht']
  let B := (LocalStalkSections.cocone i hi x H hH F).whisker j.op
  obtain ⟨hB⟩ := affineOpenSections_cocone_isColimit D c (X.fromSpecStalk x)
    (fun U ↦ LocalStalkSections.lift_fac i hi x U.obj) hc H hH F B.ι (by
      intro U
      rfl)
  obtain ⟨U, t, ht⟩ := Concrete.isColimit_exists_rep _ hB s
  exact ⟨j.op.obj U, t, ht⟩
