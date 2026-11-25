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
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

set_option backward.isDefEq.respectTransparency false in
/-- A section on an affine neighbourhood that pulls back to zero on the local scheme
vanishes after shrinking the neighbourhood.
Source: Stacks Project, Tag 03Q6, Lemma 59.51.5, degree zero.
(blueprint: new-local-stalk-sections-affine-vanishing)

Proof: Write the affine neighbourhood A as Spec R and the point as a prime p.
The principal opens D(f), f outside p, form a directed system with coordinate-ring
colimit R_p. Restrict F to the small etale site of A. Apply degree-zero continuity
in Tag 03Q6 to the identity of A and the system R_f: this identity is quasi-compact
and quasi-separated. Restriction along an open immersion identifies sections of
the inverse image with F evaluated on that open. The continuity comparison sends
our section to its pullback on Spec R_p. Since this pullback is zero, the section
is zero at some principal-open stage. That principal open contains x and is the
required smaller neighbourhood. The identification Spec R_p = Spec(O_X,x) respects
the maps into A and X. For the arbitrary supplied left adjoint H, uniqueness of
left adjoints gives an isomorphism to the usual inverse image commuting with units;
therefore vanishing under the displayed cocone is precisely the vanishing used by
continuity. The zero section itself needs no shrinking, and an empty affine open
cannot be a neighbourhood of x. -/
theorem localStalkSections_affine_vanishing
    {X : Scheme.{u + 1}} (i : X.Opens ⥤ X.Etale)
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor) (x : X)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (Spec (X.presheaf.stalk x)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H ⊣ (X.fromSpecStalk x).Etale.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology
      (Spec (X.presheaf.stalk x)).smallEtaleTopology)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (A : (OpenNhds x)ᵒᵖ) (hA : IsAffineOpen A.unop.1)
    (s : (LocalStalkSections.neighbourhoodDiagram i x F).obj A)
    (hs : (LocalStalkSections.cocone i hi x H hH F).ι.app A s = 0) :
    ∃ (W : (OpenNhds x)ᵒᵖ) (f : A ⟶ W),
      (LocalStalkSections.neighbourhoodDiagram i x F).map f s = 0 := by
  classical
  obtain ⟨_, _, _, _, _, _, _, _, _, hlim⟩ :=
    Scheme.fromSpecStalk_limit_affine_neighbourhoods X x
  let affine : ObjectProperty (OpenNhds x) := fun U ↦ IsAffineOpen U.1
  let N := affine.FullSubcategory
  let j : N ⥤ OpenNhds x := affine.ι
  have hsmall : ∀ U, ∃ V : N, Nonempty (j.obj V ⟶ U) := by
    intro U
    obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset U.2
    exact ⟨⟨⟨W, hxW⟩, hW⟩, ⟨homOfLE hWU⟩⟩
  have : IsCofiltered N :=
    IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful j hsmall
  let D : N ⥤ X.Etale := j ⋙ OpenNhds.inclusion x ⋙ i
  have (U : N) : IsAffine (D.obj U).left := by
    have : IsAffine (X.restrictFunctor.obj U.obj.1).left := U.property
    exact IsAffine.of_isIso (LocalStalkSections.openIso i hi U.obj.1).hom.left
  have hw (U : N) : (LocalStalkSections.openIso i hi U.obj.1).hom.left ≫
      Scheme.Opens.ι (X := X) U.obj.1 = (i.obj U.obj.1).hom :=
    (LocalStalkSections.openIso i hi U.obj.1).hom.w
  have (U : N) : IsOpenImmersion (D.obj U).hom := by
    change IsOpenImmersion (i.obj U.obj.1).hom
    rw [← hw U]
    infer_instance
  have hmap {U V : N} (f : U ⟶ V) :
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
  have hcanonical (U : N) : c.π.app U ≫
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
      (⟨⟨W.1, W.2.2⟩, W.2.1⟩ : N)
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
  let a : N := ⟨A.unop, hA⟩
  have hz : B.ι.app (op a) s = B.ι.app (op a) 0 := by
    change (LocalStalkSections.cocone i hi x H hH F).ι.app A s =
      (LocalStalkSections.cocone i hi x H hH F).ι.app A 0
    rw [hs, map_zero]
  obtain ⟨W, f, g, hf⟩ := Concrete.isColimit_exists_of_rep_eq _ (i := op a) (j := op a) hB s 0 hz
  have hf' : (D.op ⋙ F.obj).map f s = 0 :=
    hf.trans (((D.op ⋙ F.obj).map g).hom.map_zero)
  refine ⟨j.op.obj W, j.op.map f, ?_⟩
  simpa [D, LocalStalkSections.neighbourhoodDiagram, j, a] using hf'
