/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.CofilteredFixedBaseCohomologyContinuity
import WeilConjectures.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Continuity of restricted étale cohomology over neighbourhoods

Source: Stacks Project, Étale Cohomology, Tags 09AX, 03Q6 and 09YQ.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

private abbrev AffineNhds (X : Scheme.{u}) (x : X) :=
  ObjectProperty.FullSubcategory
    (fun U : OpenNhds (X := X.toLocallyRingedSpace.toTopCat) x => IsAffineOpen U.1)

private noncomputable def affineNhdsDiagram (X : Scheme.{u}) (x : X) :
    AffineNhds X x ⥤ Scheme.{u} where
  obj U := Scheme.Opens.toScheme U.obj.1
  map f := X.homOfLE f.hom.le
  map_id U := X.homOfLE_rfl U.obj.1
  map_comp f g := (X.homOfLE_homOfLE f.hom.le g.hom.le).symm

private noncomputable def affineNhdsToBase (X : Scheme.{u}) (x : X) :
    affineNhdsDiagram X x ⟶ (Functor.const (AffineNhds X x)).obj X where
  app U := Scheme.Opens.ι U.obj.1
  naturality U V f := by
    change X.homOfLE f.hom.le ≫ Scheme.Opens.ι V.obj.1 =
      Scheme.Opens.ι U.obj.1 ≫ 𝟙 X
    rw [X.homOfLE_ι, Category.comp_id]

private noncomputable def affineNhdsCone (X : Scheme.{u}) (x : X)
    (g : ∀ U : OpenNhds (X := X.toLocallyRingedSpace.toTopCat) x,
      Spec (X.presheaf.stalk x) ⟶ (Scheme.Opens.toScheme U.1))
    (hg : ∀ U, X.fromSpecStalk x = g U ≫ (Scheme.Opens.ι U.1)) :
    Cone (affineNhdsDiagram X x) where
  pt := Spec (X.presheaf.stalk x)
  π :=
    { app := fun U => g U.obj
      naturality := by
        intro U V f
        simp only [Functor.const_obj_map]
        apply (cancel_mono (Scheme.Opens.ι V.obj.1)).mp
        change g V.obj ≫ Scheme.Opens.ι V.obj.1 =
          (g U.obj ≫ X.homOfLE f.hom.le) ≫ Scheme.Opens.ι V.obj.1
        rw [Category.assoc, X.homOfLE_ι, ← hg, ← hg] }

/-- The cohomology groups of the restricted sheaves have the canonical local-scheme
pullbacks as a colimit cocone. This statement concerns global cohomology on the open
schemes, and does not identify it with object cohomology on the original étale site.
Source: Stacks Project, Étale Cohomology, Tags 09AX, 03Q6 and 09YQ;
Limits of Schemes, Tag 0GWT.
(blueprint: lem-weil-pbc-etale-restricted-cohomology-neighbourhood-colimit).

Proof: The affine-open basis gives an affine neighbourhood inside every open
neighbourhood. Apply the full-subcategory cofilteredness and initiality criteria to
the inclusion of affine neighbourhoods. Taking opposites makes this inclusion final.
The inclusions of the affine open subschemes form a diagram E over X. Its objects are
qcqs and its transitions are affine by fromSpecStalk_limit_affine_neighbourhoods.
The supplied g are compatible: cancel the open immersion into X and use hg. They
therefore form a cone c with point Spec O_{X,x}. Cancel the same open immersions to
identify these projections with Mathlib's fromSpecStalkOfMem. The universal property
in fromSpecStalk_limit_affine_neighbourhoods then proves that c is a limit cone.
Whisker D and B by the opposite inclusion. The equations hD and hB are precisely the
transition and cocone equations of nonempty_isColimit_cofiltered_fixed_base_cohomology,
after unfolding cohomologyTriangleMap. Apply that theorem, then transfer its colimit
property back along the final inclusion. No quasi-compactness assumption on X or on
arbitrary open neighbourhoods is needed; only the affine stages are used.

Edge cases: q = 0 and F = 0 are included. There are no empty neighbourhoods of x;
X itself may be non-quasi-separated. If X is empty the point hypothesis is empty. -/
theorem etaleRestrictedCohomology_neighbourhood_colimit
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (x : X) (q : ℕ)
    (D : (OpenNhds (X := X.toLocallyRingedSpace.toTopCat) x)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (eD : ∀ U : OpenNhds (X := X.toLocallyRingedSpace.toTopCat) x,
      D.obj (op U) ≅ AddCommGrpCat.of
        (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} (Scheme.Opens.ι U.1)).obj F) q))
    (hD : ∀ (U V : OpenNhds (X := X.toLocallyRingedSpace.toTopCat) x) (f : V ⟶ U),
      D.map f.op = (eD U).hom ≫ AddCommGrpCat.ofHom
        (Etale.cohomologyMap (X.homOfLE f.le)
          ((Etale.upperStar AddCommGrpCat.{u + 1} (Scheme.Opens.ι U.1)).obj F) q) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map
          ((Etale.upperStarComp AddCommGrpCat.{u + 1} (X.homOfLE f.le)
            (Scheme.Opens.ι U.1) (Scheme.Opens.ι V.1)
            (X.homOfLE_ι f.le).symm).inv.app F) q) ≫ (eD V).inv)
    (g : ∀ U : OpenNhds (X := X.toLocallyRingedSpace.toTopCat) x,
      Spec (X.presheaf.stalk x) ⟶ (Scheme.Opens.toScheme U.1))
    (hg : ∀ U, X.fromSpecStalk x = g U ≫ (Scheme.Opens.ι U.1))
    (B : Cocone D)
    (b : B.pt ≅ AddCommGrpCat.of
      (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1}
        (X.fromSpecStalk x)).obj F) q))
    (hB : ∀ U, B.ι.app (op U) ≫ b.hom =
      (eD U).hom ≫ AddCommGrpCat.ofHom
        (Etale.cohomologyMap (g U)
          ((Etale.upperStar AddCommGrpCat.{u + 1} (Scheme.Opens.ι U.1)).obj F) q) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map
          ((Etale.upperStarComp AddCommGrpCat.{u + 1} (g U) (Scheme.Opens.ι U.1)
            (X.fromSpecStalk x) (hg U)).inv.app F) q)) :
    Nonempty (IsColimit B) := by
  classical
  obtain ⟨hbasis, _, _, _, _, hqc, haff, _, _, hlim⟩ :=
    Scheme.fromSpecStalk_limit_affine_neighbourhoods X x
  let affine : ObjectProperty (OpenNhds (X := X.toLocallyRingedSpace.toTopCat) x) :=
    fun U => IsAffineOpen U.1
  let A := affine.FullSubcategory
  let i : A ⥤ OpenNhds (X := X.toLocallyRingedSpace.toTopCat) x := affine.ι
  have hsmall : ∀ U, ∃ V : A, Nonempty (i.obj V ⟶ U) := by
    intro U
    obtain ⟨W, hW, hxW, hWU⟩ := hbasis U.1 U.2
    exact ⟨⟨⟨W, hxW⟩, hW⟩, ⟨homOfLE hWU⟩⟩
  have : IsCofiltered A :=
    IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful i hsmall
  have : i.Initial := Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful i hsmall
  let E : A ⥤ Scheme.{u} := affineNhdsDiagram X x
  let π : E ⟶ (Functor.const A).obj X := affineNhdsToBase X x
  have hqcE (U : A) : CompactSpace (E.obj U) ∧ QuasiSeparatedSpace (E.obj U) :=
    hqc ⟨U.obj.1, U.property, U.obj.2⟩
  have (U : A) : CompactSpace (E.obj U) := (hqcE U).1
  have (U : A) : QuasiSeparatedSpace (E.obj U) := (hqcE U).2
  have {U V : A} (f : U ⟶ V) : IsAffineHom (E.map f) :=
    (haff ⟨V.obj.1, V.property, V.obj.2⟩ ⟨U.obj.1, U.property, U.obj.2⟩ f.hom.le).2
  let c : Cone E := affineNhdsCone X x g hg
  let toA := fun W : {W : X.Opens // IsAffineOpen W ∧ x ∈ W} =>
    (⟨⟨W.1, W.2.2⟩, W.2.1⟩ : A)
  have hcanonical (W : {W : X.Opens // IsAffineOpen W ∧ x ∈ W}) :
      W.1.fromSpecStalkOfMem x W.2.2 = g (toA W).obj := by
    apply (cancel_mono W.1.ι).mp
    exact (Scheme.Opens.fromSpecStalkOfMem_ι W.1 x W.2.2).trans (hg (toA W).obj)
  have hc : IsLimit c := by
    apply IsLimit.ofExistsUnique
    intro s
    have hfamily := hlim s.pt (fun W => s.π.app (toA W)) (by
      intro W V hVW
      let f : toA V ⟶ toA W := ObjectProperty.homMk (homOfLE hVW)
      exact s.w f)
    obtain ⟨t, ht, huniq⟩ := hfamily
    refine ⟨t, ?_, ?_⟩
    · intro U
      have h := ht ⟨U.obj.1, U.property, U.obj.2⟩
      rw [hcanonical] at h
      exact h
    · intro t' ht'
      apply huniq
      intro W
      rw [hcanonical]
      exact ht' (toA W)
  have hH : ∀ (U V : A) (f : U ⟶ V), (i.op ⋙ D).map f.op =
      (eD V.obj).hom ≫ AddCommGrpCat.ofHom
        (Etale.cohomologyTriangleMap (E.map f) (π.app V) (π.app U)
          (by
            have h := (π.naturality f).symm
            change π.app U ≫ 𝟙 X = E.map f ≫ π.app V at h
            exact (Category.comp_id _).symm.trans h) F q) ≫ (eD U.obj).inv := by
    intro U V f
    dsimp only [Etale.cohomologyTriangleMap]
    rw [AddCommGrpCat.ofHom_comp]
    exact hD V.obj U.obj f.hom
  have hBc : ∀ U : A, (B.whisker i.op).ι.app (op U) ≫ b.hom =
      (eD U.obj).hom ≫ AddCommGrpCat.ofHom
        (Etale.cohomologyTriangleMap (c.π.app U) (π.app U) (X.fromSpecStalk x)
          (hg U.obj) F q) := by
    intro U
    dsimp only [Etale.cohomologyTriangleMap]
    rw [AddCommGrpCat.ofHom_comp]
    exact hB U.obj
  obtain ⟨hcolim⟩ := Etale.nonempty_isColimit_cofiltered_fixed_base_cohomology
    E π c hc (X.fromSpecStalk x) (fun U => hg U.obj) F q (i.op ⋙ D)
    (fun U => eD U.obj) hH (B.whisker i.op) b hBc
  exact ⟨Functor.Final.isColimitWhiskerEquiv i.op B hcolim⟩


end AlgebraicGeometry
