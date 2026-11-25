/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.CofilteredFixedBaseCohomologyContinuity
import WeilConjectures.AlgebraicGeometry.GrothendieckHypercoverComparison
import WeilConjectures.AlgebraicGeometry.GrothendieckHypercoverLimitGeneration
import WeilConjectures.AlgebraicGeometry.Sites.EtaleZariskiComparison
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived

/-!
# Continuity of étale cohomology at inverse limits

Let `(Xᵢ)` be a cofiltered system of quasi-compact quasi-separated schemes over a scheme `S`, with
affine transition maps and limit `X`, and let `F` be an étale sheaf on `S`. Then
`H^q(X, F|_X) = colimᵢ H^q(Xᵢ, F|_{Xᵢ})` ([Stacks, Tag 09YQ]). For abelian sheaves this is
`cohomologyMap_isColimit_of_isLimit`, in elementwise form, with vanishing form
`isZero_rightDerived_sectionsFunctor_upperStar_of_isLimit_addCommGrpCat`. The vanishing form for a
general Grothendieck abelian coefficient category is
`isZero_rightDerived_sectionsFunctor_upperStar_of_isLimit`.

## Main definitions

- `AlgebraicGeometry.Etale.sectionsFunctor`: the global sections functor of the small étale
  site, the sections over the terminal object.

## Implementation details

The elementwise form specialises `nonempty_isColimit_cofiltered_fixed_base_cohomology`. The
vanishing form for general coefficients is proved through finite split étale hypercovers: the
derived functors of sections are computed by hypercover cohomology, which commutes with the limit.

## References

* [Stacks, Tag 09YQ]
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The global sections functor `Γ(X, -)` on étale sheaves: the sections over the terminal
object `X` of the small étale site. -/
noncomputable abbrev sectionsFunctor (X : Scheme.{u}) : Sheaf X.smallEtaleTopology A ⥤ A :=
  sheafToPresheaf _ A ⋙
    (evaluation _ A).obj (op (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X)))

/-- Étale cohomology continuity, vanishing form: let `(Dᵢ)` be a cofiltered system of
quasi-compact quasi-separated schemes over `S` with affine transition maps and limit `X = c.pt`,
and let `F` be an étale sheaf on `S` with values in a Grothendieck abelian category `A`. If all
the `H^q(Dᵢ, F|_{Dᵢ})` vanish, then so does `H^q(X, F|_X)`. -/
theorem isZero_rightDerived_sectionsFunctor_upperStar_of_isLimit {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology A) {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over S) [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left] [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g).left]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c)) (q : ℕ)
    (h : ∀ i, IsZero (((sectionsFunctor A (D.obj i).left).rightDerived q).obj
      ((Etale.upperStar A (D.obj i).hom).obj F))) :
    IsZero (((sectionsFunctor A c.pt.left).rightDerived q).obj
      ((Etale.upperStar A c.pt.hom).obj F)) := by
  classical
  let D' := D ⋙ Over.forget S
  let c' := (Over.forget S).mapCone c
  have (i : I) : CompactSpace (D'.obj i) :=
    inferInstanceAs (CompactSpace (D.obj i).left)
  have (i : I) : QuasiSeparatedSpace (D'.obj i) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i).left)
  have {i j : I} (g : i ⟶ j) : IsAffineHom (D'.map g) :=
    inferInstanceAs (IsAffineHom (D.map g).left)
  have : CompactSpace c.pt.left := Scheme.compactSpace_of_isLimit D' c' hc
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  have : IsAffineHom (c'.π.app i) := isAffineHom_π_app D' c' hc i
  have : QuasiSeparatedSpace c.pt.left :=
    quasiSeparatedSpace_of_quasiSeparated (c'.π.app i)
  have hstage (j : I) :
      IsZero (FiniteSplitEtaleHypercover.hypercoverCohomology A
        ((Etale.upperStar A (D.obj j).hom).obj F) q) := by
    obtain ⟨e⟩ := FiniteSplitEtaleHypercover.nonempty_hypercoverCohomology_iso A q
      ((sectionsFunctor A (D.obj j).left).rightDerived q)
      (FiniteSplitEtaleHypercover.isCohomologyColimit_rightDerived_sections A
        (D.obj j).left q) ((Etale.upperStar A (D.obj j).hom).obj F)
    exact (h j).of_iso e
  obtain ⟨e⟩ := FiniteSplitEtaleHypercover.nonempty_hypercoverCohomology_iso A q
    ((sectionsFunctor A c.pt.left).rightDerived q)
    (FiniteSplitEtaleHypercover.isCohomologyColimit_rightDerived_sections A c.pt.left q)
    ((Etale.upperStar A c.pt.hom).obj F)
  have hlimit : IsZero (FiniteSplitEtaleHypercover.hypercoverCohomology A
      ((Etale.upperStar A c.pt.hom).obj F) q) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply FiniteSplitEtaleHypercover.hypercoverCohomology_limit_hom_ext A F D c hc q
    intro j
    exact (hstage j).eq_of_src _ _
  exact hlimit.of_iso e.symm

/-- Étale cohomology continuity, elementwise form: for a cofiltered system `(Dᵢ)` of
quasi-compact quasi-separated schemes over `S` with affine transition maps and limit `X = c.pt`,
and an abelian étale sheaf `F` on `S`, `Hᵠ(X, F|_X) = colimᵢ Hᵠ(Dᵢ, F|_{Dᵢ})` along
`AlgebraicGeometry.Etale.cohomologyMap`: every class on `X` comes from some `Dᵢ` (via
`F|_X ≅ (F|_{Dᵢ})|_X`), and a class on `Dᵢ` vanishing on `X` vanishes on some `Dⱼ`, `j ⟶ i`. -/
theorem cohomologyMap_isColimit_of_isLimit {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) {I : Type u} [SmallCategory I]
    [IsCofiltered I] (D : I ⥤ Over S) [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left] [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g).left]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c)) (q : ℕ) :
    (∀ x : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} c.pt.hom).obj F) q,
      ∃ (i : I) (y : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} (D.obj i).hom).obj F) q),
        Etale.cohomologyMap (c.π.app i).left _ q y =
          Sheaf.H.map ((Etale.upperStarComp AddCommGrpCat.{u + 1} (c.π.app i).left (D.obj i).hom
            c.pt.hom (Over.w (c.π.app i)).symm).hom.app F) q x) ∧
    ∀ (i : I) (y : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} (D.obj i).hom).obj F) q),
      Etale.cohomologyMap (c.π.app i).left _ q y = 0 →
        ∃ (j : I) (g : j ⟶ i), Etale.cohomologyMap (D.map g).left _ q y = 0 := by
  classical
  let D' := D ⋙ Over.forget S
  let π : D' ⟶ (Functor.const I).obj S :=
    { app := fun i ↦ (D.obj i).hom
      naturality := fun i j f ↦ by simp [D'] }
  have hπ {j k : I} (f : j ⟶ k) : π.app j = D'.map f ≫ π.app k := (Over.w (D.map f)).symm
  have ht (j : I) : c.pt.hom = ((Over.forget S).mapCone c).π.app j ≫ π.app j :=
    (Over.w (c.π.app j)).symm
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have (i : I) : CompactSpace (D'.obj i) := inferInstanceAs (CompactSpace (D.obj i).left)
  have (i : I) : QuasiSeparatedSpace (D'.obj i) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i).left)
  have {i j : I} (g : i ⟶ j) : IsAffineHom (D'.map g) :=
    inferInstanceAs (IsAffineHom (D.map g).left)
  have laws := cohomologyTriangleMap_laws S F q
  let H : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    { obj := fun j ↦ AddCommGrpCat.of
        (Sheaf.H (((π.app j.unop)^*[AddCommGrpCat.{u + 1}]).obj F) q)
      map := fun f ↦ AddCommGrpCat.ofHom
        (cohomologyTriangleMap (D'.map f.unop) (π.app _) (π.app _) (hπ f.unop) F q)
      map_id := by
        intro j
        dsimp
        simp only [D'.map_id]
        exact (congrArg AddCommGrpCat.ofHom
          (laws.1 (D'.obj j.unop) (π.app j.unop))).trans AddCommGrpCat.ofHom_id
      map_comp := by
        intro j k l f g
        dsimp
        simp only [D'.map_comp]
        exact (congrArg AddCommGrpCat.ofHom
          (laws.2 (D'.obj l.unop) (D'.obj k.unop) (D'.obj j.unop)
            (D'.map g.unop) (D'.map f.unop) (π.app j.unop) (π.app k.unop)
            (π.app l.unop) (hπ f.unop) (hπ g.unop))).trans
              (AddCommGrpCat.ofHom_comp _ _) }
  let B : Cocone H :=
    { pt := AddCommGrpCat.of (Sheaf.H (((c.pt.hom)^*[AddCommGrpCat.{u + 1}]).obj F) q)
      ι :=
        { app := fun j ↦ AddCommGrpCat.ofHom
            (cohomologyTriangleMap (c.π.app j.unop).left (π.app j.unop) c.pt.hom
              (ht j.unop) F q)
          naturality := by
            intro j k f
            dsimp
            simp only [Category.comp_id]
            have h := laws.2 c.pt.left (D'.obj k.unop) (D'.obj j.unop)
              (c.π.app k.unop).left (D'.map f.unop) (π.app j.unop) (π.app k.unop)
              c.pt.hom (hπ f.unop) (ht k.unop)
            simp only [D', Functor.comp_map, Over.forget_map, ← Over.comp_left,
              c.w f.unop] at h
            exact (AddCommGrpCat.ofHom_comp _ _).symm.trans
              (congrArg AddCommGrpCat.ofHom h).symm } }
  obtain ⟨hB⟩ := nonempty_isColimit_cofiltered_fixed_base_cohomology
    D' π ((Over.forget S).mapCone c) hc c.pt.hom ht F q H (fun j ↦ Iso.refl _)
    (fun j k f ↦ by simp [H]) B (Iso.refl _) (fun j ↦ by simp [B])
  -- `cohomologyTriangleMap` followed by the inverse-image comparison is `cohomologyMap`
  have key {X Y : Scheme.{u}} (f : X ⟶ Y) (a : Y ⟶ S) (b : X ⟶ S) (h : b = f ≫ a)
      (y : Sheaf.H (((a)^*[AddCommGrpCat.{u + 1}]).obj F) q) :
      Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} f a b h).hom.app F) q
        (cohomologyTriangleMap f a b h F q y) = cohomologyMap f _ q y := by
    unfold cohomologyTriangleMap
    rw [AddMonoidHom.comp_apply, ← Sheaf.H.map_comp_apply]
    simp
  refine ⟨fun x ↦ ?_, fun i y hy ↦ ?_⟩
  · obtain ⟨i, y, hy⟩ := Concrete.isColimit_exists_rep H hB x
    refine ⟨i.unop, y, ?_⟩
    rw [← key]
    exact congrArg _ hy
  · have h0 : B.ι.app (op i) y = B.ι.app (op i) 0 := by
      rw [map_zero]
      change cohomologyTriangleMap (c.π.app i).left (π.app i) c.pt.hom (ht i) F q y = 0
      have := congrArg (Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} (c.π.app i).left
        (π.app i) c.pt.hom (ht i)).inv.app F) q)
        ((key (c.π.app i).left (π.app i) c.pt.hom (ht i) y).trans hy)
      rw [← Sheaf.H.map_comp_apply, map_zero] at this
      simpa using this
    obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq H hB y 0 h0
    refine ⟨k.unop, f.unop, ?_⟩
    rw [map_zero] at hfg
    rw [← key (D.map f.unop).left (D.obj i).hom (D.obj k.unop).hom (hπ f.unop) y]
    change Sheaf.H.map _ q (H.map f y) = 0
    rw [hfg, map_zero]

/-- Étale cohomology continuity, vanishing form for abelian sheaves: let `(Dᵢ)` be a cofiltered
system of quasi-compact quasi-separated schemes over `S` with affine transition maps and limit
`X = c.pt`, and let `F` be an abelian étale sheaf on `S`. If all the `H^q(Dᵢ, F|_{Dᵢ})` vanish,
then so does `H^q(X, F|_X)`. -/
theorem isZero_rightDerived_sectionsFunctor_upperStar_of_isLimit_addCommGrpCat {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) {I : Type u} [SmallCategory I]
    [IsCofiltered I] (D : I ⥤ Over S) [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left] [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g).left]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c)) (q : ℕ)
    (h : ∀ i, IsZero (((sectionsFunctor AddCommGrpCat.{u + 1} (D.obj i).left).rightDerived q).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} (D.obj i).hom).obj F))) :
    IsZero (((sectionsFunctor AddCommGrpCat.{u + 1} c.pt.left).rightDerived q).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} c.pt.hom).obj F)) := by
  refine (Sheaf.subsingleton_H_iff_isZero_rightDerived c.pt.left.smallEtaleTopology
    (Scheme.isTerminalEtaleMkId c.pt.left) q _).1 (subsingleton_of_forall_eq 0 fun x ↦ ?_)
  obtain ⟨i, y, hy⟩ := (cohomologyMap_isColimit_of_isLimit F D c hc q).1 x
  have : Subsingleton (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} (D.obj i).hom).obj F) q) :=
    (Sheaf.subsingleton_H_iff_isZero_rightDerived (D.obj i).left.smallEtaleTopology
      (Scheme.isTerminalEtaleMkId (D.obj i).left) q _).2 (h i)
  rw [Subsingleton.elim y 0, map_zero] at hy
  have := congrArg (Sheaf.H.map ((Etale.upperStarComp AddCommGrpCat.{u + 1} (c.π.app i).left
    (D.obj i).hom c.pt.hom (Over.w (c.π.app i)).symm).inv.app F) q) hy
  rw [← Sheaf.H.map_comp_apply, map_zero] at this
  simpa using this.symm

end AlgebraicGeometry.Etale
