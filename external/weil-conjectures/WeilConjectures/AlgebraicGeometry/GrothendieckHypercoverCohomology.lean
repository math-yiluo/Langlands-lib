/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.HypercoverCohomologyColimit
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Filtered.Basic
import WeilConjectures.AlgebraicGeometry.FiniteSplitHypercoverRefinement
import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
import Mathlib.Algebra.Homology.Opposite

/-! # A concrete hypercover cohomology object for Grothendieck coefficients

The indexing category keeps actual finite split hypercovers and quotients their
refinements by simplicial homotopy. Geometric refinement makes its opposite
filtered. The cohomology object is a colimit of the alternating cochain cohomologies.

Source: blueprint corollary-cohomology-pro-etale-affine, hypercover construction;
Stacks Project, Hypercoverings, Tag 01H0.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite AlgebraicTopology

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]

/-- The category of finite split étale hypercovers and actual simplicial refinements. -/
abbrev Index (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :=
  InducedCategory (SimplicialObject X.Etale)
    (fun U : FiniteSplitEtaleHypercover X ↦ U.simplicial)

variable (A : Type u') [Category.{u + 1} A] [Abelian A]

private theorem generalCofaceDEq (K : CosimplicialObject A) (i j : ℕ) :
    (((alternatingFaceMapComplex Aᵒᵖ).obj K.op).d j i).unop =
      ((alternatingCofaceMapComplex A).obj K).d i j := by
  by_cases hij : i + 1 = j
  · subst j
    simp only [alternatingFaceMapComplex_obj_d, alternatingCofaceMapComplex,
      AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
      AlternatingCofaceMapComplex.objD, AlternatingFaceMapComplex.objD,
      unop_sum, unop_zsmul]
    rfl
  · simp [alternatingFaceMapComplex, AlternatingFaceMapComplex.obj,
      alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj,
      hij]

private noncomputable def generalCofaceUnopIso (K : CosimplicialObject A) :
    (alternatingCofaceMapComplex A).obj K ≅
      ((alternatingFaceMapComplex Aᵒᵖ).obj K.op).unop :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    intro i j _
    simpa using (generalCofaceDEq A K i j))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def generalRefinementCochainHomotopy
    {U V : FiniteSplitEtaleHypercover X} (f g : U.Refinement V)
    (h : SimplicialObject.Homotopy f g)
    (F : Sheaf X.smallEtaleTopology A) :
    Homotopy
      ((alternatingCofaceMapComplex A).map
        (Functor.whiskerRight f.rightOp F.obj))
      ((alternatingCofaceMapComplex A).map
        (Functor.whiskerRight g.rightOp F.obj)) := by
  let h' := (h.whiskerRight F.obj.rightOp).toChainHomotopy.unop
  let eU := generalCofaceUnopIso A (U.simplicial.rightOp ⋙ F.obj)
  let eV := generalCofaceUnopIso A (V.simplicial.rightOp ⋙ F.obj)
  convert (h'.compLeft eV.hom).compRight eU.inv using 1 <;>
    first
    | rfl
    | ext n
      simp only [eU, eV, generalCofaceUnopIso,
        alternatingCofaceMapComplex_map, AlternatingCofaceMapComplex.map,
        Functor.whiskerRight_app, Functor.rightOp_obj, NatTrans.rightOp_app,
        Category.assoc, HomologicalComplex.comp_f, HomologicalComplex.unopFunctor_map_f,
        alternatingFaceMapComplex_obj_X, Quiver.Hom.unop_op,
        alternatingFaceMapComplex_map_f, Functor.whiskeringRight_obj_map,
        Functor.rightOp_map, HomologicalComplex.Hom.isoOfComponents_hom_f,
        HomologicalComplex.Hom.isoOfComponents_inv_f, Iso.refl_hom, Iso.refl_inv,
        Category.id_comp]
      exact (Category.comp_id _).symm

/-- Simplicially homotopic refinements induce equal maps on cochain cohomology. -/
theorem cohomologyRefinement_homotopy_invariant (q : ℕ)
    {U V : FiniteSplitEtaleHypercover X} (f g : U.Refinement V)
    (h : isRefinementHomotopic f g) :
    cohomologyRefinement A f q =
      cohomologyRefinement A g q := by
  induction h with
  | rel f g h =>
      obtain ⟨h⟩ := h
      apply NatTrans.ext
      funext F
      exact (generalRefinementCochainHomotopy A f g h F).homologyMap_eq q
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂


/-- The cosimplicial section objects, contravariant in hypercover refinements. -/
noncomputable def sectionDiagram (F : Sheaf X.smallEtaleTopology A) :
    (Index X)ᵒᵖ ⥤ CosimplicialObject A where
  obj U := U.unop.simplicial.rightOp ⋙ F.obj
  map f := Functor.whiskerRight f.unop.hom.rightOp F.obj
  map_id U := by
    ext n
    simp
  map_comp f g := by
    ext n
    simp

/-- The cohomology of the alternating section complexes, contravariant in refinements. -/
noncomputable def cohomologyDiagram (F : Sheaf X.smallEtaleTopology A) (q : ℕ) :
    (Index X)ᵒᵖ ⥤ A :=
  sectionDiagram A F ⋙ AlgebraicTopology.alternatingCofaceMapComplex A ⋙
    HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q

/-- Homotopy of refinements, oriented in the direction of cochain maps. -/
def refinementRelation : HomRel (Index X)ᵒᵖ :=
  fun _ _ f g ↦ isRefinementHomotopic f.unop.hom g.unop.hom

/-- Finite split hypercovers with refinements modulo simplicial homotopy,
oriented in the direction of cochain maps. -/
abbrev HomotopyIndex (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :=
  CategoryTheory.Quotient (refinementRelation (X := X))

/-- The geometric common-refinement and homotopy-equalization lemmas make the
homotopy index filtered. -/
instance : IsFiltered (HomotopyIndex X) where
  nonempty := by
    obtain ⟨U⟩ := (exists_and_cofiltered X).1
    exact ⟨⟨op U⟩⟩
  cocone_objs U V := by
    obtain ⟨W, ⟨f⟩, ⟨g⟩⟩ := (exists_and_cofiltered X).2.1 U.as.unop V.as.unop
    let f' : (show Index X from W) ⟶ (show Index X from U.as.unop) := ⟨f⟩
    let g' : (show Index X from W) ⟶ (show Index X from V.as.unop) := ⟨g⟩
    exact ⟨⟨op W⟩, (CategoryTheory.Quotient.functor _).map f'.op,
      (CategoryTheory.Quotient.functor _).map g'.op, trivial⟩
  cocone_maps := by
    rintro ⟨U⟩ ⟨V⟩ f g
    refine Quot.inductionOn f ?_
    intro f
    refine Quot.inductionOn g ?_
    intro g
    obtain ⟨W, c, hc⟩ := (exists_and_cofiltered X).2.2 V.unop U.unop
      f.unop.hom g.unop.hom
    let c' : (show Index X from W) ⟶ (show Index X from V.unop) := ⟨c⟩
    refine ⟨⟨op W⟩, (CategoryTheory.Quotient.functor _).map c'.op, ?_⟩
    change (CategoryTheory.Quotient.functor _).map f ≫
      (CategoryTheory.Quotient.functor _).map c'.op =
      (CategoryTheory.Quotient.functor _).map g ≫
        (CategoryTheory.Quotient.functor _).map c'.op
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact CategoryTheory.Quotient.sound _ hc

/-- The filtered diagram of hypercover cohomologies. Simplicial homotopies induce
chain homotopies, so cochain cohomology descends to the homotopy quotient. -/
noncomputable def homotopyCohomologyDiagram
    (F : Sheaf X.smallEtaleTopology A) (q : ℕ) : HomotopyIndex X ⥤ A :=
  CategoryTheory.Quotient.lift _ (cohomologyDiagram A F q)
    (fun _ _ f g h ↦ congrArg (fun t ↦ t.app F)
      (cohomologyRefinement_homotopy_invariant A q f.unop.hom g.unop.hom h))

variable [IsGrothendieckAbelian.{u + 1} A]

local instance : HasColimitsOfSize.{u, u + 1} A :=
  hasColimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} A

/-- Hypercover cohomology, constructed as a colimit of the actual cochain cohomologies. -/
noncomputable def hypercoverCohomology (F : Sheaf X.smallEtaleTopology A) (q : ℕ) : A :=
  colimit (homotopyCohomologyDiagram A F q)

set_option backward.isDefEq.respectTransparency false in
/-- Any functor satisfying the existing hypercover universal property computes this
concrete colimit. The proof uses only the universal property of a colimit. -/
theorem nonempty_hypercoverCohomology_iso
    (q : ℕ) (H : Sheaf X.smallEtaleTopology A ⥤ A)
    (hH : IsCohomologyColimit A q H) (F : Sheaf X.smallEtaleTopology A) :
    Nonempty (hypercoverCohomology A F q ≅ H.obj F) := by
  obtain ⟨_, c, hc, huniq⟩ := hH
  let B : Cocone (homotopyCohomologyDiagram A F q) :=
    { pt := H.obj F
      ι :=
        { app := fun U ↦ (c U.as.unop).app F
          naturality := by
            rintro ⟨U⟩ ⟨V⟩ f
            refine Quot.inductionOn f ?_
            intro f
            change (cohomologyRefinement A f.unop.hom q).app F ≫
              (c V.unop).app F = (c U.unop).app F ≫ 𝟙 _
            simpa only [Category.comp_id, NatTrans.comp_app] using
              congrArg (fun t ↦ t.app F) (hc V.unop U.unop f.unop.hom) } }
  have hB : IsColimit B := by
    apply IsColimit.ofExistsUnique
    intro s
    let d (U : FiniteSplitEtaleHypercover X) :
        (cohomologyFunctor A U q).obj F ⟶ s.pt := s.ι.app ⟨op U⟩
    have hd (U V : FiniteSplitEtaleHypercover X) (f : U.Refinement V) :
        (cohomologyRefinement A f q).app F ≫ d U = d V := by
      let f' : (show Index X from U) ⟶ (show Index X from V) := ⟨f⟩
      have hh := s.w ((CategoryTheory.Quotient.functor _).map f'.op)
      change (cohomologyRefinement A f q).app F ≫ d U = d V at hh
      exact hh
    obtain ⟨e, he, hu⟩ := huniq F s.pt d hd
    refine ⟨e, ?_, ?_⟩
    · intro U
      exact he U.as.unop
    · intro e' he'
      apply hu e'
      intro U
      exact he' ⟨op U⟩
  exact ⟨(colimit.isColimit _).coconePointUniqueUpToIso hB⟩

end AlgebraicGeometry.FiniteSplitEtaleHypercover
