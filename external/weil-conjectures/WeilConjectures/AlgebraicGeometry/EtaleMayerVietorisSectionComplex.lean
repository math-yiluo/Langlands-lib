/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyMaps
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!
# Section complexes for an étale open cover

Source: Stacks Project, Tag 0A50, proof.
(blueprint: def-weil-pbc-etale-mayer-vietoris-section-complex).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- Evaluation of an abelian étale sheaf at an étale object.
Source: Stacks Project, Tag 0A50, proof. -/
noncomputable abbrev etaleSectionFunctor {X : Scheme.{u}} (W : X.Etale) :=
  sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (evaluation _ _).obj (op W)

/-- Restriction on complexes of sections.
Source: Stacks Project, Tag 0A50, proof. -/
noncomputable def etaleSectionMap {X : Scheme.{u}} {A B : X.Etale} (f : A ⟶ B)
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    ((etaleSectionFunctor B).mapHomologicalComplex (.up ℕ)).obj I ⟶
      ((etaleSectionFunctor A).mapHomologicalComplex (.up ℕ)).obj I :=
  (NatTrans.mapHomologicalComplex
    (Functor.whiskerLeft (sheafToPresheaf _ _) ((evaluation _ _).map f.op)) _).app I

/-- The restriction-pair and difference short complex of sections of a sheaf complex.
Source: Stacks Project, Tag 0A50, proof.
(blueprint: def-weil-pbc-etale-mayer-vietoris-section-complex) -/
noncomputable def etaleSectionShortComplex {X : Scheme.{u}} (U V : X.Opens)
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    ShortComplex (CochainComplex AddCommGrpCat.{u + 1} ℕ) := by
  let a : Scheme.Etale.mk U.ι ⟶ Scheme.Etale.mk (𝟙 X) :=
    MorphismProperty.Over.homMk U.ι (Category.comp_id _)
  let b : Scheme.Etale.mk V.ι ⟶ Scheme.Etale.mk (𝟙 X) :=
    MorphismProperty.Over.homMk V.ι (Category.comp_id _)
  let c : Scheme.Etale.mk (U ⊓ V).ι ⟶ Scheme.Etale.mk U.ι :=
    MorphismProperty.Over.homMk (X.homOfLE inf_le_left) (X.homOfLE_ι _)
  let d : Scheme.Etale.mk (U ⊓ V).ι ⟶ Scheme.Etale.mk V.ι :=
    MorphismProperty.Over.homMk (X.homOfLE inf_le_right) (X.homOfLE_ι _)
  refine ShortComplex.mk
    (biprod.lift (etaleSectionMap a I) (etaleSectionMap b I))
    (biprod.desc (etaleSectionMap c I) (-etaleSectionMap d I)) ?_
  simp only [biprod.lift_desc, Preadditive.comp_neg, ← sub_eq_add_neg, sub_eq_zero]
  apply HomologicalComplex.hom_ext
  intro n
  change (I.X n).obj.map a.op ≫ (I.X n).obj.map c.op =
    (I.X n).obj.map b.op ≫ (I.X n).obj.map d.op
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
  congr 2
  apply MorphismProperty.Over.Hom.ext
  exact (X.homOfLE_ι inf_le_left).trans (X.homOfLE_ι inf_le_right).symm


end AlgebraicGeometry.Etale
