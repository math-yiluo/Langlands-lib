/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluation
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality

/-! # HomComplexUnitEvaluationComm

Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
(blueprint: lem-sc-hom-complex-unit-evaluation-comm).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory Opposite
namespace CategoryTheory
variable {C : Type u} [SmallCategory C]
  (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})

private lemma homMap_zero_left
    {A A' B B' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} (g : B ⟶ B') :
    SheafOfModules.homObjMap (R := R) (0 : A' ⟶ A) g = 0 :=
  SheafOfModules.hom_ext (PresheafOfModules.homObjMap_zero_left g.val)

/-- Evaluation at one commutes with the Hom-complex differential.
Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
(blueprint: lem-sc-hom-complex-unit-evaluation-comm).

Proof: apply the differential-projection identity in `homComplex_exists` at
source index zero, with q=m, q'=n and p'=m-n. The precomposition term vanishes
because every differential of the single complex is zero; internal Hom sends
zero precomposition to zero. The remaining term is the projection in degree n
followed by postcomposition with M.d n m. Transport along the zero-degree
single-complex isomorphism commutes with postcomposition by associativity.
Evaluation at one also commutes with postcomposition: both sides send a
localized linear map a to (M.d n m)(a(1)). This is an equality of restrictions
and linear maps, hence of sheaf morphisms. Reassociate these equalities to
obtain the displayed identity. No degree except adjacent degrees is required. -/
theorem homComplex_unit_evaluation_comm
    (M : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (n m : ℤ) (h : n + 1 = m) :
    homComplexUnitEvaluation J R M n ≫ M.d n m =
      ((homComplexUnitFunctor J R).obj M).d n m ≫
        homComplexUnitEvaluation J R M m := by
  let L := homComplexUnitSource J R
  let π := Classical.choose
    (homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R))
  have hd := (Classical.choose_spec
    (homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R))).2.1
      L M n m 0 m n (m - n) h (by omega) (by omega) (by omega)
  simp only [show L.d 0 (m - n) = 0 from rfl, homMap_zero_left J R,
    CategoryTheory.Limits.comp_zero, smul_zero, sub_zero] at hd
  change ((homComplexUnitFunctor J R).obj M).d n m ≫ π L M m 0 m (by omega) =
    π L M n 0 n (by omega) ≫
      SheafOfModules.homObjMap (R := R) (𝟙 (L.X 0)) (M.d n m) at hd
  let s : L.X 0 ≅
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
    HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
  have swap :
      SheafOfModules.homObjMap (R := R) (𝟙 (L.X 0)) (M.d n m) ≫
        SheafOfModules.homObjMap (R := R) s.inv (𝟙 (M.X m)) =
      SheafOfModules.homObjMap (R := R) s.inv (𝟙 (M.X n)) ≫
        SheafOfModules.homObjMap (R := R) (𝟙 _) (M.d n m) := by
    simp only [SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp,
      Category.comp_id]
  symm
  change ((homComplexUnitFunctor J R).obj M).d n m ≫
      (π L M m 0 m (by omega) ≫
        SheafOfModules.homObjMap (R := R) s.inv (𝟙 (M.X m)) ≫
          (SheafOfModules.homObjUnitIso (M.X m)).hom) =
    (π L M n 0 n (by omega) ≫
      SheafOfModules.homObjMap (R := R) s.inv (𝟙 (M.X n)) ≫
        (SheafOfModules.homObjUnitIso (M.X n)).hom) ≫ M.d n m
  dsimp only [homComplexUnitFunctor] at hd ⊢
  simp only [← Category.assoc]
  rw [hd]
  simp only [Category.assoc]
  rw [← Category.assoc (SheafOfModules.homObjMap (R := R) (𝟙 (L.X 0)) (M.d n m)),
    swap, Category.assoc, CategoryTheory.evaluation_naturality J R (M.d n m)]

end CategoryTheory
