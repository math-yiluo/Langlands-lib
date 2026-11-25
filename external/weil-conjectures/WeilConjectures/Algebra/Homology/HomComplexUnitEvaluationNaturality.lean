/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluation

/-! # HomComplexUnitEvaluationNaturality

Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
(blueprint: lem-sc-hom-complex-unit-evaluation-naturality).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory Opposite
namespace CategoryTheory
variable {C : Type u} [SmallCategory C]
  (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})

/-- Evaluation at one commutes with postcomposition.
Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
(blueprint: lem-sc-hom-complex-unit-evaluation-naturality).
Proof: on each localized site both composites send a linear map φ to g(φ(1));
extensionality of the underlying presheaf morphisms proves the equality. -/
lemma evaluation_naturality
    {A B : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} (g : A ⟶ B) :
    SheafOfModules.homObjMap (R := R) (𝟙 _) g ≫
      (SheafOfModules.homObjUnitIso B).hom =
    (SheafOfModules.homObjUnitIso A).hom ≫ g := by
  apply SheafOfModules.hom_ext
  ext X φ : 3
  rfl

-- Dependent projection and sheaf types require extra elaboration steps.
/-- Degreewise evaluation at one commutes with a chain map.
Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
(blueprint: lem-sc-hom-complex-unit-evaluation-naturality).

Proof: specialize the componentwise map identity in `homComplex_exists` to
the identity on the unit single complex, a chain map f in the target, and source
degree zero. The identity functor map disappears. Thus projection after the
Hom-complex map equals projection followed by internal Hom postcomposition
with f.f n. Transport along the zero-degree single-complex isomorphism commutes
with postcomposition by the internal-Hom composition law. Evaluation at one
commutes with f.f n since both sides take a localized linear map a to
(f.f n)(a(1)). Sectionwise extensionality and reassociation yield the equation.
No invertibility or differential compatibility is needed for this identity. -/
theorem homComplex_unit_evaluation_naturality
    {M N : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ}
    (f : M ⟶ N) (n : ℤ) :
    ((homComplexUnitFunctor J R).map f).f n ≫ homComplexUnitEvaluation J R N n =
      homComplexUnitEvaluation J R M n ≫ f.f n := by
  let L := homComplexUnitSource J R
  let π := Classical.choose
    (homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R))
  have hm := (Classical.choose_spec
    (homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R))).2.2
      L L M N (𝟙 L) f n 0 n (by omega)
  simp only [op_id, Functor.map_id, NatTrans.id_app, Category.id_comp] at hm
  change ((homComplexUnitFunctor J R).map f).f n ≫ π L N n 0 n (by omega) =
    π L M n 0 n (by omega) ≫
      SheafOfModules.homObjMap (R := R) (𝟙 (L.X 0)) (f.f n) at hm
  let s : L.X 0 ≅
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
    HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
  have swap :
      SheafOfModules.homObjMap (R := R) (𝟙 (L.X 0)) (f.f n) ≫
        SheafOfModules.homObjMap (R := R) s.inv (𝟙 (N.X n)) =
      SheafOfModules.homObjMap (R := R) s.inv (𝟙 (M.X n)) ≫
        SheafOfModules.homObjMap (R := R) (𝟙 _) (f.f n) := by
    simp only [SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp,
      Category.comp_id]
  change ((homComplexUnitFunctor J R).map f).f n ≫
      (π L N n 0 n (by omega) ≫
        SheafOfModules.homObjMap (R := R) s.inv (𝟙 (N.X n)) ≫
          (SheafOfModules.homObjUnitIso (N.X n)).hom) =
    (π L M n 0 n (by omega) ≫
      SheafOfModules.homObjMap (R := R) s.inv (𝟙 (M.X n)) ≫
        (SheafOfModules.homObjUnitIso (M.X n)).hom) ≫ f.f n
  dsimp only [homComplexUnitFunctor] at hm ⊢
  simp only [← Category.assoc]
  rw [hm]
  simp only [Category.assoc]
  rw [← Category.assoc (SheafOfModules.homObjMap (R := R) (𝟙 (L.X 0)) (f.f n)),
    swap, Category.assoc, evaluation_naturality J R (f.f n)]

end CategoryTheory
