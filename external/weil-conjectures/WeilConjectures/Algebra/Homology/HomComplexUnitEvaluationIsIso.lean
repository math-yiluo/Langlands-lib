/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluation
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! # HomComplexUnitEvaluationIsIso

Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
(blueprint: lem-sc-hom-complex-unit-evaluation-is-iso).
-/

@[expose] public section

universe u v v'
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
variable {C : Type u} [SmallCategory C]
  (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})

private lemma isIso_dependent {D : Type v} [Category.{v'} D] {A : D} {B : ℤ → D}
    {k : ℤ} (π : ∀ q, k = q → (A ⟶ B q)) {q : ℤ} (hq : k = q)
    (hi : IsIso (π k rfl)) : IsIso (π q hq) := by
  subst q
  exact hi

set_option backward.isDefEq.respectTransparency true in
-- Dependent projection and sheaf types require extra elaboration steps.
/-- The degreewise evaluation map is invertible.
Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
(blueprint: lem-sc-hom-complex-unit-evaluation-is-iso).

Proof: the specified projections form a limit fan. For nonzero source degree p,
the single complex has zero object, and its internal Hom to any target is zero:
every localized linear map from zero is zero. Thus projection to degree zero
is an isomorphism. Its inverse is the limit lift with identity at zero and zero
at every other index. The limit hom-ext principle proves both inverse identities.
Transport from the source's zero degree to the unit is an isomorphism under
internal Hom. Finally evaluation at one is `SheafOfModules.homObjUnitIso`.
Their composite is therefore an isomorphism. This includes zero rings, empty
sites, zero complexes, and every integer target degree. -/
theorem homComplex_unit_evaluation_isIso
    (M : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) (n : ℤ) :
    IsIso (homComplexUnitEvaluation J R M n) := by
  classical
  let L := homComplexUnitSource J R
  let π := Classical.choose
    (homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R))
  let Q := fun p : ℤ => SheafOfModules.homObj (R := R) (L.X p) (M.X (p + n))
  let P := ((homComplexFunctor (R := R)).obj (op L)).obj M
  have hc : IsLimit (Fan.mk (P.X n) (fun p : ℤ => π L M n p (p + n) rfl)) :=
    Classical.choice ((Classical.choose_spec
      (homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R))).1 L M n)
  have hz (p : ℤ) (h : p ≠ 0) : IsZero (Q p) := by
    exact (((SheafOfModules.homFunctor R).flip.obj (M.X (p + n))).map_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
          p h).op)
  let v : Q 0 ⟶ P.X n := Fan.IsLimit.lift hc
    (fun p => if h : p = 0 then eqToHom (congrArg Q h.symm) else 0)
  have hv : v ≫ π L M n 0 (0 + n) rfl = 𝟙 (Q 0) := by
    change Fan.IsLimit.lift hc _ ≫
      (Fan.mk (P.X n) (fun p : ℤ => π L M n p (p + n) rfl)).proj 0 = _
    rw [Fan.IsLimit.fac]
    simp
  have hπ : π L M n 0 (0 + n) rfl ≫ v = 𝟙 (P.X n) := by
    apply Fan.IsLimit.hom_ext hc
    intro p
    change (π L M n 0 (0 + n) rfl ≫ v) ≫ π L M n p (p + n) rfl =
      𝟙 (P.X n) ≫ π L M n p (p + n) rfl
    by_cases h : p = 0
    · subst p
      rw [Category.assoc, hv, Category.comp_id, Category.id_comp]
    · exact (hz p h).eq_of_tgt _ _
  have hi : IsIso (π L M n 0 (0 + n) rfl) :=
    (Iso.mk (π L M n 0 (0 + n) rfl) v hπ hv).isIso_hom
  have hi' : IsIso (π L M n 0 n (by omega)) := by
    exact isIso_dependent (fun q h => π L M n 0 q h) (by omega) hi
  let s : L.X 0 ≅
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
    HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
  have hs : IsIso (SheafOfModules.homObjMap (R := R) s.inv (𝟙 (M.X n))) := by
    change IsIso (((SheafOfModules.homFunctor R).flip.obj (M.X n)).map s.inv.op)
    infer_instance
  change IsIso (π L M n 0 n (by omega) ≫
    SheafOfModules.homObjMap (R := R) s.inv (𝟙 (M.X n)) ≫
      (SheafOfModules.homObjUnitIso (M.X n)).hom)
  infer_instance

end CategoryTheory
