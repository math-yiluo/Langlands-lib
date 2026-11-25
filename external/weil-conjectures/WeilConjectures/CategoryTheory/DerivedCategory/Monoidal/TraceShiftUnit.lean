/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Trace
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-!
# The trace of an endomorphism of a shifted unit

Let `A` be a braided monoidal closed Grothendieck abelian category with functorial flat
resolutions. For an endomorphism `r` of the unit of `A` and `n : ℤ`, the categorical trace in
`D(A)`, for the Koszul braiding `DerivedCategory.braidedCategory'`, of the shift by `n` of
`r[0] : 𝟙[0] ⟶ 𝟙[0]` is `(-1)ⁿ r[0]` (`DerivedCategory.trace_shiftFunctor_map_singleFunctor_map`):
the shifted unit is represented by the complex `𝟙` in degree `-n`, whose supertrace is
`(-1)⁻ⁿ tr(r)`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A]

local instance instHasColimitsOfSize_traceShiftUnit
    : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A

variable (A) in
/-- The termwise right duals of the complex `𝟙` concentrated in degree `m`: the unit in degree
`m`, and zero objects elsewhere. -/
@[instance_reducible]
noncomputable def singleUnitXHasRightDual (m n : ℤ) :
    HasRightDual (((HomologicalComplex.single A (.up ℤ) m).obj (𝟙_ A)).X n) :=
  if h : n = m then hasRightDualOfIso (HomologicalComplex.singleObjXIsoOfEq _ m (𝟙_ A) n h)
  else hasRightDualOfIsZero (HomologicalComplex.isZero_single_obj_X _ m _ n h)

omit [HasDerivedCategory A] [Abelian.HasFunctorialFlatResolution A] in
/-- The trace of `r` placed in degree `m` is `(-1)ᵐ r` placed in degree `0`, for the termwise
dual of the complex `𝟙[-m]`. -/
lemma trace_single_map (m : ℤ) (r : 𝟙_ A ⟶ 𝟙_ A) :
    letI := singleUnitXHasRightDual A m
    letI := CochainComplex.hasRightDual ((HomologicalComplex.single A (.up ℤ) m).obj (𝟙_ A)) m m
    trace ((HomologicalComplex.single A (.up ℤ) m).map r) =
      (m.negOnePow : ℤ) • (HomologicalComplex.single A (.up ℤ) 0).map r := by
  let := singleUnitXHasRightDual A m
  let := CochainComplex.hasRightDual ((HomologicalComplex.single A (.up ℤ) m).obj (𝟙_ A)) m m
  refine HomologicalComplex.from_single_hom_ext ?_
  rw [CochainComplex.trace_f_zero_eq _ m m, Finset.Icc_self, Finset.sum_singleton,
    HomologicalComplex.zsmul_f_apply, HomologicalComplex.single_map_f_self,
    trace_eq_of_iso (HomologicalComplex.singleObjXSelf (.up ℤ) m (𝟙_ A)) _ r
      (by simp),
    trace_tensorUnit, HomologicalComplex.single_map_f_self]
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul]

/-- **The trace of an endomorphism of a shifted unit**: for an endomorphism `r` of the unit of
`A` and `n : ℤ`, the trace in `D(A)`, for the Koszul braiding, of `r[0]⟦n⟧` is `(-1)ⁿ r[0]`. -/
theorem trace_shiftFunctor_map_singleFunctor_map (n : ℤ) (r : 𝟙_ A ⟶ 𝟙_ A)
    [HasRightDual ((shiftFunctor (DerivedCategory A) n).obj ((singleFunctor A 0).obj (𝟙_ A)))] :
    letI := braidedCategory' A
    trace ((shiftFunctor (DerivedCategory A) n).map ((singleFunctor A 0).map r)) =
      (quotientCompQhIso A).hom.app (𝟙_ (CochainComplex A ℤ)) ≫
        ((n.negOnePow : ℤ) • (singleFunctor A 0).map r) ≫
          (quotientCompQhIso A).inv.app (𝟙_ (CochainComplex A ℤ)) := by
  let := braidedCategory' A
  let P := (HomologicalComplex.single A (.up ℤ) (-n)).obj (𝟙_ A)
  let eX : (shiftFunctor (DerivedCategory A) n).obj ((singleFunctor A 0).obj (𝟙_ A)) ≅
      Qh.obj ((HomotopyCategory.quotient A (.up ℤ)).obj P) :=
    ((singleFunctors A).shiftIso n (-n) 0 (by lia)).app (𝟙_ A)
  have hnat : (shiftFunctor (DerivedCategory A) n).map ((singleFunctor A 0).map r) ≫ eX.hom =
      eX.hom ≫ Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map
        ((HomologicalComplex.single A (.up ℤ) (-n)).map r)) :=
    ((singleFunctors A).shiftIso n (-n) 0 (by lia)).hom.naturality r
  let : HasRightDual (Qh.obj ((HomotopyCategory.quotient A (.up ℤ)).obj P)) :=
    hasRightDualOfIso eX.symm
  let := singleUnitXHasRightDual A (-n)
  rw [trace_eq_of_iso eX _ _ hnat,
    trace_Qh_map_quotient_map (fun X Y _ _ ↦ braiding_hom_μ_Qh X Y) P (-n) (-n), trace_single_map,
    Int.negOnePow_neg]
  simp only [Functor.map_zsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  have hε : ε (Qh (C := A)) = 𝟙 _ := rfl
  simp only [hε, IsIso.inv_id, Category.id_comp]
  erw [Category.comp_id]
  erw [Category.id_comp]

end DerivedCategory
