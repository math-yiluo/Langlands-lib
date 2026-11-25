/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TraceShiftUnit
public import WeilConjectures.CategoryTheory.Monoidal.Rigid.TraceShiftDecomposition
public import WeilConjectures.Mathlib.CategoryTheory.Conj
public import WeilConjectures.TraceFormula.CategoricalTrace

/-!
# The trace on a finite sum of shifted units is the supertrace on homology

Let `A` be a braided monoidal closed Grothendieck abelian category with functorial flat
resolutions, and `Y` an object of `D(A)` which is a finite direct sum `⨁ⱼ 𝟙⟦nⱼ⟧` of shifts of
the unit (`CategoryTheory.ShiftDecomposition`). For an endomorphism `w` of `Y`, the categorical
trace of `w` in `D(A)`, for the Koszul braiding `DerivedCategory.braidedCategory'`, is the
supertrace `∑ᵢ (-1)ⁱ Tr(Hⁱ(w) | Hⁱ(Y))` of the endomorphisms induced on the homology objects,
placed in degree `0` (`DerivedCategory.trace_eq_singleFunctor_map_superTrace`; blueprint
`proposition-properties-trace`, item (4)).

The scalar `Tr(Hⁱ(w))` in `End (𝟙_ A)` is placed in degree `0` by
`DerivedCategory.singleFunctorUnitEndRingHom`.

Both sides are sums over the summands `𝟙⟦nⱼ⟧`: the trace by cyclicity
(`CategoryTheory.ShiftDecomposition.trace_eq_sum`), the trace of each `Hⁱ(w)` likewise
(`CategoryTheory.traceOrZero_eq_sum`), `Hⁱ` being additive. On a summand `𝟙⟦n⟧` an
endomorphism is `r[0]⟦n⟧` for an endomorphism `r` of the unit of `A`; its trace is `(-1)ⁿ r[0]`
(`DerivedCategory.trace_shiftFunctor_map_singleFunctor_map`), and its homology is `r` in degree
`-n` and zero elsewhere, with supertrace `(-1)ⁿ r`
(`DerivedCategory.superTrace_homologyFunctor_map_shiftFunctor_map_singleFunctor_map`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  [BraidedCategory C]

/-- The categorical trace of an endomorphism `v` of a finite direct sum `M = ⨁ⱼ Eⱼ` of
dualizable objects is the sum of the traces of its diagonal blocks `Eⱼ ⟶ M ⟶ M ⟶ Eⱼ`. Only the
relation `∑ⱼ pⱼ ≫ iⱼ = 𝟙` is needed, by cyclicity of the trace. -/
theorem traceOrZero_eq_sum {ι : Type*} [Fintype ι] {M : C} {E : ι → C}
    (hM : IsDualizable M) (hE : ∀ j, IsDualizable (E j)) (incl : ∀ j, E j ⟶ M)
    (proj : ∀ j, M ⟶ E j) (h : ∑ j, proj j ≫ incl j = 𝟙 M) (v : M ⟶ M) :
    traceOrZero v = ∑ j, traceOrZero (incl j ≫ v ≫ proj j) := by
  obtain ⟨_⟩ := hM
  have (j : ι) : HasRightDual (E j) := (hE j).some
  rw [traceOrZero_eq_trace]
  simp_rw [traceOrZero_eq_trace]
  apply End.ext
  simp only [End.sum_asHom]
  calc trace v = trace ((∑ j, proj j ≫ incl j) ≫ v) := by rw [h, Category.id_comp]
    _ = ∑ j, trace (proj j ≫ incl j ≫ v) := by
        rw [Preadditive.sum_comp, ← traceAddMonoidHom_apply, map_sum]
        simp only [traceAddMonoidHom_apply, Category.assoc]
    _ = ∑ j, trace (incl j ≫ v ≫ proj j) := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [trace_comp_comm, Category.assoc]

end CategoryTheory

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A]

local instance instHasColimitsOfSize_traceSupertrace
    : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A

variable (A) in
/-- The endomorphisms of the unit of `A`, placed in degree `0`, as endomorphisms of the unit of
`D(A)`. -/
noncomputable def singleFunctorUnitEndRingHom : End (𝟙_ A) →+* End (𝟙_ (DerivedCategory A)) :=
  cast (by rfl) ((singleFunctor A 0).mapEndRingHom (𝟙_ A))

variable (A) in
/-- The homology in degree `-n` of the shift by `n` of an object placed in degree `0`. -/
noncomputable def homologyFunctorShiftSingleFunctorIso (n : ℤ) :
    singleFunctor A 0 ⋙ shiftFunctor (DerivedCategory A) n ⋙ homologyFunctor A (-n) ≅ 𝟭 A :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((singleFunctors A).shiftIso n (-n) 0 (by lia)) _ ≪≫
    singleFunctorCompHomologyFunctorIso A (-n)

omit [IsGrothendieckAbelian A] [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A]
  [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A] in
/-- The homology of the shift by `n` of an object placed in degree `0` vanishes outside degree
`-n`. -/
lemma isZero_homologyFunctor_obj_shiftFunctor_obj_singleFunctor_obj (n : ℤ) (X : A) {i : ℤ}
    (hi : i ≠ -n) :
    IsZero ((homologyFunctor A i).obj
      ((shiftFunctor (DerivedCategory A) n).obj ((singleFunctor A 0).obj X))) :=
  isZero_homologyFunctor_obj_of_iso_singleFunctor
    (((singleFunctors A).shiftIso n (-n) 0 (by lia)).app X) hi

/-- The homology objects of a shifted unit of `D(A)` are dualizable. -/
lemma isDualizable_homologyFunctor_obj_shiftFunctor_obj_tensorUnit (n i : ℤ) :
    IsDualizable ((homologyFunctor A i).obj
      ((shiftFunctor (DerivedCategory A) n).obj (𝟙_ (DerivedCategory A)))) := by
  by_cases hi : i = -n
  · subst hi
    exact IsDualizable.of_iso ((homologyFunctorShiftSingleFunctorIso A n).app (𝟙_ A)).symm
      isDualizable_unit
  · exact ⟨hasRightDualOfIsZero
      (isZero_homologyFunctor_obj_shiftFunctor_obj_singleFunctor_obj n _ hi)⟩

omit [IsGrothendieckAbelian A] [MonoidalPreadditive A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
/-- The supertrace on homology of the shift by `n` of an endomorphism `r[0]` of the unit placed
in degree `0` is `(-1)ⁿ r`: the homology is `r` in degree `-n` and zero elsewhere. -/
lemma superTrace_homologyFunctor_map_shiftFunctor_map_singleFunctor_map (n : ℤ)
    (r : 𝟙_ A ⟶ 𝟙_ A) :
    superTrace
      (fun i ↦ (homologyFunctor A i).obj
        ((shiftFunctor (DerivedCategory A) n).obj ((singleFunctor A 0).obj (𝟙_ A))))
      (fun i ↦ (homologyFunctor A i).map
        ((shiftFunctor (DerivedCategory A) n).map ((singleFunctor A 0).map r))) =
      (n.negOnePow : ℤ) • End.of r := by
  unfold superTrace
  rw [finsum_eq_single _ (-n) fun i hi ↦ by
    rw [traceOrZero_eq_zero_of_isZero
      (isZero_homologyFunctor_obj_shiftFunctor_obj_singleFunctor_obj n _ hi), smul_zero],
    Int.negOnePow_neg]
  congr 1
  dsimp only
  let e := (homologyFunctorShiftSingleFunctorIso A n).app (𝟙_ A)
  have he : r = e.inv ≫ (homologyFunctor A (-n)).map
      ((shiftFunctor (DerivedCategory A) n).map ((singleFunctor A 0).map r)) ≫ e.hom := by
    have := (homologyFunctorShiftSingleFunctorIso A n).hom.naturality r
    simp only [Functor.comp_map, Functor.id_map] at this
    simp only [e, Iso.app_hom, Iso.app_inv]
    rw [this, Iso.inv_hom_id_app_assoc]
  calc _ = traceOrZero (e.inv ≫ (homologyFunctor A (-n)).map
          ((shiftFunctor (DerivedCategory A) n).map ((singleFunctor A 0).map r)) ≫ e.hom) :=
        (traceOrZero_conj e _).symm
    _ = traceOrZero r := by rw [← he]
    _ = .of (r) := by
        let : HasRightDual (𝟙_ A) := ⟨𝟙_ A⟩
        rw [traceOrZero_eq_trace, trace_tensorUnit]

/-- The trace of an endomorphism of a shifted unit `𝟙⟦n⟧` of `D(A)` is the supertrace of the
induced endomorphisms of its homology objects, placed in degree `0`. -/
lemma trace_eq_singleFunctor_map_superTrace_of_shift (n : ℤ)
    [HasRightDual ((shiftFunctor (DerivedCategory A) n).obj (𝟙_ (DerivedCategory A)))]
    (b : (shiftFunctor (DerivedCategory A) n).obj (𝟙_ (DerivedCategory A)) ⟶
      (shiftFunctor (DerivedCategory A) n).obj (𝟙_ (DerivedCategory A))) :
    letI := braidedCategory' A
    trace b = (singleFunctorUnitEndRingHom A
      (superTrace
        (fun i ↦ (homologyFunctor A i).obj
          ((shiftFunctor (DerivedCategory A) n).obj (𝟙_ (DerivedCategory A))))
        (fun i ↦ (homologyFunctor A i).map b))).asHom := by
  obtain ⟨r, rfl⟩ : ∃ r, (shiftFunctor (DerivedCategory A) n).map ((singleFunctor A 0).map r) = b :=
    ⟨(singleFunctor A 0).preimage ((shiftFunctor (DerivedCategory A) n).preimage b), by
      erw [Functor.map_preimage, Functor.map_preimage]⟩
  refine (@trace_shiftFunctor_map_singleFunctor_map _ _ _ _ _ _ _ _ _ _ n r ‹_›).trans ?_
  erw [superTrace_homologyFunctor_map_shiftFunctor_map_singleFunctor_map, map_zsmul,
    End.zsmul_asHom, Category.id_comp, Category.comp_id]
  rfl

/-- **The trace as a supertrace** (blueprint `proposition-properties-trace`, item (4)): for an
object `Y` of `D(A)` which is a finite direct sum of shifts of the unit, with dualizable
homology objects, the categorical trace of an endomorphism `w` of `Y`, for the Koszul braiding, is
the alternating sum `∑ᵢ (-1)ⁱ Tr(Hⁱ(w) | Hⁱ(Y))` of the traces on the homology objects, placed in
degree `0`. -/
theorem trace_eq_singleFunctor_map_superTrace {Y : DerivedCategory A} [HasRightDual Y]
    (D : ShiftDecomposition (𝟙_ (DerivedCategory A)) Y)
    (hY : ∀ i, IsDualizable ((homologyFunctor A i).obj Y)) (w : Y ⟶ Y) :
    letI := braidedCategory' A
    trace w = (singleFunctorUnitEndRingHom A
      (superTrace (fun i ↦ (homologyFunctor A i).obj Y)
        (fun i ↦ (homologyFunctor A i).map w))).asHom := by
  let := braidedCategory' A
  let (n : ℤ) : HasRightDual ((shiftFunctor (DerivedCategory A) n).obj (𝟙_ _)) :=
    (isDualizable_shift isDualizable_unit n).some
  rw [D.trace_eq_sum w]
  rw [Finset.sum_congr rfl fun j _ ↦ trace_eq_singleFunctor_map_superTrace_of_shift (A := A)
    (D.deg j) (D.incl j ≫ w ≫ D.proj j)]
  rw [← End.sum_asHom]
  apply congrArg End.asHom
  refine (map_sum (singleFunctorUnitEndRingHom A) _ _).symm.trans (congrArg _ ?_)
  unfold superTrace
  have hi (i : ℤ) : traceOrZero ((homologyFunctor A i).map w) =
      ∑ j, traceOrZero ((homologyFunctor A i).map (D.incl j ≫ w ≫ D.proj j)) := by
    have h := traceOrZero_eq_sum (hY i)
      (fun j ↦ isDualizable_homologyFunctor_obj_shiftFunctor_obj_tensorUnit (D.deg j) i)
      (fun j ↦ (homologyFunctor A i).map (D.incl j)) (fun j ↦ (homologyFunctor A i).map (D.proj j))
      (by
        calc ∑ j, (homologyFunctor A i).map (D.proj j) ≫ (homologyFunctor A i).map (D.incl j)
            = ∑ j, (homologyFunctor A i).map (D.proj j ≫ D.incl j) :=
              Finset.sum_congr rfl fun j _ ↦ ((homologyFunctor A i).map_comp _ _).symm
          _ = (homologyFunctor A i).map (∑ j, D.proj j ≫ D.incl j) := (Functor.map_sum _ _ _).symm
          _ = 𝟙 _ := by rw [D.total, CategoryTheory.Functor.map_id])
      ((homologyFunctor A i).map w)
    refine h.trans (Finset.sum_congr rfl fun j _ ↦ ?_)
    rw [Functor.map_comp, Functor.map_comp]
  simp_rw [hi, Finset.smul_sum]
  refine (finsum_sum_comm _ _ fun j _ ↦ Set.Finite.subset (Set.finite_singleton (-D.deg j)) ?_).symm
  intro i hi
  by_contra h
  exact hi (smul_eq_zero_of_right _ (traceOrZero_eq_zero_of_isZero
    (isZero_homologyFunctor_obj_shiftFunctor_obj_singleFunctor_obj (D.deg j) _
      (by simpa using h)) _))

end DerivedCategory
