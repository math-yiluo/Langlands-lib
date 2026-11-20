import Langlands.Global.AdelicFunctoriality.Extension
import Langlands.Global.Arithmetic.CMSubfield
import Mathlib.FieldTheory.SplittingField.Construction

/-! # Finite algebraic closures of archimedean completions -/

noncomputable section

universe u

open NumberField Polynomial
open scoped NumberField.LiesOver
open Langlands.Global.AdelicFunctoriality
open scoped Langlands.Global.AdelicFunctoriality.InfiniteExtension

namespace Langlands.Global

/-- The actual algebraic closure of each infinite completion is finite over the completion. -/
def FiniteArchimedeanAlgebraicClosureStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (v : InfinitePlace F),
    FiniteDimensional v.Completion (AlgebraicClosure v.Completion)

/-- Pass to a complex place of a finite number field containing a square root of `-1`. -/
theorem finiteArchimedeanAlgebraicClosure : FiniteArchimedeanAlgebraicClosureStatement.{u} := by
  intro F _ _ v
  let p : F[X] := X ^ 2 - C (-1)
  let E := p.SplittingField
  let : NumberField E := NumberField.of_module_finite F E
  have hdeg : (p.map (algebraMap F E)).degree ≠ 0 := by
    apply degree_ne_of_natDegree_ne
    rw [natDegree_map, show p.natDegree = 2 from natDegree_X_pow_sub_C]
    decide
  obtain ⟨r, hr⟩ := (SplittingField.splits p).exists_eval_eq_zero hdeg
  have hr' : r ^ 2 = algebraMap ℚ E (-1) := by
    rw [eval_map] at hr
    simpa only [p, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, eval₂_neg, eval₂_one,
      sub_eq_zero, map_neg, map_one] using hr
  let : IsTotallyComplex E := CMRealization.isTotallyComplex_of_sq_neg (by norm_num) hr'
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := F) (K := E) v
  let : w.LiesOver v := ⟨congrArg Subtype.val hw⟩
  let : FiniteDimensional v.Completion w.Completion := InfiniteExtension.local_finite v w
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
  let : IsAlgClosed w.Completion := ⟨fun f => Polynomial.Splits.of_splits_map
    e.toRingHom (IsAlgClosed.splits _) (fun x _ => e.surjective x)⟩
  let i : AlgebraicClosure v.Completion →ₐ[v.Completion] w.Completion := IsAlgClosed.lift
  exact Module.Finite.of_injective i.toLinearMap i.injective

end Langlands.Global
