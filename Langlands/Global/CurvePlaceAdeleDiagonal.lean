import Langlands.Global.CurvePlaceAdeleCongr
import Langlands.Global.CurvePlaceFinitePolesProof

/-! # The full-field diagonal in actual curve-place adeles -/

noncomputable section
universe u
open IsDedekindDomain
open scoped RestrictedProduct

namespace Langlands.Global

section Local

variable {k F : Type u} [Field k] [Field F] [Algebra k F]

theorem curvePlaceCompletion_mem_integers_iff
    (v : AlgebraicCurve.Place k F) (x : F) :
    algebraMap F (curvePlaceCompletion v) x ∈ curvePlaceCompletionIntegers v ↔
      x ∈ v.toValuationSubring := by
  change Valued.v (algebraMap F (v.heightOneSpectrum.adicCompletion F) x) ≤ 1 ↔ _
  simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.mem_iff_adicValuation_le_one.symm

end Local

variable (k F : Type u) [Field k] [PerfectField k] [Field F]
  [Algebra k F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FunctionField k F]

theorem exists_mem_curvePlaceSIntegers (x : F) :
    ∃ S : Finset (AlgebraicCurve.Place k F), x ∈ curvePlaceSIntegers k F S := by
  classical
  let h := curvePlaceFinitePoles k F x
  refine ⟨h.toFinset, ?_⟩
  intro v hv
  by_contra hx
  exact hv (h.mem_toFinset.mpr hx)

/-- The canonical diagonal maps each field element to all its actual completions. -/
def curvePlaceAdeleDiagonal : F →+* CurvePlaceAdeleRing k F where
  toFun x := ⟨fun v => algebraMap F (curvePlaceCompletion v) x, by
    apply Filter.eventually_cofinite.mpr
    exact (curvePlaceFinitePoles k F x).subset (fun v hv hx =>
      hv (curvePlaceCompletion_integral k F v x hx))⟩
  map_one' := by
    apply RestrictedProduct.ext
    intro v
    exact map_one (algebraMap F (curvePlaceCompletion v))
  map_mul' x y := by
    apply RestrictedProduct.ext
    intro v
    exact map_mul (algebraMap F (curvePlaceCompletion v)) x y
  map_zero' := by
    apply RestrictedProduct.ext
    intro v
    exact map_zero (algebraMap F (curvePlaceCompletion v))
  map_add' x y := by
    apply RestrictedProduct.ext
    intro v
    exact map_add (algebraMap F (curvePlaceCompletion v)) x y

@[simp]
theorem curvePlaceAdeleDiagonal_apply (x : F) (v : AlgebraicCurve.Place k F) :
    curvePlaceAdeleDiagonal k F x v = algebraMap F (curvePlaceCompletion v) x := rfl

instance : Algebra F (CurvePlaceAdeleRing k F) :=
  (curvePlaceAdeleDiagonal k F).toAlgebra

instance : Algebra k (CurvePlaceAdeleRing k F) :=
  ((curvePlaceAdeleDiagonal k F).comp (algebraMap k F)).toAlgebra

instance : IsScalarTower k F (CurvePlaceAdeleRing k F) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

@[simp]
theorem curvePlaceAdeleDiagonal_mem_level_iff
    (S : Finset (AlgebraicCurve.Place k F)) (x : F) :
    curvePlaceAdeleDiagonal k F x ∈ curvePlaceAdeleLevel k F S ↔
      x ∈ curvePlaceSIntegers k F S := by
  change (∀ v, v ∉ S →
    algebraMap F (curvePlaceCompletion v) x ∈ curvePlaceCompletionIntegers v) ↔ _
  simp only [curvePlaceCompletion_mem_integers_iff]
  rfl

theorem curvePlaceAdeleLevelDiagonal_eq
    (S : Finset (AlgebraicCurve.Place k F)) (x : curvePlaceSIntegers k F S) :
    (curvePlaceAdeleLevelDiagonal k F S x : CurvePlaceAdeleRing k F) =
      curvePlaceAdeleDiagonal k F x.val := by
  apply RestrictedProduct.ext
  intro v
  rfl

section Presentation

variable {F' : Type u} [Field F'] [Algebra k F']
  [Algebra (RatFunc k) F'] [IsScalarTower k (RatFunc k) F']
  [FunctionField k F']

theorem curvePlaceAdeleCongr_diagonal (e : F ≃ₐ[k] F') (x : F) :
    curvePlaceAdeleCongr e (curvePlaceAdeleDiagonal k F x) =
      curvePlaceAdeleDiagonal k F' (e x) := by
  apply RestrictedProduct.ext
  intro w
  obtain ⟨v, rfl⟩ := (curvePlaceEquiv e).surjective w
  rw [curvePlaceAdeleCongr_apply, curvePlaceAdeleDiagonal_apply,
    curvePlaceAdeleDiagonal_apply]
  exact curvePlaceCompletionCongr_algebraMap e v x

/-- The adelic presentation comparison respects the diagonal constant-field action. -/
def curvePlaceAdeleAlgEquiv (e : F ≃ₐ[k] F') :
    CurvePlaceAdeleRing k F ≃ₐ[k] CurvePlaceAdeleRing k F' where
  __ := curvePlaceAdeleCongr e
  commutes' a := by
    change curvePlaceAdeleCongr e
      (curvePlaceAdeleDiagonal k F (algebraMap k F a)) =
        curvePlaceAdeleDiagonal k F' (algebraMap k F' a)
    rw [curvePlaceAdeleCongr_diagonal, e.commutes]

end Presentation
end Langlands.Global
