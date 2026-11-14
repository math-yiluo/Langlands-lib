import Langlands.Geometry.Building.Kottwitz.NormalizedValuationStatement
import Langlands.ClassFieldTheory.Local.SeparableInertiaNormProof
import Langlands.Global.AdelicFunctoriality.UnramifiedUnitNorm
import Mathlib.RingTheory.Valuation.Discrete.RankOne

/-! # Integer normalization on finite extensions of the unramified closure -/

noncomputable section

universe u

namespace Langlands.Geometry.Building.Kottwitz

open Langlands.LocalGalois.Separable
open Langlands.ClassFieldTheory.Local.SeparableInertiaNorm
open scoped NNReal

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
  [FiniteDimensional (UnramifiedClosure F) L]

private local instance : Module.Free (UnramifiedClosure F) L :=
  Module.Free.of_divisionRing _ _

/-- The norm preserves the spectral valuation ordering on a finite intermediate field. -/
private theorem norm_integer_le_iff (x y : L) :
    MaximalUnramified.valuation F (Algebra.norm (UnramifiedClosure F) x) ≤
      MaximalUnramified.valuation F (Algebra.norm (UnramifiedClosure F) y) ↔
        intermediateValuation F L x ≤ intermediateValuation F L y := by
  rw [MaximalUnramified.valuation_isEquiv F]
  have hnorm (z : L) :
      fixedFieldValuation F (Algebra.norm (UnramifiedClosure F) z) =
        intermediateValuation F L z ^ Module.finrank (UnramifiedClosure F) L :=
    val_norm_eq (ambientHyp_sepClosureValuation F).inv z
  rw [hnorm, hnorm]
  exact pow_le_pow_iff_left₀ (by positivity) (by positivity) Module.finrank_pos.ne'

/-- The base integer valuation composed with the norm, before normalizing its image. -/
private def normIntegerValuation : Valuation L (WithZero (Multiplicative ℤ)) where
  toFun x := MaximalUnramified.valuation F (Algebra.norm (UnramifiedClosure F) x)
  map_zero' := by simp
  map_one' := by simp
  map_mul' x y := by simp
  map_add_le_max' x y := by
    rcases le_max_iff.mp ((intermediateValuation F L).map_add x y) with h | h
    · exact le_max_of_le_left ((norm_integer_le_iff F L _ _).mpr h)
    · exact le_max_of_le_right ((norm_integer_le_iff F L _ _).mpr h)

private theorem normIntegerValuation_isEquiv :
    (normIntegerValuation F L).IsEquiv (intermediateValuation F L) :=
  norm_integer_le_iff F L

private theorem normIntegerValuation_nontrivial :
    (normIntegerValuation F L).IsNontrivial := by
  obtain ⟨a, ha⟩ := MaximalUnramified.valuation_surjective F (WithZero.exp (1 : ℤ))
  refine ⟨algebraMap (UnramifiedClosure F) L a, ?_, ?_⟩
  · change MaximalUnramified.valuation F
      (Algebra.norm (UnramifiedClosure F) (algebraMap (UnramifiedClosure F) L a)) ≠ 0
    rw [Algebra.norm_algebraMap, map_pow, ha]
    simp
  · change MaximalUnramified.valuation F
      (Algebra.norm (UnramifiedClosure F) (algebraMap (UnramifiedClosure F) L a)) ≠ 1
    rw [Algebra.norm_algebraMap, map_pow, ha]
    exact ne_of_gt (one_lt_pow₀ (by simp) Module.finrank_pos.ne')

/-- The required unique normalization, in the full scope of the published statement. -/
theorem normalizedIntermediateValuation_existsUnique :
    NormalizedIntermediateValuationStatement.{u} := by
  intro F _ _ _ _ L _
  let w := normIntegerValuation F L
  have : w.IsNontrivial := normIntegerValuation_nontrivial F L
  have : w.IsRankOneDiscrete := inferInstance
  let e := Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt w
  let v := w.restrict.map e.toMonoidWithZeroHom e.strictMono.monotone
  have hv : v.IsEquiv (intermediateValuation F L) :=
    (Valuation.isEquiv_map_self_of_strictMono _ e.strictMono).trans
      (w.isEquiv_restrict.symm.trans (normIntegerValuation_isEquiv F L))
  have hs : Function.Surjective v :=
    e.surjective.comp (MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective _)
  refine ⟨v, ⟨hv, hs⟩, ?_⟩
  intro v' hv'
  exact Langlands.Global.AdelicFunctoriality.valuation_eq_of_isEquiv_of_surjective
    (hv'.1.trans hv.symm) hv'.2 hs

end Langlands.Geometry.Building.Kottwitz
