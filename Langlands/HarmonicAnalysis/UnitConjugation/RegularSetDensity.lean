import Langlands.HarmonicAnalysis.UnitConjugation.RegularSet
import Mathlib.Topology.Algebra.Module.PerfectSpace

/-! # Density of the regular set over a nontrivially normed field -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Polynomial Set
open scoped _root_.Topology

universe u v

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The regular set of a finite-dimensional associative algebra is dense over a nontrivially
normed field when addition and scalar multiplication are continuous. -/
def RegularSetDensityStatement : Prop :=
  ∀ (F : Type u) [NontriviallyNormedField F] (A : Type v) [Ring A] [Algebra F A]
    [FiniteDimensional F A] [TopologicalSpace A] [ContinuousAdd A] [ContinuousSMul F A],
    Dense (regularSet F A)

theorem dense_regularSet : RegularSetDensityStatement.{u, v} := by
  intro F _ A _ _ _ _ _ _
  classical
  obtain ⟨y, hy⟩ := regularSet_nonempty F (A := A)
  rw [dense_iff_inter_open]
  intro U hU ⟨x, hx⟩
  let l (t : F) : A := x + t • (y - x)
  let b := Module.finBasis F A
  let q := (LinearMap.polyCharpoly (LieAlgebra.ad F A).toLinearMap b).coeff (LieAlgebra.rank F A)
  let c (i : Fin (Module.finrank F A)) : F[X] :=
    C (b.repr x i) + X * C (b.repr (y - x) i)
  let p : F[X] := MvPolynomial.eval₂ C c q
  have hp_eval (t : F) : p.eval t = MvPolynomial.eval (b.repr (l t)) q := by
    change Polynomial.evalRingHom t (MvPolynomial.eval₂ C c q) = _
    rw [MvPolynomial.eval₂_comp_left]
    have hC : (Polynomial.evalRingHom t).comp C = RingHom.id F := by
      ext a
      exact Polynomial.eval_C
    rw [hC]
    change MvPolynomial.eval (Polynomial.evalRingHom t ∘ c) q = _
    have hline : Polynomial.evalRingHom t ∘ c = ⇑(b.repr (l t)) := by
      funext i
      simp [c, l, Polynomial.coe_evalRingHom, smul_eq_mul]
    rw [hline]
  have hreg (t : F) : l t ∈ regularSet F A ↔ p.eval t ≠ 0 := by
    rw [hp_eval, mem_regularSet_iff_isRegular]
    exact LieAlgebra.isRegular_iff_coeff_polyCharpoly_rank_ne_zero F b (l t)
  have h1 : p.eval 1 ≠ 0 := (hreg 1).1 (by simpa [l] using hy)
  have hp : p ≠ 0 := fun h => h1 (by rw [h, eval_zero])
  have hc : Continuous l := continuous_const.add (continuous_id.smul continuous_const)
  have hn : l ⁻¹' U ∈ 𝓝 (0 : F) :=
    hc.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simpa [l] using hx))
  by_contra h
  have hroots : l ⁻¹' U ⊆ {t | p.IsRoot t} := by
    intro t ht
    by_contra hnt
    exact h ⟨l t, ht, (hreg t).2 hnt⟩
  exact (infinite_of_mem_nhds 0 hn) ((Polynomial.finite_setOfPred_isRoot hp).subset hroots)

end Langlands.HarmonicAnalysis.UnitConjugation
