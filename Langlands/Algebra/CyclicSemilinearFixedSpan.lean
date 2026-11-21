import Mathlib.Algebra.Group.Hom.End
import Mathlib.Algebra.Ring.Aut
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Ring

/-! Fixed vectors span for cyclic semilinear operators with separating scalars. -/

open scoped BigOperators

namespace Langlands

universe u v

variable {M : Type v} [AddCommGroup M]

/-- The additive endomorphism summing the first `l` powers of `D`. -/
def cyclicSemilinearSum (D : AddMonoid.End M) (l : ℕ) : AddMonoid.End M :=
  ∑ i : Fin l, D ^ (i : ℕ)

theorem cyclicSemilinearSum_apply (D : AddMonoid.End M) (l : ℕ) (x : M) :
    cyclicSemilinearSum D l x = ∑ i : Fin l, (D ^ (i : ℕ)) x := by
  exact map_sum (AddMonoidHom.eval x) (fun i : Fin l =>
    (show AddMonoid.End M from D ^ (i : ℕ))) Finset.univ

theorem cyclicSemilinearSum_fixed (D : AddMonoid.End M) {l : ℕ} (hD : D ^ l = 1) (x : M) :
    D (cyclicSemilinearSum D l x) = cyclicSemilinearSum D l x := by
  cases l with
  | zero => simp [cyclicSemilinearSum]
  | succ l =>
    calc
      D (cyclicSemilinearSum D (l + 1) x) = ∑ i : Fin (l + 1), (D ^ ((i : ℕ) + 1)) x := by
        simp only [cyclicSemilinearSum_apply, map_sum, pow_succ']
        rfl
      _ = (∑ i : Fin l, (D ^ ((i : ℕ) + 1)) x) + x := by
        rw [Fin.sum_univ_castSucc]
        simp [hD]
      _ = cyclicSemilinearSum D (l + 1) x := by
        rw [cyclicSemilinearSum_apply, Fin.sum_univ_succ]
        simp [add_comm]

variable {S : Type u} [CommRing S] [Module S M]

/-- For `0 < l`, a `σ`-semilinear operator with `D ^ l = 1` has a spanning set of
fixed vectors if the conjugates of one scalar indexed by `Fin l` have pairwise
unit differences. -/
theorem span_cyclicSemilinear_fixed_eq_top (σ : RingAut S) (D : AddMonoid.End M) {l : ℕ}
    (hl : 0 < l) (hD : D ^ l = 1) (hσ : ∀ (r : S) (x : M), D (r • x) = σ r • D x)
    (a : S) (ha : Pairwise fun i j : Fin l => IsUnit ((σ ^ (i : ℕ)) a - (σ ^ (j : ℕ)) a)) :
    Submodule.span S {x : M | D x = x} = ⊤ := by
  classical
  let P := Submodule.span S {x : M | D x = x}
  let c (i : Fin l) := (σ ^ (i : ℕ)) a
  have hpow (n : ℕ) (r : S) (x : M) : (D ^ n) (r • x) = (σ ^ n) r • (D ^ n) x := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ' D, pow_succ' σ]
      change D ((D ^ n) (r • x)) = σ ((σ ^ n) r) • D ((D ^ n) x)
      rw [ih, hσ]
  have hweighted (s : Finset (Fin l)) (x : M) :
      (∑ i : Fin l, (∏ j ∈ s, (c i - c j)) • (D ^ (i : ℕ)) x) ∈ P := by
    induction s using Finset.induction_on generalizing x with
    | empty =>
      have hfixed : cyclicSemilinearSum D l x ∈ {y : M | D y = y} :=
        cyclicSemilinearSum_fixed D hD x
      simp only [Finset.prod_empty, one_smul, ← cyclicSemilinearSum_apply]
      change cyclicSemilinearSum D l x ∈ (P : Set M)
      exact Submodule.subset_span (R := S) hfixed
    | @insert j s hj ih =>
      have hdiff := P.sub_mem (ih (a • x)) (P.smul_mem (c j) (ih x))
      convert hdiff using 1
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.prod_insert hj, hpow, smul_smul, smul_smul, ← sub_smul]
      change ((c i - c j) * (∏ k ∈ s, (c i - c k))) • _ =
        (((∏ k ∈ s, (c i - c k)) * c i) - c j * (∏ k ∈ s, (c i - c k))) • _
      congr 1
      ring
  let i₀ : Fin l := ⟨0, hl⟩
  let s := Finset.univ.erase i₀
  let d := ∏ j ∈ s, (c i₀ - c j)
  have hd : IsUnit d := by
    change IsUnit (∏ j ∈ s, (c i₀ - c j))
    exact IsUnit.prod_iff.mpr fun _ hj => ha ((Finset.mem_erase.mp hj).1.symm)
  apply top_unique
  intro x _
  have heq : (∑ i : Fin l, (∏ j ∈ s, (c i - c j)) • (D ^ (i : ℕ)) x) = d • x := by
    rw [Finset.sum_eq_single i₀]
    · rfl
    · intro i _ hi
      have hprod : (∏ j ∈ s, (c i - c j)) = 0 :=
        Finset.prod_eq_zero (f := fun j => c i - c j)
          (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩) (sub_self _)
      rw [hprod, zero_smul]
    · simp
  have hx : d • x ∈ P := heq ▸ hweighted s x
  obtain ⟨e, he⟩ := hd
  rw [← he] at hx
  simpa only [smul_smul, Units.inv_mul, one_smul] using P.smul_mem (↑e⁻¹ : S) hx

end Langlands
