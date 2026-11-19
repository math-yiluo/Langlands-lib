import Langlands.Representation.Archimedean.RealAdjacentFourierBand
import Langlands.Representation.Archimedean.RealAdjacentWeightStringLifting
import Mathlib.LinearAlgebra.Lagrange

/-! # One-sided lifting for two adjacent rotations -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.RealAdjacentRotationLifting

open Complex Polynomial RealOrthogonalUncertainty RealTailMultiplierPolynomial

variable {W V : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]

private theorem map_aeval (L : W →ₗ[ℂ] V) {a : Module.End ℂ W} {b : Module.End ℂ V}
    (h : ∀ v, L (a v) = b (L v)) (Q : ℂ[X]) (v : W) :
    L (aeval a Q v) = aeval b Q (L v) := by
  have hpow (k : ℕ) : L ((a ^ k) v) = (b ^ k) (L v) := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ' a, pow_succ' b, Module.End.mul_apply, Module.End.mul_apply, h, ih]
  rw [aeval_eq_sum_range, aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  simp only [LinearMap.smul_apply, map_smul, hpow]

/-- An intertwiner of two rotation generators also intertwines the polynomial
calculus of their normalized generators. -/
theorem map_aeval_rotation (L : W →ₗ[ℂ] V) {a : Module.End ℂ W} {b : Module.End ℂ V}
    (h : ∀ v, L (a v) = b (L v)) (Q : ℂ[X]) (v : W) :
    L (aeval (-I • a) Q v) = aeval (-I • b) Q (L v) :=
  map_aeval L (fun x => by simp only [LinearMap.smul_apply, map_smul, h]) Q v

private theorem eq_of_modes_eq {a : Module.End ℂ W} {π : ℤ → Module.End ℂ W} {S : Finset ℤ}
    (hM : IsModeDecomposition a π S) {v w : W} (h : ∀ j ∈ S, π j v = π j w) : v = w := by
  rw [← hM.sum_apply v, ← hM.sum_apply w]
  exact Finset.sum_congr rfl h

private theorem proj_mem_of_mem_invariant
    {a : Module.End ℂ W} {π : ℤ → Module.End ℂ W} {S : Finset ℤ}
    (hM : IsModeDecomposition a π S) {U : Submodule ℂ W}
    (hU : U ≤ U.comap a) (j : ℤ) {v : W} (hv : v ∈ U) : π j v ∈ U := by
  classical
  by_cases hj : j ∈ S
  · let Q : ℂ[X] := Lagrange.basis S (fun i : ℤ => (i : ℂ)) j
    have hP : π j v = aeval (-I • a) Q v := by
      apply eq_of_modes_eq hM
      intro i hi
      rw [hM.proj_apply_proj, RealPolynomialFourierPropagation.proj_aeval hM]
      by_cases hij : i = j
      · subst i
        simp only [↓reduceIte]
        rw [Lagrange.eval_basis_self _ hj, one_smul]
        intro j₁ _ j₂ _ h
        exact_mod_cast h
      · have hval : Q.eval (i : ℂ) = 0 := Lagrange.eval_basis_of_ne (Ne.symm hij) hi
        simp only [hij, ↓reduceIte, hval, zero_smul]
    let aU := a.restrict (p := U) (q := U) fun _ hx => hU hx
    rw [hP]
    change aeval (-I • a) Q (U.subtype ⟨v, hv⟩) ∈ U
    rw [← map_aeval_rotation U.subtype (b := a) (a := aU) (fun _ => rfl) Q ⟨v, hv⟩]
    exact (aeval (-I • aU) Q ⟨v, hv⟩).property
  · rw [hM.eq_zero j hj, LinearMap.zero_apply]
    exact U.zero_mem

private theorem top_mode {a : Module.End ℂ W} {π : ℤ → Module.End ℂ W} {S : Finset ℤ}
    (hM : IsModeDecomposition a π S) {v : W} (hv : v ≠ 0) :
    ∃ J ∈ S, (∃ u, π J u ≠ 0) ∧ ∀ i : ℤ, J < i → π i = 0 := by
  classical
  let T := S.filter fun i => ∃ u, π i u ≠ 0
  have hT : T.Nonempty := by
    by_contra h
    apply hv
    rw [← hM.sum_apply v]
    apply Finset.sum_eq_zero
    intro i hi
    by_contra hi'
    exact h ⟨i, Finset.mem_filter.mpr ⟨hi, v, hi'⟩⟩
  let J := T.max' hT
  have hJ := Finset.mem_filter.mp (T.max'_mem hT)
  refine ⟨J, hJ.1, hJ.2, fun i hi => ?_⟩
  by_cases hiS : i ∈ S
  · ext x
    by_contra h
    have : i ∈ T := Finset.mem_filter.mpr ⟨hiS, x, h⟩
    exact hi.not_ge (T.le_max' i this)
  · exact hM.eq_zero i hiS

private def raising (b c : Module.End ℂ W) : Module.End ℂ W := b - I • c

private def lowering (b c : Module.End ℂ W) : Module.End ℂ W := -(b + I • c)

/-- A highest-weight string of top mode `J`. It includes the zero vectors after
the last nonzero weight at index `2 * J`. -/
private structure WeightString (a b c : Module.End ℂ W) where
  top : ℕ
  vec : ℕ → W
  eigen (k : ℕ) : a (vec k) = (I * ((top - (k : ℤ) : ℤ) : ℂ)) • vec k
  nonzero (k : ℕ) : k ≤ 2 * top → vec k ≠ 0
  eq_zero (k : ℕ) : 2 * top < k → vec k = 0
  lower (k : ℕ) : lowering b c (vec k) = vec (k + 1)
  raise_zero : raising b c (vec 0) = 0
  raise (k : ℕ) : raising b c (vec (k + 1)) = ((k + 1 : ℂ) * (2 * top - k)) • vec k

private theorem exists_weightString {a b c : Module.End ℂ W} {π : ℤ → Module.End ℂ W}
    {S : Finset ℤ} (hab : a * b - b * a = c) (hbc : b * c - c * b = a)
    (hca : c * a - a * c = b) (hM : IsModeDecomposition a π S) {v : W} (hv : v ≠ 0) :
    Nonempty (WeightString a b c) := by
  classical
  obtain ⟨J, hJS, ⟨x, hx⟩, htop⟩ := top_mode hM hv
  let nu := π J x
  let E := raising b c
  let F := lowering b c
  let u (k : ℕ) : W := (F ^ k) nu
  have hnext (k : ℕ) : F (u k) = u (k + 1) := by
    dsimp only [u]
    rw [pow_succ', Module.End.mul_apply]
  have hF : a * F - F * a = (I * ((-1 : ℤ) : ℂ)) • F := by
    dsimp only [F, lowering]
    calc
      _ = -(a * (b + I • c) - (b + I • c) * a) := by
        simp only [mul_neg, neg_mul]
        abel
      _ = _ := by rw [lie_lower hab hca, smul_neg]
  have hproj (k : ℕ) : π (J - k) (u k) = u k := by
    induction k with
    | zero => simp [u, nu, hM.proj_apply_proj]
    | succ k ih =>
      rw [← hnext, hM.proj_apply_of_lie hF, show J - (k + 1 : ℕ) - (-1 : ℤ) = J - k by omega, ih]
  have heig (k : ℕ) : a (u k) = (I * ((J - (k : ℤ) : ℤ) : ℂ)) • u k := by
    conv_lhs => rw [← hproj k]
    rw [hM.apply_proj, hproj]
  have hE0 : E (u 0) = 0 := by
    have hh := hM.proj_apply_of_lie (lie_raise hab hca) (J + 1) (u 0)
    rw [htop _ (by omega), LinearMap.zero_apply, add_sub_cancel_right] at hh
    rw [show π J (u 0) = u 0 by simpa using hproj 0] at hh
    exact hh.symm
  have hEF : E * F - F * E = (-2 * I) • a := by
    dsimp only [E, F, raising, lowering]
    calc
      _ = -((b - I • c) * (b + I • c) - (b + I • c) * (b - I • c)) := by
        simp only [mul_neg, neg_mul]
        abel
      _ = _ := by rw [lie_raise_lower hbc, ← neg_smul, neg_mul]
  have hstep (k : ℕ) : E (F (u k)) = F (E (u k)) + (2 * ((J - (k : ℤ) : ℤ) : ℂ)) • u k := by
    have h := congrArg (fun T : Module.End ℂ W => T (u k)) hEF
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
    rw [heig, smul_smul, show (-2 * I : ℂ) * (I * ((J - (k : ℤ) : ℤ) : ℂ)) =
      2 * ((J - (k : ℤ) : ℤ) : ℂ) by linear_combination (-2 * ((J - (k : ℤ) : ℤ) : ℂ)) * I_sq,
      sub_eq_iff_eq_add] at h
    simpa only [add_comm] using h
  have hrec (k : ℕ) : E (u (k + 1)) = ((k + 1 : ℂ) * (2 * (J : ℂ) - k)) • u k := by
    induction k with
    | zero => rw [← hnext, hstep, hE0, map_zero, zero_add]; simp
    | succ k ih =>
      rw [← hnext, hstep, ih, map_smul, hnext, ← add_smul]
      congr 1
      push_cast
      ring
  have hzero : ∃ k : ℕ, u k = 0 := by
    let m := S.min' ⟨J, hJS⟩
    let k := (J - m + 1).toNat
    have hbelow : J - (k : ℤ) < m := by
      dsimp only [k]
      omega
    have hnot : J - (k : ℤ) ∉ S := fun h => hbelow.not_ge (S.min'_le _ h)
    have hp := hproj k
    rw [hM.eq_zero _ hnot, LinearMap.zero_apply] at hp
    exact ⟨k, hp.symm⟩
  have hu0 : u 0 ≠ 0 := by simpa [u, nu] using hx
  obtain ⟨n, hn, hn'⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists hu0 hzero
  have hnJ : 2 * J = (n : ℤ) := by
    have h := hrec n
    rw [hn', map_zero, eq_comm, smul_eq_zero_iff_left hn, mul_eq_zero] at h
    have h' := sub_eq_zero.mp (h.resolve_left (Nat.cast_add_one_ne_zero n))
    exact_mod_cast h'
  let J₀ := J.toNat
  have hJ₀ : (J₀ : ℤ) = J := by dsimp only [J₀]; omega
  have hn₀ : n = 2 * J₀ := by omega
  have hzero_after {i k : ℕ} (hik : i ≤ k) (hi : u i = 0) : u k = 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hik
    dsimp only [u] at hi ⊢
    rw [add_comm, pow_add, Module.End.mul_apply, hi, map_zero]
  refine ⟨⟨J₀, u, ?_, ?_, ?_, hnext, hE0, ?_⟩⟩
  · intro k
    rw [hJ₀]
    exact heig k
  · intro k hk h
    exact hn (hzero_after (by omega) h)
  · intro k hk
    exact hzero_after (by omega) hn'
  · intro k
    have hc : (J₀ : ℂ) = (J : ℂ) := by exact_mod_cast hJ₀
    rw [hc]
    exact hrec k

private def WeightString.space {a b c : Module.End ℂ W} (t : WeightString a b c) :
    Submodule ℂ W :=
  Submodule.span ℂ (Set.range t.vec)

private theorem WeightString.vec_mem {a b c : Module.End ℂ W} (t : WeightString a b c)
    (k : ℕ) : t.vec k ∈ t.space :=
  Submodule.subset_span (Set.mem_range_self k)

private theorem WeightString.space_ne_bot {a b c : Module.End ℂ W} (t : WeightString a b c) :
    t.space ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨t.vec 0, t.vec_mem 0, t.nonzero 0 (by omega)⟩

private theorem WeightString.a_stable {a b c : Module.End ℂ W} (t : WeightString a b c) :
    t.space ≤ t.space.comap a := by
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  change a (t.vec k) ∈ t.space
  rw [t.eigen]
  exact t.space.smul_mem _ (t.vec_mem k)

private theorem WeightString.b_stable {a b c : Module.End ℂ W} (t : WeightString a b c) :
    t.space ≤ t.space.comap b := by
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  change b (t.vec k) ∈ t.space
  have hab : b = (1 / 2 : ℂ) • (raising b c - lowering b c) := by
    dsimp only [raising, lowering]
    module
  have hk := congrArg (fun B : Module.End ℂ W => B (t.vec k)) hab
  rw [LinearMap.smul_apply, LinearMap.sub_apply, t.lower] at hk
  rw [hk]
  refine t.space.smul_mem _ (t.space.sub_mem ?_ (t.vec_mem _))
  cases k with
  | zero => rw [t.raise_zero]; exact t.space.zero_mem
  | succ k => rw [t.raise]; exact t.space.smul_mem _ (t.vec_mem _)

private theorem WeightString.finrank_space {a b c : Module.End ℂ W} (t : WeightString a b c) :
    Module.finrank ℂ t.space = 2 * t.top + 1 := by
  classical
  let u : Fin (2 * t.top + 1) → W := fun k => t.vec k
  have hspan : Submodule.span ℂ (Set.range u) = t.space := by
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact t.vec_mem i
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      by_cases hi : i ≤ 2 * t.top
      · exact Submodule.subset_span (Set.mem_range_self (⟨i, by omega⟩ : Fin (2 * t.top + 1)))
      · rw [t.eq_zero _ (by omega)]
        exact Submodule.zero_mem _
  rw [← hspan]
  let μ : Fin (2 * t.top + 1) → ℂ := fun k =>
    I * (((t.top : ℤ) - (k : ℕ) : ℤ) : ℂ)
  have hμ : Function.Injective μ := by
    intro i j hij
    apply Fin.ext
    have hi' : I * (((t.top : ℤ) - (i : ℕ) : ℤ) : ℂ) =
        I * (((t.top : ℤ) - (j : ℕ) : ℤ) : ℂ) := hij
    have hcast : ((t.top : ℤ) - (i : ℕ)) = (t.top : ℤ) - (j : ℕ) := by
      exact_mod_cast mul_left_cancel₀ I_ne_zero hi'
    omega
  have hli := a.eigenvectors_linearIndependent' μ hμ u fun k => by
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    exact ⟨t.eigen k, t.nonzero k (by have := k.isLt; omega)⟩
  simpa using finrank_span_eq_card hli

private theorem WeightString.proj_vec {a b c : Module.End ℂ W} (t : WeightString a b c)
    {π : ℤ → Module.End ℂ W} {S : Finset ℤ} (hM : IsModeDecomposition a π S) (j : ℤ) (k : ℕ) :
    π j (t.vec k) = if j = (t.top : ℤ) - k then t.vec k else 0 := by
  split_ifs with h
  · rw [h]
    exact hM.proj_self_of_eigen (t.eigen k)
  · refine hM.proj_eq_zero_of_eigen (t.eigen k) fun hh => h ?_
    exact_mod_cast mul_left_cancel₀ I_ne_zero hh

private theorem WeightString.proj_zero_above {a b c : Module.End ℂ W} (t : WeightString a b c)
    (ht : t.space = ⊤) {π : ℤ → Module.End ℂ W} {S : Finset ℤ}
    (hM : IsModeDecomposition a π S) {j : ℤ} (hj : (t.top : ℤ) < j) : π j = 0 := by
  have h : t.space ≤ LinearMap.ker (π j) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    change π j (t.vec k) = 0
    have hk : j ≠ (t.top : ℤ) - k := by omega
    simp only [t.proj_vec hM, hk, ↓reduceIte]
  ext v
  change π j v = 0
  exact LinearMap.mem_ker.mp (h (ht.symm ▸ Submodule.mem_top))

private theorem WeightString.proj_mem_line {a b c : Module.End ℂ W} (t : WeightString a b c)
    (ht : t.space = ⊤) {π : ℤ → Module.End ℂ W} {S : Finset ℤ}
    (hM : IsModeDecomposition a π S) (j : ℤ) (v : W) :
    π j v ∈ ℂ ∙ t.vec ((t.top : ℤ) - j).toNat := by
  let L := ℂ ∙ t.vec ((t.top : ℤ) - j).toNat
  have h : t.space ≤ L.comap (π j) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    change π j (t.vec k) ∈ L
    rw [t.proj_vec hM]
    split_ifs with hk
    · have heq : ((t.top : ℤ) - j).toNat = k := by omega
      simpa only [L, heq] using Submodule.mem_span_singleton_self (R := ℂ) (t.vec k)
    · exact L.zero_mem
  exact h (ht.symm ▸ Submodule.mem_top)

private theorem WeightString.raise_injective {a b c : Module.End ℂ W} (t : WeightString a b c)
    (ht : t.space = ⊤) {π : ℤ → Module.End ℂ W} {S : Finset ℤ}
    (hM : IsModeDecomposition a π S) (j : ℤ) (hj : j < (t.top : ℤ)) (v : W)
    (h : raising b c (π j v) = 0) : π j v = 0 := by
  let k := ((t.top : ℤ) - j).toNat
  obtain ⟨z, heq⟩ := Submodule.mem_span_singleton.mp (t.proj_mem_line ht hM j v)
  change z • t.vec k = π j v at heq
  by_cases hk : k ≤ 2 * t.top
  · have hpos : 0 < k := by dsimp only [k]; omega
    obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hl' : l < 2 * t.top := by omega
    rw [← heq, hl, map_smul, t.raise] at h
    have hcoef : ((l + 1 : ℂ) * (2 * (t.top : ℂ) - l)) ≠ 0 := by
      refine mul_ne_zero (Nat.cast_add_one_ne_zero l) (sub_ne_zero.mpr fun hEq => ?_)
      have hEq' : 2 * (t.top : ℤ) = (l : ℤ) := by exact_mod_cast hEq
      omega
    rw [← heq, (smul_eq_zero.mp h).resolve_right
      (smul_ne_zero hcoef (t.nonzero l hl'.le)), zero_smul]
  · rw [← heq, t.eq_zero _ (by omega), smul_zero]

private def SimplePair (a b : Module.End ℂ W) : Prop :=
  ∀ U : Submodule ℂ W, U ≤ U.comap a → U ≤ U.comap b → U ≠ ⊥ → U = ⊤

private theorem exists_lift_of_simple [FiniteDimensional ℂ W]
    {a b c : Module.End ℂ W} {π τ : ℤ → Module.End ℂ W} {S T : Finset ℤ}
    (hab : a * b - b * a = c) (hbc : b * c - c * b = a) (hca : c * a - a * c = b)
    (hM : IsModeDecomposition a π S) (hM' : IsModeDecomposition b τ T) (hs : SimplePair a b)
    {N : ℤ} (hN : 0 < N) (H : ℕ) (v : W)
    (hv : ∀ j : ℤ, N + H ≤ j → π j (aeval (-I • b) (tailPolynomial H) v) = 0) :
    ∃ w : W, aeval (-I • b) (tailPolynomial H) w = 0 ∧ ∀ j : ℤ, N ≤ j → π j w = π j v := by
  classical
  by_cases hne : v = 0
  · exact ⟨0, map_zero _, fun _ _ => by rw [hne]⟩
  obtain ⟨s⟩ := exists_weightString hab hbc hca hM hne
  have hs' : s.space = ⊤ := hs _ s.a_stable s.b_stable s.space_ne_bot
  have hba : b * a - a * b = -c := by rw [← hab]; abel
  have hac : a * (-c) - (-c) * a = b := by rw [mul_neg, neg_mul]; rw [← hca]; abel
  have hcb : (-c) * b - b * (-c) = a := by rw [neg_mul, mul_neg]; rw [← hbc]; abel
  obtain ⟨t⟩ := exists_weightString hba hac hcb hM' hne
  have ht : t.space = ⊤ := hs _ t.b_stable t.a_stable t.space_ne_bot
  have hrankS := s.finrank_space
  have hrankT := t.finrank_space
  rw [hs', finrank_top] at hrankS
  rw [ht, finrank_top] at hrankT
  have hJ : s.top = t.top := by omega
  have heig (j : ℤ) (hj : -(s.top : ℤ) ≤ j) (hj' : j ≤ s.top) :
      (-I • b).HasEigenvalue (j : ℂ) := by
    let k := ((t.top : ℤ) - j).toNat
    have hk : k ≤ 2 * t.top := by dsimp only [k]; omega
    have hm : (t.top : ℤ) - (k : ℕ) = j := by dsimp only [k]; omega
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := t.vec k)
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    refine ⟨?_, t.nonzero k hk⟩
    rw [LinearMap.smul_apply, t.eigen, hm, smul_smul]
    congr 1
    linear_combination (-(j : ℂ)) * I_sq
  let S' := S.filter fun j => j ≤ (s.top : ℤ)
  have hMs : IsModeDecomposition a π S' := by
    refine ⟨?_, ?_, hM.mul_proj, hM.proj_mul_proj⟩
    · intro x
      calc
        _ = ∑ j ∈ S, π j x := Finset.sum_subset (Finset.filter_subset _ _) fun j hjS hj => by
          have h : (s.top : ℤ) < j := by
            simp only [Finset.mem_filter, not_and] at hj
            exact lt_of_not_ge (hj hjS)
          rw [s.proj_zero_above hs' hM h, LinearMap.zero_apply]
        _ = x := hM.sum_apply x
    · intro j hj
      by_cases hjS : j ∈ S
      · exact s.proj_zero_above hs' hM (by
          simp only [S', Finset.mem_filter, hjS, true_and] at hj
          omega)
      · exact hM.eq_zero _ hjS
  have hdim (j : ℤ) : Module.finrank ℂ (LinearMap.range (π j)) ≤ 1 :=
    (Submodule.finrank_mono (show LinearMap.range (π j) ≤
        ℂ ∙ s.vec ((s.top : ℤ) - j).toNat from by
      rintro _ ⟨x, rfl⟩
      exact s.proj_mem_line hs' hM j x)).trans (finrank_span_le_card {_})
  exact RealAdjacentWeightStringLifting.exists_lift hab hca hMs
    (fun j hj => (Finset.mem_filter.mp hj).2) hdim (s.raise_injective hs' hM) heig hN H v hv

private theorem modes_of_injective (L : W →ₗ[ℂ] V) (hL : Function.Injective L)
    {a : Module.End ℂ W} {b : Module.End ℂ V} {π : ℤ → Module.End ℂ W}
    {τ : ℤ → Module.End ℂ V} {S : Finset ℤ}
    (hM : IsModeDecomposition b τ S) (hab : ∀ v, L (a v) = b (L v))
    (hπτ : ∀ i v, L (π i v) = τ i (L v)) : IsModeDecomposition a π S := by
  classical
  constructor
  · intro v
    apply hL
    simp only [map_sum, hπτ, hM.sum_apply]
  · intro i hi
    ext v
    apply hL
    simp only [hπτ, hM.eq_zero _ hi, LinearMap.zero_apply, map_zero]
  · intro i
    ext v
    apply hL
    simp only [Module.End.mul_apply, LinearMap.smul_apply, map_smul, hab, hπτ, hM.apply_proj]
  · intro i j
    ext v
    apply hL
    by_cases hij : i = j
    · subst j
      simp only [↓reduceIte, Module.End.mul_apply, hπτ, hM.proj_apply_proj]
    · simp only [hij, ↓reduceIte, Module.End.mul_apply, hπτ, hM.proj_apply_proj,
        LinearMap.zero_apply, map_zero]

private theorem modes_of_surjective (L : W →ₗ[ℂ] V) (hL : Function.Surjective L)
    {a : Module.End ℂ W} {b : Module.End ℂ V} {π : ℤ → Module.End ℂ W}
    {τ : ℤ → Module.End ℂ V} {S : Finset ℤ}
    (hM : IsModeDecomposition a π S) (hab : ∀ v, L (a v) = b (L v))
    (hπτ : ∀ i v, L (π i v) = τ i (L v)) : IsModeDecomposition b τ S := by
  classical
  constructor
  · intro x
    obtain ⟨v, rfl⟩ := hL x
    simp only [← hπτ, ← map_sum, hM.sum_apply]
  · intro i hi
    ext x
    obtain ⟨v, rfl⟩ := hL x
    simp only [← hπτ, hM.eq_zero _ hi, LinearMap.zero_apply, map_zero]
  · intro i
    ext x
    obtain ⟨v, rfl⟩ := hL x
    simp only [Module.End.mul_apply, LinearMap.smul_apply, ← hπτ, ← hab, ← map_smul, hM.apply_proj]
  · intro i j
    ext x
    obtain ⟨v, rfl⟩ := hL x
    by_cases hij : i = j
    · subst j
      simp only [↓reduceIte, Module.End.mul_apply, ← hπτ, hM.proj_apply_proj]
    · simp only [hij, ↓reduceIte, Module.End.mul_apply, ← hπτ, hM.proj_apply_proj,
        LinearMap.zero_apply, map_zero]

private theorem comm_apply {a b c : Module.End ℂ W} (h : a * b - b * a = c) (v : W) :
    a (b v) - b (a v) = c v :=
  congrArg (fun T : Module.End ℂ W => T v) h

private structure RotationPair (W : Type*) [AddCommGroup W] [Module ℂ W] where
  a : Module.End ℂ W
  b : Module.End ℂ W
  c : Module.End ℂ W
  π : ℤ → Module.End ℂ W
  τ : ℤ → Module.End ℂ W
  S : Finset ℤ
  T : Finset ℤ
  hab : a * b - b * a = c
  hbc : b * c - c * b = a
  hca : c * a - a * c = b
  modeA : IsModeDecomposition a π S
  modeB : IsModeDecomposition b τ T

private theorem RotationPair.c_stable (D : RotationPair W) {U : Submodule ℂ W}
    (ha : U ≤ U.comap D.a) (hb : U ≤ U.comap D.b) : U ≤ U.comap D.c := by
  intro v hv
  change D.c v ∈ U
  rw [← comm_apply D.hab]
  exact U.sub_mem (ha (hb hv)) (hb (ha hv))

private def RotationPair.restrict (D : RotationPair W) (U : Submodule ℂ W)
    (ha : U ≤ U.comap D.a) (hb : U ≤ U.comap D.b) : RotationPair U :=
  let a := D.a.restrict (p := U) (q := U) (fun _ hv => ha hv)
  let b := D.b.restrict (p := U) (q := U) (fun _ hv => hb hv)
  let c := D.c.restrict (p := U) (q := U) (fun _ hv => D.c_stable ha hb hv)
  let π (i : ℤ) := (D.π i).restrict (p := U) (q := U)
    (fun _ hv => proj_mem_of_mem_invariant D.modeA ha i hv)
  let τ (i : ℤ) := (D.τ i).restrict (p := U) (q := U)
    (fun _ hv => proj_mem_of_mem_invariant D.modeB hb i hv)
  { a := a, b := b, c := c, π := π, τ := τ, S := D.S, T := D.T
    hab := LinearMap.ext fun v => Subtype.ext (comm_apply D.hab (v : W))
    hbc := LinearMap.ext fun v => Subtype.ext (comm_apply D.hbc (v : W))
    hca := LinearMap.ext fun v => Subtype.ext (comm_apply D.hca (v : W))
    modeA := modes_of_injective U.subtype Subtype.coe_injective (a := a) (π := π) D.modeA
      (fun _ => rfl) (fun _ _ => rfl)
    modeB := modes_of_injective U.subtype Subtype.coe_injective (a := b) (π := τ) D.modeB
      (fun _ => rfl) (fun _ _ => rfl) }

private theorem quot_comm (U : Submodule ℂ W) {a b c : Module.End ℂ W}
    (ha : U ≤ U.comap a) (hb : U ≤ U.comap b) (hc : U ≤ U.comap c)
    (h : a * b - b * a = c) :
    U.mapQ U a ha * U.mapQ U b hb - U.mapQ U b hb * U.mapQ U a ha = U.mapQ U c hc := by
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := U.mkQ_surjective x
  change U.mkQ (a (b v)) - U.mkQ (b (a v)) = U.mkQ (c v)
  rw [← map_sub, comm_apply h]

private def RotationPair.quotient (D : RotationPair W) (U : Submodule ℂ W)
    (ha : U ≤ U.comap D.a) (hb : U ≤ U.comap D.b) : RotationPair (W ⧸ U) :=
  let hc := D.c_stable ha hb
  let hπ (i : ℤ) : U ≤ U.comap (D.π i) :=
    fun _ hv => proj_mem_of_mem_invariant D.modeA ha i hv
  let hτ (i : ℤ) : U ≤ U.comap (D.τ i) :=
    fun _ hv => proj_mem_of_mem_invariant D.modeB hb i hv
  { a := U.mapQ U D.a ha, b := U.mapQ U D.b hb, c := U.mapQ U D.c hc
    π := fun i => U.mapQ U (D.π i) (hπ i), τ := fun i => U.mapQ U (D.τ i) (hτ i)
    S := D.S, T := D.T
    hab := quot_comm U ha hb hc D.hab
    hbc := quot_comm U hb hc ha D.hbc
    hca := quot_comm U hc ha hb D.hca
    modeA := modes_of_surjective U.mkQ U.mkQ_surjective D.modeA
      (b := U.mapQ U D.a ha) (τ := fun i => U.mapQ U (D.π i) (hπ i))
      (fun _ => rfl) (fun _ _ => rfl)
    modeB := modes_of_surjective U.mkQ U.mkQ_surjective D.modeB
      (b := U.mapQ U D.b hb) (τ := fun i => U.mapQ U (D.τ i) (hτ i))
      (fun _ => rfl) (fun _ _ => rfl) }

private theorem RotationPair.exists_simple [FiniteDimensional ℂ W] (D : RotationPair W)
    {v : W} (hv : v ≠ 0) :
    ∃ (U : Submodule ℂ W) (ha : U ≤ U.comap D.a) (hb : U ≤ U.comap D.b),
      U ≠ ⊥ ∧ SimplePair (D.restrict U ha hb).a (D.restrict U ha hb).b := by
  classical
  let P (d : ℕ) : Prop := ∃ U : Submodule ℂ W,
    U ≤ U.comap D.a ∧ U ≤ U.comap D.b ∧ U ≠ ⊥ ∧ Module.finrank ℂ U = d
  have hex : ∃ d, P d := ⟨Module.finrank ℂ (⊤ : Submodule ℂ W), ⊤, by simp, by simp,
    (Submodule.ne_bot_iff _).mpr ⟨v, Submodule.mem_top, hv⟩, rfl⟩
  obtain ⟨U, ha, hb, hU, hdim⟩ := Nat.find_spec hex
  refine ⟨U, ha, hb, hU, ?_⟩
  intro Y hYa hYb hY
  let Z := Y.map U.subtype
  have hZU : Z ≤ U := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hZa : Z ≤ Z.comap D.a := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨(D.restrict U ha hb).a x, hYa hx, rfl⟩
  have hZb : Z ≤ Z.comap D.b := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨(D.restrict U ha hb).b x, hYb hx, rfl⟩
  have hZ : Z ≠ ⊥ := by
    obtain ⟨x, hx, hne⟩ := (Submodule.ne_bot_iff _).mp hY
    exact (Submodule.ne_bot_iff _).mpr ⟨x, ⟨x, hx, rfl⟩, fun hz => hne (Subtype.ext hz)⟩
  have hle := Nat.find_min' hex (show P (Module.finrank ℂ Z) from ⟨Z, hZa, hZb, hZ, rfl⟩)
  have hEq : Z = U := Submodule.eq_of_le_of_finrank_le hZU (hdim.trans_le hle)
  apply top_unique
  intro x _
  have hx : (x : W) ∈ Z := hEq.symm ▸ x.property
  obtain ⟨y, hy, hyx⟩ := hx
  exact (Subtype.ext hyx : y = x) ▸ hy

private theorem proj_filter_sum {a : Module.End ℂ W} {π : ℤ → Module.End ℂ W} {S : Finset ℤ}
    (hM : IsModeDecomposition a π S) (p : ℤ → Prop) [DecidablePred p] (j : ℤ) (v : W) :
    π j (∑ i ∈ S.filter p, π i v) = if p j then π j v else 0 := by
  rw [map_sum]
  simp_rw [hM.proj_apply_proj]
  rw [Finset.sum_ite_eq]
  by_cases hj : j ∈ S
  · simp only [Finset.mem_filter, hj, true_and]
  · simp only [Finset.mem_filter, hj, false_and, hM.eq_zero j hj, LinearMap.zero_apply, ite_self]

private def RotationPair.HasLift (D : RotationPair W) (N : ℤ) (H : ℕ) : Prop :=
  ∀ v : W, (∀ j : ℤ, N + H ≤ j → D.π j (aeval (-I • D.b) (tailPolynomial H) v) = 0) →
    ∃ w : W, aeval (-I • D.b) (tailPolynomial H) w = 0 ∧
      ∀ j : ℤ, N ≤ j → D.π j w = D.π j v

private theorem lift_aux.{u} (d : ℕ) :
    ∀ (W : Type u) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W],
      Module.finrank ℂ W = d → ∀ (D : RotationPair W) (N : ℤ), 0 < N →
      ∀ H : ℕ, D.HasLift N H := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro W _ _ _ hdim D N hN H v hv
    classical
    by_cases hne : v = 0
    · exact ⟨0, map_zero _, fun _ _ => by rw [hne]⟩
    obtain ⟨U, ha, hb, hU, hsimple⟩ := D.exists_simple hne
    let Q := D.quotient U ha hb
    let R := D.restrict U ha hb
    let P := tailPolynomial H
    have hdimQ : Module.finrank ℂ (W ⧸ U) < d := by
      have hp : 0 < Module.finrank ℂ U :=
        Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hU)
      have := U.finrank_quotient_add_finrank
      omega
    have hpolyQ (x : W) : U.mkQ (aeval (-I • D.b) P x) =
        aeval (-I • Q.b) P (U.mkQ x) :=
      map_aeval_rotation U.mkQ (fun _ => rfl) P x
    obtain ⟨wQ, hwQ, hhighQ⟩ :=
      ih _ hdimQ (W ⧸ U) rfl Q N hN H (U.mkQ v) fun j hj => by
        rw [← hpolyQ]
        change U.mkQ (D.π j (aeval (-I • D.b) P v)) = 0
        rw [hv j hj, map_zero]
    obtain ⟨x, hx⟩ := U.mkQ_surjective wQ
    let roots := D.T.filter fun i : ℤ => P.eval (i : ℂ) = 0
    let w₀ := ∑ i ∈ roots, D.τ i x
    have hw₀ : aeval (-I • D.b) P w₀ = 0 := by
      apply eq_of_modes_eq D.modeB
      intro j _
      rw [map_zero, RealPolynomialFourierPropagation.proj_aeval D.modeB]
      change P.eval (j : ℂ) • D.τ j (∑ i ∈ roots, D.τ i x) = 0
      rw [proj_filter_sum D.modeB]
      split_ifs with h <;> simp only [h, zero_smul, smul_zero]
    have hw₀Q : U.mkQ w₀ = wQ := by
      change U.mkQ (∑ i ∈ roots, D.τ i x) = wQ
      rw [map_sum]
      calc
        _ = ∑ i ∈ roots, Q.τ i wQ :=
          Finset.sum_congr rfl fun i _ => by rw [← hx]; rfl
        _ = ∑ i ∈ Q.T, Q.τ i wQ := Finset.sum_subset (Finset.filter_subset _ _) fun j hj hj' => by
          have hvj : P.eval (j : ℂ) ≠ 0 := fun h =>
            hj' (Finset.mem_filter.mpr ⟨hj, h⟩)
          have hpj := RealPolynomialFourierPropagation.proj_aeval Q.modeB P j wQ
          rw [hwQ, map_zero] at hpj
          exact (smul_eq_zero.mp hpj.symm).resolve_left hvj
        _ = wQ := Q.modeB.sum_apply _
    let z := v - w₀
    have hzU (j : ℤ) (hj : N ≤ j) : D.π j z ∈ U := by
      apply (Submodule.Quotient.mk_eq_zero U).mp
      change U.mkQ (D.π j (v - w₀)) = 0
      rw [map_sub, map_sub]
      change Q.π j (U.mkQ v) - Q.π j (U.mkQ w₀) = 0
      rw [hw₀Q, hhighQ j hj, sub_self]
    let u : U := ⟨∑ i ∈ D.S.filter (fun i => N ≤ i), D.π i z,
      U.sum_mem fun j hj => hzU j (Finset.mem_filter.mp hj).2⟩
    have hu (j : ℤ) :
        D.π j (u : W) = if N ≤ j then D.π j z else 0 :=
      proj_filter_sum D.modeA _ j z
    have huP (j : ℤ) (hj : N + H ≤ j) : D.π j (aeval (-I • D.b) P (u : W)) = 0 := by
      have hlower : ∀ i : ℤ, j - P.natDegree ≤ i → i ≤ j + P.natDegree →
          D.π i (z - (u : W)) = 0 := by
        intro i hi _
        have hdegree : P.natDegree = H := tailPolynomial_natDegree H
        rw [hdegree] at hi
        rw [map_sub, hu, ite_eq_left (by omega : N ≤ i), sub_self]
      have hp := RealAdjacentFourierBand.proj_aeval_eq_zero D.hab D.hca D.modeA
        (z - (u : W)) P j hlower
      rw [map_sub, map_sub] at hp
      rw [← sub_eq_zero.mp hp]
      change D.π j (aeval (-I • D.b) P (v - w₀)) = 0
      rw [map_sub, hw₀, sub_zero, hv j hj]
    have hpolyR (y : U) : U.subtype (aeval (-I • R.b) P y) =
        aeval (-I • D.b) P (U.subtype y) :=
      map_aeval_rotation U.subtype (fun _ => rfl) P y
    obtain ⟨w₁, hw₁, hmatch⟩ := exists_lift_of_simple R.hab R.hbc R.hca R.modeA R.modeB
      hsimple hN H u fun j hj => by
        apply U.subtype_injective
        change D.π j (U.subtype (aeval (-I • R.b) P u)) = 0
        rw [hpolyR]
        exact huP j hj
    have hw₁' : aeval (-I • D.b) P (w₁ : W) = 0 := by
      change aeval (-I • D.b) P (U.subtype w₁) = 0
      rw [← hpolyR, hw₁, map_zero]
    refine ⟨w₀ + (w₁ : W), ?_, ?_⟩
    · rw [map_add, hw₀, hw₁', add_zero]
    · intro j hj
      have h : D.π j (w₁ : W) = D.π j (u : W) := congrArg U.subtype (hmatch j hj)
      rw [map_add, h, hu, ite_eq_left hj]
      change D.π j w₀ + D.π j (v - w₀) = D.π j v
      rw [map_sub]
      abel

/-- For a finite-dimensional representation with two adjacent rotation mode
decompositions, high-mode vanishing of the tail polynomial image gives a lift
of the lower high window to the polynomial kernel. -/
theorem exists_lift [FiniteDimensional ℂ W]
    {a b c : Module.End ℂ W} {π τ : ℤ → Module.End ℂ W} {S T : Finset ℤ}
    (hab : a * b - b * a = c) (hbc : b * c - c * b = a) (hca : c * a - a * c = b)
    (hM : IsModeDecomposition a π S) (hM' : IsModeDecomposition b τ T)
    {N : ℤ} (hN : 0 < N) (H : ℕ) (v : W)
    (hv : ∀ j : ℤ, N + H ≤ j → π j (aeval (-I • b) (tailPolynomial H) v) = 0) :
    ∃ w : W, aeval (-I • b) (tailPolynomial H) w = 0 ∧
      ∀ j : ℤ, N ≤ j → π j w = π j v :=
  lift_aux (Module.finrank ℂ W) W rfl ⟨a, b, c, π, τ, S, T, hab, hbc, hca, hM, hM'⟩ N hN H v hv

end Langlands.Archimedean.RealAdjacentRotationLifting

namespace Langlands.Archimedean

open Complex Polynomial RealOrthogonalUncertainty RealTailMultiplierPolynomial

/-- One-sided lifting for a finite-dimensional module with the commutator and
finite integer-mode identities of two adjacent rotations. -/
def RealAdjacentRotationLiftingStatement.{u} : Prop :=
  ∀ (W : Type u) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W],
    ∀ (a b c : Module.End ℂ W) (π τ : ℤ → Module.End ℂ W) (S T : Finset ℤ),
    a * b - b * a = c → b * c - c * b = a → c * a - a * c = b →
    IsModeDecomposition a π S → IsModeDecomposition b τ T →
    ∀ N : ℤ, 0 < N → ∀ (H : ℕ) (v : W),
    (∀ j : ℤ, N + H ≤ j → π j (aeval (-I • b) (tailPolynomial H) v) = 0) →
    ∃ w : W, aeval (-I • b) (tailPolynomial H) w = 0 ∧
      ∀ j : ℤ, N ≤ j → π j w = π j v

theorem realAdjacentRotationLifting : RealAdjacentRotationLiftingStatement := by
  intro _ _ _ _ a b c π τ S T hab hbc hca hM hM' N hN H v hv
  exact RealAdjacentRotationLifting.exists_lift hab hbc hca hM hM' hN H v hv

end Langlands.Archimedean
