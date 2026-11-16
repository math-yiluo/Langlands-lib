import Langlands.Representation.Archimedean.RealOrthogonalUncertaintyStatement
import Langlands.Representation.Archimedean.RealKTypeCount
import Langlands.Representation.Archimedean.RealBlockFourierFinite
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Derivation.Lie

/-!
# An uncertainty principle for two block rotations of `O(3)`

This file proves `RealOrthogonalBlockUncertaintyStatement`
(`realOrthogonalBlockUncertainty`): a continuous right `O(3)`-finite function on `GL_3(ℝ)` whose
left Fourier modes along `r_p = blockRotation 3 p` are all at least `n` in absolute value and whose
left Fourier modes along `r_q` are all smaller than `n' < n` in absolute value vanishes on `O(3)`,
for `{p, q} = {0, 1}`.

## Proof

* **Abstract part** (section `Abstract`). `IsModeDecomposition a π S` says that the `π m` are
  orthogonal idempotents summing to the identity, `a π_m = i m π_m`, and `π_m = 0` for `m ∉ S`.
  Let `a, b, c` be operators on a finite-dimensional space with `[a, b] = c`, `[b, c] = a` and
  `[c, a] = b` (the relations of `so(3)`). Then `E₊ = b - i c` raises the `a`-modes by one and
  `E₋ = b + i c` lowers them by one, and `((2i) a, E₋, -E₊)` is an `sl₂`-triple.
  `proj_eq_zero_of_pos`: if the `a`-modes of `v` are at least `n` in absolute value and
  `Q(-i b) v = 0` for a nonzero polynomial `Q` of degree `d < n`, take the lowest positive mode
  `k ≥ n` of `v`. The mode `k - d` of `Q(-i b) v` is a nonzero multiple of `E₋^d π_k v`, because
  the modes `k - d` of `b^e v` with `e < d` vanish. So `E₋^d π_k v = 0`, and some `E₋^e π_k v` with
  `e < d` is a nonzero primitive vector of the `sl₂`-triple with eigenvalue `-2(k - e) < 0`. This
  contradicts `IsSl2Triple.HasPrimitiveVectorWith.exists_nat`. `eq_zero_of_finite_modes` applies
  this with `Q = ∏_{j ∈ T} (X - j)` when the `b`-modes of `v` lie in a finite set `T` with
  `|T| < n`, and to `(-a, b, -c)` for the negative modes. `eq_zero_of_parity` splits `v` into the
  two eigenvectors `v ± σ v` of an operator `σ` that reverses the `a`-modes and multiplies the
  `b`-mode `j` by `(-1)^j`. Each part has its `b`-modes among the integers in `(-n', n')` of one
  parity; there are at most `n'` of them.
* **Analytic part** (section `Analytic`). The restriction of `f` to `O(3)` lies in the
  finite-dimensional space `RealKTypeCount.degreeLE 3 N` of polynomial functions of degree at most
  `N` in the matrix entries. This space is stable under left and right translation, and the mode
  projections `proj N hp m` (the left Fourier modes along `r_p`) preserve it (`projFun_mem`,
  through finitely many evaluation functionals). With `gen N hp = Σ_m i m π_m`, the derivative at
  `0` of `θ ↦ w(r_p(θ) x)` is `(gen N hp w)(x)`. The derivative along `r_p` is a derivation `der`
  of the algebra of polynomial functions on `O(3)` that acts on the matrix entries through the
  generator matrix `rotationGenerator 3 p` (`HasMatrix`). Commutators of such derivations act
  through commutators of the matrices, and a derivation is determined by its action on the
  entries. The two matrix identities `rotationGenerator_lie_one` and `rotationGenerator_lie_two`
  then give the `so(3)` relations among `gen N _` (`gen_relations`, `exists_relations`). Left
  translation by `r_q(π)` (`flipOp`) reverses the `r_p`-modes and multiplies the `r_q`-mode `j` by
  `(-1)^j`.
* **Conclusion.** The block Fourier coefficients of `f` at points of `O(3)` are `2π` times the
  values of the modes of the restriction of `f`. So the hypotheses say that the restriction
  satisfies the hypotheses of `eq_zero_of_parity`, and it vanishes.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

namespace RealOrthogonalUncertainty

open Polynomial Complex

/-! ## Mode decompositions and an `sl₂` argument -/

section Abstract

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- Mode projections for an operator `a`: `π m` projects onto the eigenspace of `a` of the
eigenvalue `i m`; the projections are orthogonal idempotents, vanish outside the finite set `S`,
and sum to the identity. -/
structure IsModeDecomposition (a : Module.End ℂ W) (π : ℤ → Module.End ℂ W) (S : Finset ℤ) :
    Prop where
  sum_apply : ∀ w, ∑ m ∈ S, π m w = w
  eq_zero : ∀ m ∉ S, π m = 0
  mul_proj : ∀ m, a * π m = (I * m) • π m
  proj_mul_proj : ∀ m m', π m * π m' = if m = m' then π m else 0

namespace IsModeDecomposition

variable {a : Module.End ℂ W} {π : ℤ → Module.End ℂ W} {S : Finset ℤ}

theorem proj_apply_proj (hM : IsModeDecomposition a π S) (m m' : ℤ) (w : W) :
    π m (π m' w) = if m = m' then π m w else 0 := by
  have h := congrArg (fun T : Module.End ℂ W => T w) (hM.proj_mul_proj m m')
  simp only [Module.End.mul_apply] at h
  rw [h]
  split_ifs <;> rfl

theorem apply_proj (hM : IsModeDecomposition a π S) (m : ℤ) (w : W) :
    a (π m w) = (I * m) • π m w := by
  have h := congrArg (fun T : Module.End ℂ W => T w) (hM.mul_proj m)
  simpa using h

theorem proj_apply (hM : IsModeDecomposition a π S) (m : ℤ) (w : W) :
    π m (a w) = (I * m) • π m w := by
  conv_lhs => rw [← hM.sum_apply w]
  rw [map_sum, map_sum]
  simp_rw [hM.apply_proj, map_smul, hM.proj_apply_proj]
  rw [Finset.sum_eq_single m]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · intro hm
    simp [hM.eq_zero m hm]

theorem proj_eq_zero_of_eigen (hM : IsModeDecomposition a π S) {u : W} {μ : ℂ}
    (hu : a u = μ • u) {m : ℤ} (hm : I * m ≠ μ) : π m u = 0 := by
  have h1 := hM.proj_apply m u
  rw [hu, map_smul] at h1
  have h2 : (I * m - μ) • π m u = 0 := by rw [sub_smul, ← h1, sub_self]
  exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hm)

theorem proj_self_of_eigen (hM : IsModeDecomposition a π S) {u : W} {μ : ℤ}
    (hu : a u = (I * μ) • u) : π μ u = u := by
  conv_rhs => rw [← hM.sum_apply u]
  rw [Finset.sum_eq_single μ]
  · intro j _ hj
    refine hM.proj_eq_zero_of_eigen hu fun h => hj ?_
    exact_mod_cast mul_left_cancel₀ I_ne_zero h
  · intro hμ
    rw [hM.eq_zero μ hμ, LinearMap.zero_apply]

theorem proj_apply_of_lie (hM : IsModeDecomposition a π S) {E : Module.End ℂ W} {s : ℤ}
    (hE : a * E - E * a = (I * s) • E) (m : ℤ) (w : W) :
    π m (E w) = E (π (m - s) w) := by
  have hj : ∀ j : ℤ, π m (E (π j w)) = if m = j + s then E (π j w) else 0 := by
    intro j
    have heig : a (E (π j w)) = (I * ((j + s : ℤ) : ℂ)) • E (π j w) := by
      have h := congrArg (fun T : Module.End ℂ W => T (π j w)) hE
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
      rw [sub_eq_iff_eq_add, hM.apply_proj, map_smul] at h
      rw [h]
      push_cast
      rw [← add_smul]
      congr 1
      ring
    split_ifs with h
    · rw [h]
      exact hM.proj_self_of_eigen heig
    · refine hM.proj_eq_zero_of_eigen heig fun h' => h ?_
      exact_mod_cast (mul_left_cancel₀ I_ne_zero h')
  conv_lhs => rw [← hM.sum_apply w]
  rw [map_sum, map_sum]
  simp_rw [hj]
  by_cases hS : m - s ∈ S
  · rw [Finset.sum_eq_single (m - s)]
    · simp
    · intro j _ hj'
      split_ifs with h
      · omega
      · rfl
    · intro h
      exact absurd hS h
  · rw [hM.eq_zero _ hS, LinearMap.zero_apply, map_zero]
    refine Finset.sum_eq_zero fun j hjS => ?_
    split_ifs with h
    · exact absurd (by rw [h, add_sub_cancel_right]; exact hjS) hS
    · rfl

theorem reflect (hM : IsModeDecomposition a π S) :
    IsModeDecomposition (-a) (fun m => π (-m)) (S.image Neg.neg) where
  sum_apply w := by
    rw [Finset.sum_image (fun x _ y _ h => neg_injective h)]
    simp_rw [neg_neg]
    exact hM.sum_apply w
  eq_zero m hm := hM.eq_zero _ fun h => hm (Finset.mem_image.mpr ⟨-m, h, neg_neg m⟩)
  mul_proj m := by
    rw [neg_mul, hM.mul_proj, ← neg_smul]
    congr 1
    push_cast
    ring
  proj_mul_proj m m' := by
    rw [hM.proj_mul_proj]
    simp only [neg_inj]

end IsModeDecomposition

/-! ### The `sl₂` argument -/

section Sl2

attribute [local instance 100] LieRing.ofAssociativeRing

open IsModeDecomposition

variable {a b c : Module.End ℂ W} {π : ℤ → Module.End ℂ W} {S : Finset ℤ}

theorem lie_raise (hab : a * b - b * a = c) (hca : c * a - a * c = b) :
    a * (b - I • c) - (b - I • c) * a = (I * ((1 : ℤ) : ℂ)) • (b - I • c) := by
  have e : a * (b - I • c) - (b - I • c) * a = (a * b - b * a) + I • (c * a - a * c) := by
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub]
    abel
  rw [e, hab, hca, smul_sub, smul_smul, Int.cast_one, mul_one, I_mul_I]
  module

theorem lie_lower (hab : a * b - b * a = c) (hca : c * a - a * c = b) :
    a * (b + I • c) - (b + I • c) * a = (I * ((-1 : ℤ) : ℂ)) • (b + I • c) := by
  have e : a * (b + I • c) - (b + I • c) * a = (a * b - b * a) - I • (c * a - a * c) := by
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_sub]
    abel
  rw [e, hab, hca, smul_add, smul_smul, Int.cast_neg, Int.cast_one, mul_neg_one, neg_smul,
    neg_mul, I_mul_I]
  module

theorem lie_raise_lower (hbc : b * c - c * b = a) :
    (b - I • c) * (b + I • c) - (b + I • c) * (b - I • c) = (2 * I) • a := by
  have e : (b - I • c) * (b + I • c) - (b + I • c) * (b - I • c) = (2 * I) • (b * c - c * b) := by
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub,
      smul_smul]
    module
  rw [e, hbc]

theorem eq_half_raise_add_lower : b = (1 / 2 : ℂ) • ((b - I • c) + (b + I • c)) := by
  module

/-- If `v` has no `a`-modes of absolute value `< n` and is killed by `Q(-i b)` for a nonzero
polynomial `Q` of degree `< n`, then the positive `a`-modes of `v` vanish. -/
theorem proj_eq_zero_of_pos [FiniteDimensional ℂ W] (hab : a * b - b * a = c)
    (hbc : b * c - c * b = a) (hca : c * a - a * c = b) (hM : IsModeDecomposition a π S)
    {n : ℕ} {Q : ℂ[X]} (hQ : Q ≠ 0) (hd : Q.natDegree < n) {v : W}
    (hv : ∀ m : ℤ, |m| < n → π m v = 0) (hQv : aeval (-I • b) Q v = 0) :
    ∀ m : ℤ, 0 < m → π m v = 0 := by
  classical
  set Ep := b - I • c with hEp
  set Em := b + I • c with hEm
  have hEpL : a * Ep - Ep * a = (I * ((1 : ℤ) : ℂ)) • Ep := lie_raise hab hca
  have hEmL : a * Em - Em * a = (I * ((-1 : ℤ) : ℂ)) • Em := lie_lower hab hca
  have hup : ∀ (m : ℤ) (w : W), π m (Ep w) = Ep (π (m - 1) w) := fun m w =>
    hM.proj_apply_of_lie hEpL m w
  have hdown : ∀ (m : ℤ) (w : W), π m (Em w) = Em (π (m + 1) w) := fun m w => by
    have h := hM.proj_apply_of_lie hEmL m w
    rwa [sub_neg_eq_add] at h
  have hb : ∀ (m : ℤ) (w : W),
      π m (b w) = (1 / 2 : ℂ) • (Ep (π (m - 1) w) + Em (π (m + 1) w)) := fun m w => by
    conv_lhs => rw [eq_half_raise_add_lower (b := b) (c := c)]
    rw [LinearMap.smul_apply, LinearMap.add_apply, map_smul, map_add, hup, hdown]
  by_contra hne
  push Not at hne
  obtain ⟨m₀, hm₀, hm₀v⟩ := hne
  have hex : ∃ j : ℕ, 0 < j ∧ π (j : ℤ) v ≠ 0 :=
    ⟨m₀.toNat, by omega, by rwa [Int.toNat_of_nonneg hm₀.le]⟩
  set k := Nat.find hex with hk
  have hkpos : 0 < k := (Nat.find_spec hex).1
  have hkv : π (k : ℤ) v ≠ 0 := (Nat.find_spec hex).2
  have hkmin : ∀ j : ℕ, 0 < j → j < k → π (j : ℤ) v = 0 := fun j hj hjk => by
    by_contra h
    exact Nat.find_min hex hjk ⟨hj, h⟩
  have hnk : n ≤ k := by
    by_contra h
    exact hkv (hv _ (by rw [abs_of_nonneg (by positivity)]; exact_mod_cast not_le.mp h))
  set d := Q.natDegree with hdQ
  -- the lowest modes of `b^e v`
  have claim : ∀ e : ℕ, e ≤ d →
      π ((k : ℤ) - e) ((b ^ e) v) = ((1 / 2 : ℂ) ^ e) • (Em ^ e) (π k v) ∧
        ∀ m : ℤ, -(n : ℤ) + e < m → m < (k : ℤ) - e → π m ((b ^ e) v) = 0 := by
    intro e
    induction e with
    | zero =>
        intro _
        refine ⟨by simp, fun m hm1 hm2 => ?_⟩
        simp only [pow_zero, Module.End.one_apply]
        rcases le_or_gt m 0 with h | h
        · exact hv m (by rw [abs_lt]; push_cast at hm1; omega)
        · have := hkmin m.toNat (by omega) (by omega)
          rwa [Int.toNat_of_nonneg h.le] at this
    | succ e ih =>
        intro he
        obtain ⟨ih1, ih2⟩ := ih (by omega)
        have hpow : ∀ w, (b ^ (e + 1)) w = b ((b ^ e) w) := fun w => by
          rw [pow_succ', Module.End.mul_apply]
        refine ⟨?_, fun m hm1 hm2 => ?_⟩
        · rw [hpow, hb, show ((k : ℤ) - ((e + 1 : ℕ) : ℤ)) + 1 = (k : ℤ) - e by push_cast; ring,
            ih1, ih2 _ (by push_cast; omega) (by push_cast; omega), map_zero, zero_add, map_smul,
            smul_smul, pow_succ' (1 / 2 : ℂ), pow_succ' Em, Module.End.mul_apply]
        · rw [hpow, hb, ih2 _ (by push_cast at hm1 ⊢; omega) (by push_cast at hm2 ⊢; omega),
            ih2 _ (by push_cast at hm1 ⊢; omega) (by push_cast at hm2 ⊢; omega), map_zero,
            map_zero, add_zero, smul_zero]
  -- extract the mode `k - d` of `Q(-i b) v`
  have hlow : (Em ^ d) (π k v) = 0 := by
    have h := congrArg (π ((k : ℤ) - d)) hQv
    rw [map_zero, aeval_eq_sum_range, LinearMap.sum_apply, map_sum,
      Finset.sum_eq_single d] at h
    · rw [LinearMap.smul_apply, map_smul, smul_pow, LinearMap.smul_apply, map_smul,
        (claim d le_rfl).1, smul_smul, smul_smul] at h
      refine (smul_eq_zero.mp h).resolve_left ?_
      refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ (neg_ne_zero.mpr I_ne_zero)))
        (pow_ne_zero _ (by norm_num))
      exact leadingCoeff_ne_zero.mpr hQ
    · intro e he hed
      have hed' : e < d := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp he)) hed
      rw [LinearMap.smul_apply, map_smul, smul_pow, LinearMap.smul_apply, map_smul,
        (claim e hed'.le).2 _ (by omega) (by omega), smul_zero, smul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self d)) h
  -- a primitive vector of positive mode
  obtain ⟨e, he1, he2⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists
    (p := fun e => (Em ^ e) (π k v) = 0) (by simpa using hkv) ⟨d, hlow⟩
  have hed : e < d := by
    by_contra h
    apply he1
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp h)
    show (Em ^ (d + j)) (π k v) = 0
    rw [add_comm, pow_add, Module.End.mul_apply, hlow, map_zero]
  have heig : ∀ j : ℕ, a ((Em ^ j) (π k v)) = (I * ((k : ℤ) - j : ℤ)) • (Em ^ j) (π k v) := by
    intro j
    induction j with
    | zero => simpa using hM.apply_proj k v
    | succ j ih =>
        have h := congrArg (fun T : Module.End ℂ W => T ((Em ^ j) (π k v))) hEmL
        simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
        rw [sub_eq_iff_eq_add, ih, map_smul] at h
        rw [pow_succ', Module.End.mul_apply, h]
        push_cast
        rw [← add_smul]
        congr 1
        ring
  have ha0 : a ≠ 0 := by
    intro h
    have := hM.apply_proj k v
    rw [h, LinearMap.zero_apply, eq_comm, smul_eq_zero] at this
    rcases this with h' | h'
    · exact mul_ne_zero I_ne_zero (by exact_mod_cast hkpos.ne') h'
    · exact hkv h'
  have t : IsSl2Triple ((2 * I) • a) Em (-Ep) :=
    { h_ne_zero := smul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) ha0
      lie_e_f := by
        have hEE : Ep * Em - Em * Ep = (2 * I) • a := lie_raise_lower hbc
        rw [Ring.lie_def, ← hEE, mul_neg, neg_mul, sub_neg_eq_add]
        abel
      lie_h_e_nsmul := by
        rw [Ring.lie_def, smul_mul_assoc, mul_smul_comm, ← smul_sub, hEmL, smul_smul]
        rw [two_nsmul, ← two_smul ℂ]
        congr 1
        push_cast
        ring_nf
        rw [I_sq]
        ring
      lie_h_f_nsmul := by
        rw [Ring.lie_def, smul_mul_assoc, mul_smul_comm, mul_neg, neg_mul, ← smul_sub,
          neg_sub_neg, ← neg_sub, hEpL, smul_neg, smul_smul, smul_neg, neg_neg, ← neg_smul,
          ← Nat.cast_smul_eq_nsmul ℂ]
        congr 1
        push_cast
        linear_combination (-2 : ℂ) * I_sq }
  have P : t.HasPrimitiveVectorWith ((Em ^ e) (π k v)) (-2 * ((k : ℂ) - e)) :=
    { ne_zero := he1
      lie_h := by
        rw [Module.End.lie_apply, LinearMap.smul_apply, heig, smul_smul]
        congr 1
        push_cast
        ring_nf
        rw [I_sq]
        ring
      lie_e := by
        rw [Module.End.lie_apply, ← Module.End.mul_apply, ← pow_succ']
        exact he2 }
  obtain ⟨r, hr⟩ := P.exists_nat
  have hr' : (-2 * ((k : ℤ) - e) : ℤ) = r := by exact_mod_cast hr
  omega

/-- A vector whose `b`-modes lie in `T` is killed by `∏_{j ∈ T} (-i b - j)`. -/
theorem aeval_prod_apply_eq_zero {πb : ℤ → Module.End ℂ W} {Sb : Finset ℤ}
    (hMb : IsModeDecomposition b πb Sb) (T : Finset ℤ) {v : W}
    (hvT : ∀ j ∉ T, πb j v = 0) :
    aeval (-I • b) (∏ j ∈ T, (X - C (j : ℂ))) v = 0 := by
  classical
  have hj : ∀ j ∈ T, aeval (-I • b) (∏ j ∈ T, (X - C (j : ℂ))) (πb j v) = 0 := by
    intro j hj
    rw [← Finset.prod_erase_mul _ _ hj, map_mul, Module.End.mul_apply]
    have h0 : aeval (-I • b) (X - C (j : ℂ)) (πb j v) = 0 := by
      rw [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, LinearMap.smul_apply, hMb.apply_proj,
        smul_smul, Module.algebraMap_end_apply, ← sub_smul,
        show -I * (I * (j : ℂ)) - j = 0 by linear_combination (-(j : ℂ)) * I_sq, zero_smul]
    rw [h0, map_zero]
  rw [← hMb.sum_apply v, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases h : j ∈ T
  · exact hj j h
  · rw [hvT j h, map_zero]

/-- **Abstract uncertainty principle.** If the `a`-modes of `v` are all at least `n` in absolute
value and the `b`-modes of `v` lie in a set of fewer than `n` integers, then `v = 0`. -/
theorem eq_zero_of_finite_modes [FiniteDimensional ℂ W] (hab : a * b - b * a = c)
    (hbc : b * c - c * b = a) (hca : c * a - a * c = b) (hM : IsModeDecomposition a π S)
    {πb : ℤ → Module.End ℂ W} {Sb : Finset ℤ} (hMb : IsModeDecomposition b πb Sb)
    {n : ℕ} (T : Finset ℤ) (hT : T.card < n) {v : W}
    (hvT : ∀ j ∉ T, πb j v = 0) (hv : ∀ m : ℤ, |m| < n → π m v = 0) : v = 0 := by
  classical
  set Q : ℂ[X] := ∏ j ∈ T, (X - C (j : ℂ)) with hQ
  have hQ0 : Q ≠ 0 :=
    (monic_prod_of_monic T (fun j : ℤ => X - C (j : ℂ)) fun j _ => monic_X_sub_C (j : ℂ)).ne_zero
  have hQd : Q.natDegree < n := by
    rw [hQ, natDegree_finsetProd_X_sub_C_eq_card]
    exact hT
  have hQv : aeval (-I • b) Q v = 0 := aeval_prod_apply_eq_zero hMb T hvT
  have hpos := proj_eq_zero_of_pos hab hbc hca hM hQ0 hQd hv hQv
  have hneg := proj_eq_zero_of_pos (a := -a) (b := b) (c := -c)
    (by rw [neg_mul, mul_neg, sub_neg_eq_add, neg_add_eq_sub, ← neg_sub, hab])
    (by rw [mul_neg, neg_mul, sub_neg_eq_add, neg_add_eq_sub, ← neg_sub, hbc])
    (by rw [neg_mul_neg, neg_mul_neg, hca]) hM.reflect hQ0 hQd
    (fun m hm => hv (-m) (by rwa [abs_neg])) hQv
  have hall : ∀ m : ℤ, π m v = 0 := by
    intro m
    rcases lt_trichotomy m 0 with h | h | h
    · have := hneg (-m) (by omega)
      rwa [neg_neg] at this
    · exact hv m (by rw [h, abs_zero]; omega)
    · exact hpos m h
  rw [← hM.sum_apply v]
  exact Finset.sum_eq_zero fun m _ => hall m

/-- The even or odd integers in `(-n', n')` number at most `n'`. -/
theorem card_filter_parity_le (n' : ℕ) (ε : ℤ) :
    ((Finset.Ioo (-(n' : ℤ)) n').filter (fun j => (j - ε) % 2 = 0)).card ≤ n' := by
  classical
  calc ((Finset.Ioo (-(n' : ℤ)) n').filter (fun j => (j - ε) % 2 = 0)).card
      ≤ (Finset.range n').card := by
        refine Finset.card_le_card_of_injOn (fun j => ((j + n') / 2).toNat) ?_ ?_
        · intro j hj
          simp only [Finset.coe_filter, Finset.mem_Ioo, Set.mem_ofPred_eq] at hj
          simp only [Finset.coe_range, Set.mem_Iio]
          omega
        · intro j hj j' hj' h
          simp only [Finset.coe_filter, Finset.mem_Ioo, Set.mem_ofPred_eq] at hj hj'
          simp only at h
          omega
    _ = n' := Finset.card_range n'

/-- **Abstract uncertainty principle with a parity symmetry.** Let `σ` reverse the `a`-modes and
multiply the `b`-mode `j` by `(-1)^j`. If the `a`-modes of `v` are all at least `n` in absolute
value and the `b`-modes of `v` are all smaller than `n' < n` in absolute value, then `v = 0`. -/
theorem eq_zero_of_parity [FiniteDimensional ℂ W] (hab : a * b - b * a = c)
    (hbc : b * c - c * b = a) (hca : c * a - a * c = b) (hM : IsModeDecomposition a π S)
    {πb : ℤ → Module.End ℂ W} {Sb : Finset ℤ} (hMb : IsModeDecomposition b πb Sb)
    (σ : Module.End ℂ W) (hσa : ∀ (m : ℤ) (w : W), π m (σ w) = σ (π (-m) w))
    (hσb : ∀ (j : ℤ) (w : W), πb j (σ w) = ((-1 : ℂ) ^ j) • πb j w)
    {n n' : ℕ} (hnn : n' < n) {v : W} (hv : ∀ m : ℤ, |m| < n → π m v = 0)
    (hvb : ∀ j : ℤ, (n' : ℤ) ≤ |j| → πb j v = 0) : v = 0 := by
  classical
  have key : ∀ ε : ℂ, ∀ e : ℤ, ε = (-1 : ℂ) ^ e →
      (1 / 2 : ℂ) • (v + ε • σ v) = 0 := by
    intro ε e hε
    refine eq_zero_of_finite_modes hab hbc hca hM hMb
      ((Finset.Ioo (-(n' : ℤ)) n').filter (fun j => (j - e) % 2 = 0))
      ((card_filter_parity_le n' e).trans_lt hnn) ?_ ?_
    · intro j hj
      rw [map_smul, map_add, map_smul, hσb, smul_smul]
      simp only [Finset.mem_filter, Finset.mem_Ioo, not_and_or, not_lt] at hj
      rcases hj with (hj | hj) | hj
      · rw [hvb j (by rw [abs_of_nonpos (by omega)]; omega), smul_zero, add_zero, smul_zero]
      · rw [hvb j (by rw [abs_of_nonneg (by omega)]; exact hj), smul_zero, add_zero, smul_zero]
      · have hodd : Odd (j - e) := Int.odd_iff.mpr (by omega)
        have h1 : ε * (-1 : ℂ) ^ j = -1 := by
          rw [hε, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
            show e + j = (j - e) + 2 * e by ring, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
            hodd.neg_one_zpow, (even_two_mul e).neg_one_zpow, mul_one]
        rw [h1, neg_one_smul, add_neg_cancel, smul_zero]
    · intro m hm
      rw [map_smul, map_add, map_smul, hσa, hv m hm, hv (-m) (by rwa [abs_neg]), map_zero,
        smul_zero, add_zero, smul_zero]
  have hp := key 1 0 (by simp)
  have hm := key (-1) 1 (by simp)
  calc v = (1 / 2 : ℂ) • (v + (1 : ℂ) • σ v) + (1 / 2 : ℂ) • (v + (-1 : ℂ) • σ v) := by module
    _ = 0 := by rw [hp, hm, add_zero]

end Sl2

/-- Swapping the roles of `g₀` and `g₁` in the two commutation relations. -/
theorem relations_swap {g₀ g₁ : Module.End ℂ W}
    (r₁ : g₁ * (g₀ * g₁ - g₁ * g₀) - (g₀ * g₁ - g₁ * g₀) * g₁ = g₀)
    (r₂ : (g₀ * g₁ - g₁ * g₀) * g₀ - g₀ * (g₀ * g₁ - g₁ * g₀) = g₁) :
    g₀ * (g₁ * g₀ - g₀ * g₁) - (g₁ * g₀ - g₀ * g₁) * g₀ = g₁ ∧
      (g₁ * g₀ - g₀ * g₁) * g₁ - g₁ * (g₁ * g₀ - g₀ * g₁) = g₀ := by
  constructor
  · refine Eq.trans ?_ r₂
    simp only [mul_sub, sub_mul, mul_assoc]
    abel
  · refine Eq.trans ?_ r₁
    simp only [mul_sub, sub_mul, mul_assoc]
    abel

end Abstract

/-! ## Rotations of `O(3)` acting on polynomial functions -/

section Analytic

open RealKTypeCount RealBlockFourierFinite RealBlockRotation OrthogonalFinitePolynomial

local notation "K3" => Matrix.unitaryGroup (Fin 3) ℝ

/-- The block rotation `r_p(θ)` as an element of `O(3)`. -/
def rot (p : ℕ) (θ : ℝ) : K3 :=
  ⟨(blockRotation 3 p θ : Matrix (Fin 3) (Fin 3) ℝ), blockRotation_mem_unitaryCompact 3 p θ⟩

theorem rot_val (p : ℕ) (θ : ℝ) :
    ((rot p θ : K3) : Matrix (Fin 3) (Fin 3) ℝ) = blockRotation 3 p θ :=
  rfl

theorem rot_add (p : ℕ) (θ φ : ℝ) : rot p (θ + φ) = rot p θ * rot p φ := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, rot_val, rot_val, rot_val, blockRotation_add, Units.val_mul]

theorem rot_zero (p : ℕ) : rot p 0 = 1 := by
  apply Subtype.ext
  rw [rot_val, blockRotation_zero]
  rfl

theorem rot_add_two_pi {p : ℕ} (hp : p + 1 < 3) (θ : ℝ) :
    rot p (θ + 2 * Real.pi) = rot p θ := by
  apply Subtype.ext
  rw [rot_val, rot_val, blockRotation_add_two_pi hp]

theorem toUnits_rot_mul (p : ℕ) (θ : ℝ) (κ : K3) :
    Unitary.toUnits (rot p θ * κ) = blockRotation 3 p θ * Unitary.toUnits κ := by
  rw [map_mul]
  congr 1
  exact toUnits_mk (blockRotation_mem_unitaryCompact 3 p θ)

/-! ### Orbits are trigonometric polynomials -/

/-- The orbit function `θ ↦ w(r_p(θ) x)`. -/
def orb (p : ℕ) (w : K3 → ℂ) (x : K3) : ℝ → ℂ := fun θ => w (rot p θ * x)

/-- The algebra homomorphism `w ↦ (θ ↦ w(r_p(θ) x))`. -/
def orbAlgHom (p : ℕ) (x : K3) : (K3 → ℂ) →ₐ[ℂ] (ℝ → ℂ) :=
  AlgHom.pi fun θ => Pi.evalAlgHom ℂ (fun _ : K3 => ℂ) (rot p θ * x)

theorem one_le_trigPoly_zero : (1 : Submodule ℂ (ℝ → ℂ)) ≤ trigPoly 0 := by
  rw [Submodule.one_le]
  exact const_mem_trigPoly 1

theorem trigPoly_one_pow_le (N : ℕ) : trigPoly 1 ^ N ≤ trigPoly N := by
  induction N with
  | zero =>
      rw [pow_zero]
      exact one_le_trigPoly_zero
  | succ N ih =>
      rw [pow_succ]
      exact Submodule.mul_le.mpr fun F hF G hG => mul_mem_trigPoly (ih hF) hG

theorem map_orbAlgHom_linearSpan_le {p : ℕ} (hp : p + 1 < 3) (x : K3) :
    (RealKTypeCount.linearSpan 3).map (orbAlgHom p x).toLinearMap ≤ trigPoly 1 := by
  rw [linearSpan, Submodule.map_sup, Submodule.map_span]
  refine sup_le ?_ ?_
  · rw [Submodule.map_one]
    exact one_le_trigPoly_zero.trans (trigPoly_mono zero_le_one)
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨ij, rfl⟩, rfl⟩
    exact entry_blockRotation_mul_mem_trigPoly hp (x : Matrix (Fin 3) (Fin 3) ℝ) ij.1 ij.2

theorem orb_mem_trigPoly {p : ℕ} (hp : p + 1 < 3) {N : ℕ} {w : K3 → ℂ}
    (hw : w ∈ RealKTypeCount.degreeLE 3 N) (x : K3) : orb p w x ∈ trigPoly N := by
  have h : (RealKTypeCount.degreeLE 3 N).map (orbAlgHom p x).toLinearMap ≤ trigPoly N := by
    rw [RealKTypeCount.degreeLE, Submodule.map_pow]
    exact (pow_le_pow_left' (map_orbAlgHom_linearSpan_le hp x) N).trans (trigPoly_one_pow_le N)
  exact h ⟨w, hw, rfl⟩

theorem continuous_orb {p : ℕ} (hp : p + 1 < 3) {N : ℕ} {w : K3 → ℂ}
    (hw : w ∈ RealKTypeCount.degreeLE 3 N) (x : K3) : Continuous (orb p w x) :=
  continuous_of_mem_trigPoly (orb_mem_trigPoly hp hw x)

theorem periodic_orb {p : ℕ} (hp : p + 1 < 3) (w : K3 → ℂ) (x : K3) :
    Function.Periodic (orb p w x) (2 * Real.pi) := fun θ => by
  simp only [orb, rot_add_two_pi hp]

theorem orb_rot_mul (p : ℕ) (w : K3 → ℂ) (x : K3) (φ : ℝ) :
    orb p w (rot p φ * x) = fun θ => orb p w x (θ + φ) := by
  funext θ
  simp only [orb, rot_add, mul_assoc]

theorem orb_zero (p : ℕ) (w : K3 → ℂ) (x : K3) : orb p w x 0 = w x := by
  simp only [orb, rot_zero, one_mul]

/-! ### Mode projections -/

/-- The `m`-th left Fourier mode `x ↦ (2π)⁻¹ ∫₀^{2π} w(r_p(θ) x) e^{-imθ} dθ`. -/
def projFun (p : ℕ) (m : ℤ) (w : K3 → ℂ) : K3 → ℂ := fun x =>
  (2 * (Real.pi : ℂ))⁻¹ * coeff m (orb p w x)

theorem two_pi_ne_zero : (2 * (Real.pi : ℂ)) ≠ 0 :=
  mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

theorem projFun_rot_mul {p : ℕ} (hp : p + 1 < 3) (m : ℤ) (w : K3 → ℂ) (x : K3) (φ : ℝ) :
    projFun p m w (rot p φ * x) = expMode m φ * projFun p m w x := by
  simp only [projFun, orb_rot_mul, coeff_comp_add (periodic_orb hp w x)]
  ring

theorem orb_projFun {p : ℕ} (hp : p + 1 < 3) (m : ℤ) (w : K3 → ℂ) (x : K3) :
    orb p (projFun p m w) x = projFun p m w x • expMode m := by
  funext θ
  rw [Pi.smul_apply, smul_eq_mul, mul_comm]
  exact projFun_rot_mul hp m w x θ

/-- The modes of a function in `RealKTypeCount.degreeLE 3 N` lie in `RealKTypeCount.degreeLE 3 N`. -/
theorem projFun_mem {p : ℕ} (hp : p + 1 < 3) {N : ℕ} (m : ℤ) {w : K3 → ℂ}
    (hw : w ∈ RealKTypeCount.degreeLE 3 N) : projFun p m w ∈ RealKTypeCount.degreeLE 3 N := by
  let U := RealKTypeCount.degreeLE 3 N
  let ℓ : U →ₗ[ℂ] ℂ :=
    { toFun := fun u => coeff m (orb p u 1)
      map_add' := fun u u' => coeff_add (continuous_orb hp u.2 1) (continuous_orb hp u'.2 1) m
      map_smul' := fun c u => coeff_smul c _ m }
  let e : K3 → U →ₗ[ℂ] ℂ := fun κ =>
    (LinearMap.proj (R := ℂ) (φ := fun _ : K3 => ℂ) κ).comp U.subtype
  obtain ⟨k, pt, c, hsum⟩ := exists_sum_of_separating e ⊤
    (fun s _ hs => Subtype.ext (funext fun κ => hs κ)) ℓ
  have key : projFun p m w = (2 * (Real.pi : ℂ))⁻¹ • ∑ i, c i • fun x => w (pt i * x) := by
    funext x
    have hx := hsum ⟨fun y => w (y * x), right_mem_degreeLE hw x⟩ Submodule.mem_top
    have horb : orb p (fun y => w (y * x)) 1 = orb p w x := by
      funext θ
      simp only [orb, mul_one]
    change coeff m (orb p (fun y => w (y * x)) 1) = _ at hx
    rw [horb] at hx
    simp only [projFun, hx, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rfl
  rw [key]
  exact Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (left_mem_degreeLE hw (pt i)))

variable (N : ℕ)

/-- The mode projection `π_m` on `RealKTypeCount.degreeLE 3 N`. -/
def proj {p : ℕ} (hp : p + 1 < 3) (m : ℤ) : Module.End ℂ (RealKTypeCount.degreeLE 3 N) where
  toFun w := ⟨projFun p m w, projFun_mem hp m w.2⟩
  map_add' w w' := by
    apply Subtype.ext
    funext x
    show (2 * (Real.pi : ℂ))⁻¹ * coeff m (orb p w x + orb p w' x) =
      (2 * (Real.pi : ℂ))⁻¹ * coeff m (orb p w x) + (2 * (Real.pi : ℂ))⁻¹ * coeff m (orb p w' x)
    rw [coeff_add (continuous_orb hp w.2 x) (continuous_orb hp w'.2 x), mul_add]
  map_smul' c w := by
    apply Subtype.ext
    funext x
    show (2 * (Real.pi : ℂ))⁻¹ * coeff m (c • orb p w x) =
      c * ((2 * (Real.pi : ℂ))⁻¹ * coeff m (orb p w x))
    rw [coeff_smul]
    ring

theorem proj_coe {p : ℕ} (hp : p + 1 < 3) (m : ℤ) (w : RealKTypeCount.degreeLE 3 N) :
    ((proj N hp m w : RealKTypeCount.degreeLE 3 N) : K3 → ℂ) = projFun p m w :=
  rfl

theorem proj_mul_proj' {p : ℕ} (hp : p + 1 < 3) (m m' : ℤ) :
    proj N hp m * proj N hp m' = if m = m' then proj N hp m else 0 := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  funext x
  rw [Module.End.mul_apply, proj_coe]
  have h : projFun p m (projFun p m' w) x =
      if m = m' then projFun p m w x else 0 := by
    simp only [projFun]
    rw [orb_projFun hp, coeff_smul, coeff_expMode]
    split_ifs with h1 h2 h2
    · subst h1
      field_simp [two_pi_ne_zero]
      simp only [projFun]
      field_simp [two_pi_ne_zero]
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rw [mul_zero, mul_zero]
  rw [proj_coe, h]
  split_ifs <;> rfl

theorem proj_eq_zero {p : ℕ} (hp : p + 1 < 3) {m : ℤ}
    (hm : m ∉ Finset.Icc (-(N : ℤ)) N) : proj N hp m = 0 := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  funext x
  rw [proj_coe]
  show (2 * (Real.pi : ℂ))⁻¹ * coeff m (orb p w x) = 0
  rw [coeff_eq_zero_of_mem_trigPoly (orb_mem_trigPoly hp w.2 x), mul_zero]
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hm
  rw [lt_abs]
  omega

theorem sum_proj_apply {p : ℕ} (hp : p + 1 < 3) (w : RealKTypeCount.degreeLE 3 N) :
    ∑ m ∈ Finset.Icc (-(N : ℤ)) N, proj N hp m w = w := by
  apply Subtype.ext
  funext x
  rw [Submodule.coe_sum, Finset.sum_apply]
  have h := eq_sum_coeff_of_mem_trigPoly (orb_mem_trigPoly hp w.2 x) 0
  rw [orb_zero] at h
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [proj_coe]
  simp [projFun, expMode]

/-- The generator `Σ_m i m π_m` of the left rotations `r_p` on `RealKTypeCount.degreeLE 3 N`. -/
def gen {p : ℕ} (hp : p + 1 < 3) : Module.End ℂ (RealKTypeCount.degreeLE 3 N) :=
  ∑ m ∈ Finset.Icc (-(N : ℤ)) N, (I * m) • proj N hp m

theorem isModeDecomposition {p : ℕ} (hp : p + 1 < 3) :
    IsModeDecomposition (gen N hp) (proj N hp) (Finset.Icc (-(N : ℤ)) N) where
  sum_apply := sum_proj_apply N hp
  eq_zero _ hm := proj_eq_zero N hp hm
  mul_proj m := by
    rw [gen, Finset.sum_mul]
    simp_rw [smul_mul_assoc, proj_mul_proj', smul_ite, smul_zero]
    rw [Finset.sum_ite_eq']
    split_ifs with hm
    · rfl
    · rw [proj_eq_zero N hp hm, smul_zero]
  proj_mul_proj := proj_mul_proj' N hp

/-! ### Derivatives of orbits -/

theorem hasDerivAt_expMode (m : ℤ) (θ : ℝ) :
    HasDerivAt (expMode m) (I * m * expMode m θ) θ := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 θ := by
    simpa using (hasDerivAt_id θ).ofReal_comp
  have h2 := ((h1.const_mul (m : ℂ)).mul_const I).cexp
  show HasDerivAt (fun t : ℝ => Complex.exp ((m : ℂ) * (t : ℂ) * I)) _ θ
  convert h2 using 1
  simp only [expMode]
  ring

theorem expMode_zero_right (m : ℤ) : expMode m 0 = 1 := by
  simp [expMode]

theorem gen_apply_coe {p : ℕ} (hp : p + 1 < 3) (w : RealKTypeCount.degreeLE 3 N) (x : K3) :
    ((gen N hp w : RealKTypeCount.degreeLE 3 N) : K3 → ℂ) x =
      ∑ m ∈ Finset.Icc (-(N : ℤ)) N, I * m * projFun p m w x := by
  rw [gen, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  rfl

/-- The derivative at `0` of the orbit `θ ↦ w(r_p(θ) x)` is `(gen w)(x)`. -/
theorem hasDerivAt_orb_gen {p : ℕ} (hp : p + 1 < 3) (w : RealKTypeCount.degreeLE 3 N) (x : K3) :
    HasDerivAt (orb p w x) (((gen N hp w : RealKTypeCount.degreeLE 3 N) : K3 → ℂ) x) 0 := by
  have he : orb p w x = fun θ => (2 * (Real.pi : ℂ))⁻¹ *
      ∑ j ∈ Finset.Icc (-(N : ℤ)) N, coeff j (orb p w x) * expMode j θ :=
    funext (eq_sum_coeff_of_mem_trigPoly (orb_mem_trigPoly hp w.2 x))
  have hs := HasDerivAt.fun_sum (u := Finset.Icc (-(N : ℤ)) N)
    (A := fun j θ => coeff j (orb p w x) * expMode j θ)
    (A' := fun j => coeff j (orb p w x) * (I * j * expMode j 0)) (x := (0 : ℝ))
    (fun j _ => (hasDerivAt_expMode j 0).const_mul _)
  have h := hs.const_mul (2 * (Real.pi : ℂ))⁻¹
  rw [he]
  convert h using 1
  rw [gen_apply_coe, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [projFun, expMode_zero_right]
  ring

/-! ### Derivations of the polynomial functions -/

local notation "P3" => OrthogonalFinitePolynomial.polynomialFunctions 3

theorem linearSpan_le_polynomialFunctions :
    RealKTypeCount.linearSpan 3 ≤ Subalgebra.toSubmodule P3 := by
  refine sup_le ?_ ?_
  · rw [Submodule.one_le]
    exact Subalgebra.one_mem _
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨ij, rfl⟩
    exact OrthogonalFinitePolynomial.entry_mem_polynomialFunctions ij

theorem degreeLE_le_polynomialFunctions (N : ℕ) :
    RealKTypeCount.degreeLE 3 N ≤ Subalgebra.toSubmodule P3 := by
  induction N with
  | zero =>
      rw [RealKTypeCount.degreeLE, pow_zero, Submodule.one_le]
      exact Subalgebra.one_mem _
  | succ N ih =>
      rw [RealKTypeCount.degreeLE, pow_succ]
      exact Submodule.mul_le.mpr fun a ha b hb =>
        Subalgebra.mul_mem _ (ih ha) (linearSpan_le_polynomialFunctions hb)

/-- The derivative `x ↦ d/dθ w(r_p(θ) x)` at `θ = 0`. -/
def derFun (p : ℕ) (w : K3 → ℂ) : K3 → ℂ := fun x => deriv (orb p w x) 0

theorem derFun_eq_gen {p : ℕ} (hp : p + 1 < 3) (w : RealKTypeCount.degreeLE 3 N) :
    derFun p w = ((gen N hp w : RealKTypeCount.degreeLE 3 N) : K3 → ℂ) := by
  funext x
  exact (hasDerivAt_orb_gen N hp w x).deriv

theorem hasDerivAt_orb_of_mem {p : ℕ} (hp : p + 1 < 3) {w : K3 → ℂ} (hw : w ∈ P3) (x : K3) :
    HasDerivAt (orb p w x) (derFun p w x) 0 := by
  obtain ⟨N, hN⟩ := RealKTypeCount.exists_mem_degreeLE hw
  exact (hasDerivAt_orb_gen N hp ⟨w, hN⟩ x).differentiableAt.hasDerivAt

theorem derFun_mem {p : ℕ} (hp : p + 1 < 3) {w : K3 → ℂ} (hw : w ∈ P3) : derFun p w ∈ P3 := by
  obtain ⟨N, hN⟩ := RealKTypeCount.exists_mem_degreeLE hw
  have h := derFun_eq_gen N hp ⟨w, hN⟩
  rw [show ((⟨w, hN⟩ : RealKTypeCount.degreeLE 3 N) : K3 → ℂ) = w from rfl] at h
  rw [h]
  exact degreeLE_le_polynomialFunctions N (gen N hp ⟨w, hN⟩).2

/-- The derivative along the left rotations `r_p` as a derivation of the polynomial functions. -/
def der {p : ℕ} (hp : p + 1 < 3) : Derivation ℂ P3 P3 :=
  Derivation.mk'
    { toFun := fun w => ⟨derFun p w, derFun_mem hp w.2⟩
      map_add' := fun w w' => by
        apply Subtype.ext
        funext x
        exact ((hasDerivAt_orb_of_mem hp w.2 x).add (hasDerivAt_orb_of_mem hp w'.2 x)).deriv
      map_smul' := fun c w => by
        apply Subtype.ext
        funext x
        exact ((hasDerivAt_orb_of_mem hp w.2 x).const_mul c).deriv }
    fun w w' => by
      apply Subtype.ext
      funext x
      have h := ((hasDerivAt_orb_of_mem hp w.2 x).mul (hasDerivAt_orb_of_mem hp w'.2 x)).deriv
      rw [orb_zero, orb_zero] at h
      show deriv (orb p w x * orb p w' x) 0 =
        (w : K3 → ℂ) x * derFun p w' x + (w' : K3 → ℂ) x * derFun p w x
      rw [h]
      ring

theorem der_coe {p : ℕ} (hp : p + 1 < 3) (w : P3) : ((der hp w : P3) : K3 → ℂ) = derFun p w :=
  rfl

/-- The matrix entry `x ↦ x_{ik}` as a polynomial function. -/
def entryP (ij : Fin 3 × Fin 3) : P3 :=
  ⟨OrthogonalFinitePolynomial.entry 3 ij,
    OrthogonalFinitePolynomial.entry_mem_polynomialFunctions ij⟩

theorem entryP_apply (ij : Fin 3 × Fin 3) (x : K3) :
    (entryP ij : K3 → ℂ) x = ((x : Matrix (Fin 3) (Fin 3) ℝ) ij.1 ij.2 : ℂ) :=
  rfl

/-- `δ` acts on the matrix entries through the left matrix `X`: `δ x_{ik} = Σ_l X_{il} x_{lk}`. -/
def HasMatrix (δ : Derivation ℂ P3 P3) (X : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ i k : Fin 3, δ (entryP (i, k)) = ∑ l, ((X i l : ℝ) : ℂ) • entryP (l, k)

theorem hasMatrix_der {p : ℕ} (hp : p + 1 < 3) : HasMatrix (der hp) (rotationGenerator 3 p) := by
  intro i k
  apply Subtype.ext
  funext x
  set A := (x : Matrix (Fin 3) (Fin 3) ℝ) with hA
  have he : orb p (entryP (i, k)) x = fun θ => (((A i k + (Real.cos θ - 1) * (blockProj hp * A) i k
      + Real.sin θ * (rotationGenerator 3 p * A) i k : ℝ)) : ℂ) := by
    funext θ
    rw [orb, entryP_apply, Submonoid.coe_mul, rot_val, blockRotation_val_eq hp,
      rotMatrix_mul_apply hp]
  have hr : HasDerivAt (fun θ : ℝ => A i k + (Real.cos θ - 1) * (blockProj hp * A) i k
      + Real.sin θ * (rotationGenerator 3 p * A) i k) ((rotationGenerator 3 p * A) i k) 0 := by
    have := ((((Real.hasDerivAt_cos 0).sub_const 1).mul_const ((blockProj hp * A) i k)).const_add
      (A i k)).add ((Real.hasDerivAt_sin 0).mul_const ((rotationGenerator 3 p * A) i k))
    convert this using 1
    simp
  have hd := hr.ofReal_comp
  rw [← he] at hd
  rw [der_coe]
  show deriv (orb p (entryP (i, k)) x) 0 = _
  rw [hd.deriv, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, Matrix.mul_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Subalgebra.coe_smul, Pi.smul_apply, entryP_apply, smul_eq_mul, Complex.ofReal_mul]

theorem hasMatrix_lie {δ δ' : Derivation ℂ P3 P3} {X X' : Matrix (Fin 3) (Fin 3) ℝ}
    (h : HasMatrix δ X) (h' : HasMatrix δ' X') : HasMatrix ⁅δ, δ'⁆ (X' * X - X * X') := by
  unfold HasMatrix at h h' ⊢
  intro i k
  simp only [Derivation.commutator_apply, h, h', map_sum, Derivation.map_smul, Finset.smul_sum, smul_smul,
    Matrix.sub_apply, Matrix.mul_apply, Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_mul,
    sub_smul, Finset.sum_smul, Finset.sum_sub_distrib]
  congr 1 <;> exact Finset.sum_comm

theorem eq_of_hasMatrix {δ δ' : Derivation ℂ P3 P3} {X : Matrix (Fin 3) (Fin 3) ℝ}
    (h : HasMatrix δ X) (h' : HasMatrix δ' X) : δ = δ' := by
  refine Derivation.ext_of_adjoin_eq_top _
    (Algebra.adjoin_adjoin_coe_preimage (R := ℂ)
      (s := Set.range fun ij : Fin 3 × Fin 3 => (OrthogonalFinitePolynomial.entry 3 ij : K3 → ℂ)))
    ?_
  rintro y ⟨⟨i, k⟩, hy⟩
  have hy' : y = entryP (i, k) := Subtype.ext hy.symm
  rw [hy', h, h']

theorem rotationGenerator_lie_one :
    (rotationGenerator 3 1 * rotationGenerator 3 0 - rotationGenerator 3 0 * rotationGenerator 3 1)
        * rotationGenerator 3 1 - rotationGenerator 3 1 *
        (rotationGenerator 3 1 * rotationGenerator 3 0 -
          rotationGenerator 3 0 * rotationGenerator 3 1) = rotationGenerator 3 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationGenerator, Matrix.mul_apply, Fin.sum_univ_three]

theorem rotationGenerator_lie_two :
    rotationGenerator 3 0 * (rotationGenerator 3 1 * rotationGenerator 3 0 -
        rotationGenerator 3 0 * rotationGenerator 3 1) -
      (rotationGenerator 3 1 * rotationGenerator 3 0 -
        rotationGenerator 3 0 * rotationGenerator 3 1) * rotationGenerator 3 0 =
      rotationGenerator 3 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationGenerator, Matrix.mul_apply, Fin.sum_univ_three]

/-! ### The commutation relations of the generators -/

/-- The inclusion of `RealKTypeCount.degreeLE 3 N` into the polynomial functions. -/
def incl : RealKTypeCount.degreeLE 3 N →ₗ[ℂ] P3 where
  toFun w := ⟨w, degreeLE_le_polynomialFunctions N w.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem incl_injective : Function.Injective (incl N) := fun _ _ h =>
  Subtype.ext (congrArg (fun z : P3 => (z : K3 → ℂ)) h)

theorem incl_gen {p : ℕ} (hp : p + 1 < 3) (w : RealKTypeCount.degreeLE 3 N) :
    incl N (gen N hp w) = der hp (incl N w) :=
  Subtype.ext (derFun_eq_gen N hp w).symm

theorem incl_commutator {A B : Module.End ℂ (RealKTypeCount.degreeLE 3 N)}
    {δ δ' : Derivation ℂ P3 P3} (hA : ∀ w, incl N (A w) = δ (incl N w))
    (hB : ∀ w, incl N (B w) = δ' (incl N w)) (w : RealKTypeCount.degreeLE 3 N) :
    incl N ((A * B - B * A) w) = ⁅δ, δ'⁆ (incl N w) := by
  simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, hA, hB,
    Derivation.commutator_apply]

theorem zero_add_one_lt_three : 0 + 1 < 3 := by norm_num

theorem one_add_one_lt_three : 1 + 1 < 3 := by norm_num

/-- With `g_p = gen N _` and `c = g_0 g_1 - g_1 g_0`: `g_1 c - c g_1 = g_0` and
`c g_0 - g_0 c = g_1`. -/
theorem gen_relations :
    gen N one_add_one_lt_three * (gen N zero_add_one_lt_three * gen N one_add_one_lt_three -
        gen N one_add_one_lt_three * gen N zero_add_one_lt_three) -
      (gen N zero_add_one_lt_three * gen N one_add_one_lt_three -
        gen N one_add_one_lt_three * gen N zero_add_one_lt_three) * gen N one_add_one_lt_three =
      gen N zero_add_one_lt_three ∧
    (gen N zero_add_one_lt_three * gen N one_add_one_lt_three -
        gen N one_add_one_lt_three * gen N zero_add_one_lt_three) * gen N zero_add_one_lt_three -
      gen N zero_add_one_lt_three * (gen N zero_add_one_lt_three * gen N one_add_one_lt_three -
        gen N one_add_one_lt_three * gen N zero_add_one_lt_three) =
      gen N one_add_one_lt_three := by
  have hC : HasMatrix ⁅der zero_add_one_lt_three, der one_add_one_lt_three⁆
      (rotationGenerator 3 1 * rotationGenerator 3 0 -
        rotationGenerator 3 0 * rotationGenerator 3 1) :=
    hasMatrix_lie (hasMatrix_der _) (hasMatrix_der _)
  have hcW := incl_commutator N (incl_gen N zero_add_one_lt_three)
    (incl_gen N one_add_one_lt_three)
  have e1 : ⁅der one_add_one_lt_three, ⁅der zero_add_one_lt_three, der one_add_one_lt_three⁆⁆ =
      der zero_add_one_lt_three := by
    have h := hasMatrix_lie (hasMatrix_der one_add_one_lt_three) hC
    rw [rotationGenerator_lie_one] at h
    exact eq_of_hasMatrix h (hasMatrix_der _)
  have e2 : ⁅⁅der zero_add_one_lt_three, der one_add_one_lt_three⁆, der zero_add_one_lt_three⁆ =
      der one_add_one_lt_three := by
    have h := hasMatrix_lie hC (hasMatrix_der zero_add_one_lt_three)
    rw [rotationGenerator_lie_two] at h
    exact eq_of_hasMatrix h (hasMatrix_der _)
  constructor
  · refine LinearMap.ext fun w => incl_injective N ?_
    rw [incl_commutator N (incl_gen N one_add_one_lt_three) hcW, e1, incl_gen]
  · refine LinearMap.ext fun w => incl_injective N ?_
    rw [incl_commutator N hcW (incl_gen N zero_add_one_lt_three), e2, incl_gen]

/-- The three commutation relations used by the `sl₂` argument, for `(p, q) = (0, 1)` or
`(1, 0)`. -/
theorem exists_relations {p q : ℕ} (hpq : p = 0 ∧ q = 1 ∨ p = 1 ∧ q = 0) (hp : p + 1 < 3)
    (hq : q + 1 < 3) :
    ∃ c : Module.End ℂ (RealKTypeCount.degreeLE 3 N),
      gen N hp * gen N hq - gen N hq * gen N hp = c ∧
      gen N hq * c - c * gen N hq = gen N hp ∧ c * gen N hp - gen N hp * c = gen N hq := by
  obtain ⟨r1, r2⟩ := gen_relations N
  rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨_, rfl, r1, r2⟩
  · exact ⟨_, rfl, relations_swap r1 r2⟩

/-! ### Left translation by `r_q(π)` -/

/-- Left translation by `r_q(π)` on `RealKTypeCount.degreeLE 3 N`. -/
def flipOp (q : ℕ) : Module.End ℂ (RealKTypeCount.degreeLE 3 N) where
  toFun w := ⟨fun x => (w : K3 → ℂ) (rot q Real.pi * x), left_mem_degreeLE w.2 _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rot_pi_mul_rot {p q : ℕ} (hpq : p = 0 ∧ q = 1 ∨ p = 1 ∧ q = 0) (θ : ℝ) :
    rot q Real.pi * rot p θ = rot p (-θ) * rot q Real.pi := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_mul, rot_val, rot_val, rot_val]
  ext i j
  rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [Matrix.mul_apply, Fin.sum_univ_three,
      blockRotation_apply (show 0 + 1 < 3 by norm_num),
      blockRotation_apply (show 1 + 1 < 3 by norm_num)]
    fin_cases i <;> fin_cases j <;> simp
  · simp only [Matrix.mul_apply, Fin.sum_univ_three,
      blockRotation_apply (show 0 + 1 < 3 by norm_num),
      blockRotation_apply (show 1 + 1 < 3 by norm_num)]
    fin_cases i <;> fin_cases j <;> simp

/-- `r_q(π)` reverses the `r_p`-modes. -/
theorem proj_flipOp {p q : ℕ} (hpq : p = 0 ∧ q = 1 ∨ p = 1 ∧ q = 0) (hp : p + 1 < 3) (m : ℤ)
    (w : RealKTypeCount.degreeLE 3 N) :
    proj N hp m (flipOp N q w) = flipOp N q (proj N hp (-m) w) := by
  apply Subtype.ext
  funext x
  show (2 * (Real.pi : ℂ))⁻¹ * coeff m (orb p (fun y => (w : K3 → ℂ) (rot q Real.pi * y)) x) =
    (2 * (Real.pi : ℂ))⁻¹ * coeff (-m) (orb p w (rot q Real.pi * x))
  have h : orb p (fun y => (w : K3 → ℂ) (rot q Real.pi * y)) x =
      fun θ => orb p w (rot q Real.pi * x) (-θ) := by
    funext θ
    show (w : K3 → ℂ) (rot q Real.pi * (rot p θ * x)) =
      (w : K3 → ℂ) (rot p (-θ) * (rot q Real.pi * x))
    rw [← mul_assoc, rot_pi_mul_rot hpq, mul_assoc]
  rw [h, coeff_comp_neg (periodic_orb hp _ _)]

theorem expMode_pi (j : ℤ) : expMode j Real.pi = (-1 : ℂ) ^ j := by
  rw [expMode, show (j : ℂ) * (Real.pi : ℂ) * I = j * (Real.pi * I) by ring, Complex.exp_int_mul,
    Complex.exp_pi_mul_I]

/-- `r_q(π)` multiplies the `r_q`-mode `j` by `(-1)^j`. -/
theorem proj_flipOp_self {q : ℕ} (hq : q + 1 < 3) (j : ℤ) (w : RealKTypeCount.degreeLE 3 N) :
    proj N hq j (flipOp N q w) = ((-1 : ℂ) ^ j) • proj N hq j w := by
  apply Subtype.ext
  funext x
  show projFun q j (fun y => (w : K3 → ℂ) (rot q Real.pi * y)) x =
    (-1 : ℂ) ^ j * projFun q j w x
  have h : projFun q j (fun y => (w : K3 → ℂ) (rot q Real.pi * y)) x =
      projFun q j w (rot q Real.pi * x) := by
    simp only [projFun]
    congr 2
    funext θ
    show (w : K3 → ℂ) (rot q Real.pi * (rot q θ * x)) =
      (w : K3 → ℂ) (rot q θ * (rot q Real.pi * x))
    rw [← mul_assoc, ← mul_assoc, ← rot_add, ← rot_add, add_comm]
  rw [h, projFun_rot_mul hq, expMode_pi]

end Analytic

open RealKTypeCount RealBlockFourierFinite in
/-- **Uncertainty principle for two block rotations of `O(3)`.** -/
theorem realOrthogonalBlockUncertainty : RealOrthogonalBlockUncertaintyStatement := by
  intro p q n n' f hpq hnn hf hK h1 h2 g hg
  have hp : p + 1 < 3 := by rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  have hq : q + 1 < 3 := by rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  -- the restriction of `f` to `O(3)` is a polynomial function
  have hfK : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ 3 =>
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 3 ℝ)
        (k : Langlands.GeneralLinear 3 ℝ) f)) := hK
  have hle : OrthogonalFinitePolynomial.translateSpan (restrictLinear 3 f) ≤
      (Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ 3 =>
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 3 ℝ)
          (k : Langlands.GeneralLinear 3 ℝ) f)).map (restrictLinear 3) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨⟨Unitary.toUnits k, k.2⟩, rfl⟩, ?_⟩
    funext x
    show f (Unitary.toUnits x * Unitary.toUnits k) = f (Unitary.toUnits (x * k))
    rw [map_mul]
  have : FiniteDimensional ℂ (OrthogonalFinitePolynomial.translateSpan (restrictLinear 3 f)) :=
    Submodule.finiteDimensional_of_le hle
  obtain ⟨N, hN⟩ := exists_mem_degreeLE (φ := restrictLinear 3 f)
    (OrthogonalFinitePolynomial.mem_polynomialFunctions_of_finiteDimensional
      (hf.comp continuous_unitary_toUnits))
  set v : RealKTypeCount.degreeLE 3 N := ⟨restrictLinear 3 f, hN⟩ with hv
  -- the modes of `v` are block Fourier coefficients of `f`
  have hmode : ∀ {r : ℕ} (hr : r + 1 < 3) (m : ℤ),
      (∀ x : Matrix.unitaryGroup (Fin 3) ℝ,
        blockFourierCoefficient 3 r m f (Unitary.toUnits x) = 0) →
      proj N hr m v = 0 := by
    intro r hr m hm
    apply Subtype.ext
    funext x
    rw [proj_coe]
    show (2 * (Real.pi : ℂ))⁻¹ * coeff m (orb r (restrictLinear 3 f) x) = 0
    have e : orb r (restrictLinear 3 f) x =
        fun θ => f (blockRotation 3 r θ * Unitary.toUnits x) := by
      funext θ
      rw [orb, restrictLinear_apply, toUnits_rot_mul]
    rw [e, ← blockFourierCoefficient_eq_coeff, hm x, mul_zero]
  have hv0 : v = 0 := by
    obtain ⟨c, hab, hbc, hca⟩ := exists_relations N hpq hp hq
    refine eq_zero_of_parity hab hbc hca (isModeDecomposition N hp) (isModeDecomposition N hq)
      (flipOp N q) (proj_flipOp N hpq hp) (proj_flipOp_self N hq) hnn ?_ ?_
    · intro m hm
      exact hmode hp m fun x => h1 (Unitary.toUnits x) x.2 m hm
    · intro j hj
      exact hmode hq j fun x => h2 (Unitary.toUnits x) x.2 j hj
  have h := congrFun (congrArg Subtype.val hv0) ⟨(g : Matrix (Fin 3) (Fin 3) ℝ), hg⟩
  rw [hv] at h
  simpa [restrictLinear_apply, toUnits_mk hg] using h

end RealOrthogonalUncertainty

end Langlands.Archimedean
