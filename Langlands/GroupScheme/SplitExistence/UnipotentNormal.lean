import Langlands.GroupScheme.SplitExistence.Centralizer
import Langlands.GroupScheme.SplitExistence.Opposite

/-! # Normal subgroups of unipotent matrices in `Γ(K)` are trivial

Let `K` be an infinite field and `N ≤ Γ(K)` a subgroup normalized by `Γ(K)` all of whose elements
`u` satisfy `(u - 1)ⁿ = 0`. Then `N = 1`.

* `N·B` is a subgroup between `B` and `Γ = B ⊔ N(T)`. If it contained a Weyl element `n_i`, write
  `n_i = b u` with `u ∈ N`; for every torus element `t` the commutator `u t u⁻¹ t⁻¹` lies in
  `N ∩ B`, and its diagonal is `s_i(t) t⁻¹`. Unipotence forces `s_i(t) = t` for all `t`, which
  fails for `t = α_i^∨(c)` with `c⁴ ≠ 1`. So by parabolic rigidity (`IsConcreteTits.eq_of_le`)
  `N·B = B`, i.e. `N ≤ B`.
* The same argument for the opposite data gives `N ≤ B⁻`. Matrices in `B ∩ B⁻` are block
  diagonal for the `ℓ`-grading, so `N ≤ T(K)`, and unipotent diagonal matrices are `1`. -/

noncomputable section

universe u

open Matrix

namespace Langlands.GroupScheme.SplitExistence

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  (D : ChevalleyData P b) {K : Type u} [Field K]

/-- Nonzero entries `(c, d)` are diagonal or have `ℓ(wt d) < ℓ(wt c)`. -/
def IsBT (M : Matrix (Fin D.n) (Fin D.n) K) : Prop :=
  ∀ c d, M c d ≠ 0 → c = d ∨ D.ℓ (D.wt d) < D.ℓ (D.wt c)

variable {D}

theorem IsBT.mul {M M' : Matrix (Fin D.n) (Fin D.n) K} (hM : D.IsBT M) (hM' : D.IsBT M') :
    D.IsBT (M * M') := by
  intro c d h
  rw [Matrix.mul_apply] at h
  obtain ⟨e, -, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h1 := hM c e (left_ne_zero_of_mul he)
  have h2 := hM' e d (right_ne_zero_of_mul he)
  rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
  · exact Or.inl rfl
  · exact Or.inr h2
  · exact Or.inr h1
  · exact Or.inr (h2.trans h1)

theorem IsBT.mul_apply_self {M M' : Matrix (Fin D.n) (Fin D.n) K} (hM : D.IsBT M)
    (hM' : D.IsBT M') (c : Fin D.n) : (M * M') c c = M c c * M' c c := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single c (fun e _ hec => ?_) (fun h => absurd (Finset.mem_univ c) h)
  by_contra h
  have h1 := hM c e (left_ne_zero_of_mul h)
  have h2 := hM' e c (right_ne_zero_of_mul h)
  rcases h1 with rfl | h1
  · exact hec rfl
  rcases h2 with rfl | h2
  · exact hec rfl
  · exact lt_asymm h1 h2

theorem isBT_one : D.IsBT (1 : Matrix (Fin D.n) (Fin D.n) K) := by
  intro c d h
  by_contra hcd
  push Not at hcd
  exact h (Matrix.one_apply_ne hcd.1)

theorem IsBT.sub_one {M : Matrix (Fin D.n) (Fin D.n) K} (hM : D.IsBT M) : D.IsBT (M - 1) := by
  intro c d h
  by_cases hcd : c = d
  · exact Or.inl hcd
  · rw [Matrix.sub_apply, Matrix.one_apply_ne hcd, sub_zero] at h
    exact hM c d h

theorem IsBT.pow {M : Matrix (Fin D.n) (Fin D.n) K} (hM : D.IsBT M) (m : ℕ) : D.IsBT (M ^ m) := by
  induction m with
  | zero => rw [pow_zero]; exact isBT_one
  | succ m ih => rw [pow_succ]; exact ih.mul hM

theorem IsBT.pow_apply_self {M : Matrix (Fin D.n) (Fin D.n) K} (hM : D.IsBT M) (m : ℕ)
    (c : Fin D.n) : (M ^ m) c c = M c c ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, (hM.pow m).mul_apply_self hM, ih, pow_succ]

/-- A matrix with the `B`-shape and `(M - 1)ⁿ = 0` has all diagonal entries `1`. -/
theorem IsBT.apply_self_eq_one {M : Matrix (Fin D.n) (Fin D.n) K} (hM : D.IsBT M)
    (hu : (M - 1) ^ D.n = 0) (c : Fin D.n) : M c c = 1 := by
  have h := hM.sub_one.pow_apply_self D.n c
  rw [hu, Matrix.zero_apply, Matrix.sub_apply, Matrix.one_apply_eq] at h
  exact (sub_eq_zero.1 (pow_eq_zero_iff (n := D.n) (Fin.pos c).ne' |>.1 h.symm))

theorem isBT_of_mem_borelSub {g : GL (Fin D.n) K} (hg : g ∈ D.borelSub K) :
    D.IsBT (g : Matrix (Fin D.n) (Fin D.n) K) := by
  obtain ⟨t, ⟨χ, rfl⟩, v, hv, rfl⟩ := mem_borelSub.1 hg
  have hut : D.IsUT (v : Matrix (Fin D.n) (Fin D.n) K) := D.posSub_le_utSub hv
  intro c d h
  rw [Units.val_mul, coe_torusHom, Matrix.diagonal_mul] at h
  rcases hut c d (right_ne_zero_of_mul h) with ⟨rfl, -⟩ | h'
  · exact Or.inl rfl
  · exact Or.inr h'

/-- In an infinite field some unit has `t⁴ ≠ 1`. -/
theorem exists_units_pow_four_ne_one [Infinite K] : ∃ t : Kˣ, t ^ 4 ≠ 1 := by
  classical
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (insert (0 : K) (Polynomial.nthRoots 4 (1 : K)).toFinset)
  rw [Finset.mem_insert, not_or, Multiset.mem_toFinset, Polynomial.mem_nthRoots (by norm_num)] at hx
  refine ⟨Units.mk0 x hx.1, fun h => hx.2 ?_⟩
  have := congrArg Units.val h
  simpa using this

variable [Finite J] [P.IsReduced]

/-- A subgroup of unipotent matrices normalized by `Γ(K)` lies in `B(K)`. -/
theorem le_borelSub_of_unipotent [Infinite K] (N : Subgroup (GL (Fin D.n) K))
    (hN : N ≤ D.chevSub K) (hnorm : D.chevSub K ≤ Subgroup.normalizer (N : Set (GL (Fin D.n) K)))
    (hu : ∀ g ∈ N, ((g : Matrix (Fin D.n) (Fin D.n) K) - 1) ^ D.n = 0) :
    N ≤ D.borelSub K := by
  have hBn : D.borelSub K ≤ Subgroup.normalizer (N : Set (GL (Fin D.n) K)) :=
    D.borelSub_le_chevSub.trans hnorm
  have hP := (D.isConcreteTits (K := K)).eq_of_le (D.borelSub K ⊔ N) le_sup_left
    (sup_le le_sup_left (hN.trans D.chevSub_le_sup)) (fun i hi => ?_)
  · exact le_sup_right.trans hP.le
  -- a Weyl element in `B·N` gives a contradiction
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hBn] at hi
  obtain ⟨b', hb', u, hu', hbu⟩ := Set.mem_mul.1 hi
  have hsym : ∀ χ : Multiplicative X →* Kˣ, reflectChar (P := P) (i : J) χ = χ := by
    intro χ
    apply D.torusHom_injective
    set t := D.torusHom χ
    have htΓ : t ∈ D.chevSub K := le_sup_left (α := Subgroup (GL (Fin D.n) K)) ⟨χ, rfl⟩
    have hw : u * t * u⁻¹ * t⁻¹ ∈ N := by
      have h1 : t * u⁻¹ * t⁻¹ ∈ N := ((Subgroup.mem_normalizer_iff.1 (hnorm htΓ)) _).1
        (N.inv_mem hu')
      rw [mul_assoc, mul_assoc]
      rw [mul_assoc] at h1
      exact N.mul_mem hu' h1
    have hueq : u = b'⁻¹ * D.wn (K := K) i := by rw [← hbu, inv_mul_cancel_left]
    have hconj : D.wn (K := K) i * t * (D.wn (K := K) i)⁻¹ =
        D.torusHom (reflectChar (P := P) (i : J) χ) := by
      rw [D.wn_mul_torusHom, mul_inv_cancel_right]
    have hweq : u * t * u⁻¹ * t⁻¹ =
        b'⁻¹ * D.torusHom (reflectChar (P := P) (i : J) χ) * b' * t⁻¹ := by
      rw [hueq, ← hconj]
      group
    have hbB : D.IsBT (b' : Matrix (Fin D.n) (Fin D.n) K) := isBT_of_mem_borelSub hb'
    have hbB' : D.IsBT ((b'⁻¹ : GL (Fin D.n) K) : Matrix (Fin D.n) (Fin D.n) K) :=
      isBT_of_mem_borelSub ((D.borelSub K).inv_mem hb')
    have htB : ∀ ψ : Multiplicative X →* Kˣ,
        D.IsBT ((D.torusHom ψ : GL (Fin D.n) K) : Matrix (Fin D.n) (Fin D.n) K) := fun ψ =>
      isBT_of_mem_borelSub (D.torusSub_le_borelSub ⟨ψ, rfl⟩)
    have htB' : D.IsBT ((t⁻¹ : GL (Fin D.n) K) : Matrix (Fin D.n) (Fin D.n) K) := by
      rw [← map_inv]
      exact htB _
    have hwB : D.IsBT (((u * t * u⁻¹ * t⁻¹ : GL (Fin D.n) K)) : Matrix (Fin D.n) (Fin D.n) K) := by
      rw [hweq]
      simp only [Units.val_mul]
      exact ((hbB'.mul (htB _)).mul hbB).mul htB'
    have hdiag := hwB.apply_self_eq_one (hu _ hw)
    have hbb : ∀ c, ((b'⁻¹ : GL (Fin D.n) K) : Matrix (Fin D.n) (Fin D.n) K) c c *
        (b' : Matrix (Fin D.n) (Fin D.n) K) c c = 1 := by
      intro c
      rw [← hbB'.mul_apply_self hbB, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_apply_eq]
    apply Units.ext
    ext c d
    by_cases hcd : c = d
    · subst hcd
      have h := hdiag c
      rw [hweq] at h
      simp only [Units.val_mul] at h
      rw [((hbB'.mul (htB _)).mul hbB).mul_apply_self htB', (hbB'.mul (htB _)).mul_apply_self hbB,
        hbB'.mul_apply_self (htB _)] at h
      rw [← map_inv, coe_torusHom, coe_torusHom, Matrix.diagonal_apply_eq,
        Matrix.diagonal_apply_eq] at h
      rw [coe_torusHom, coe_torusHom, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
      have h' : ((b'⁻¹ : GL (Fin D.n) K) : Matrix (Fin D.n) (Fin D.n) K) c c *
          (b' : Matrix (Fin D.n) (Fin D.n) K) c c *
          (((reflectChar (P := P) (i : J) χ) (Multiplicative.ofAdd (D.wt c)) : Kˣ) : K) *
          ((χ⁻¹ (Multiplicative.ofAdd (D.wt c)) : Kˣ) : K) = 1 := by
        rw [← h]
        ring
      rw [hbb, one_mul, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
        mul_inv_eq_one₀ (Units.ne_zero _)] at h'
      exact h'
    · rw [coe_torusHom, coe_torusHom, Matrix.diagonal_apply_ne _ hcd,
        Matrix.diagonal_apply_ne _ hcd]
  obtain ⟨t, ht⟩ := exists_units_pow_four_ne_one (K := K)
  apply ht
  have h := congrArg (fun χ : Multiplicative X →* Kˣ => χ (Multiplicative.ofAdd (P.root i)))
    (hsym (corootChar (P := P) (i : J) t))
  simp only [reflectChar, corootChar, MonoidHom.coe_comp, MonoidHom.coe_mk, OneHom.coe_mk,
    Function.comp_apply, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd] at h
  have h2 : (P.toLinearMap (P.root i)) (P.coroot i) = 2 := P.root_coroot_two i
  have hr : (↑(P.reflection (i : J)) : X →ₗ[ℤ] X).toAddMonoidHom (P.root i) = -P.root i :=
    P.reflection_apply_self _
  rw [hr, map_neg, LinearMap.neg_apply, h2] at h
  rw [← zpow_natCast, show ((4 : ℕ) : ℤ) = 2 - (-2) by norm_num, _root_.zpow_sub, ← h, mul_inv_cancel]

/-- **A subgroup of unipotent matrices normalized by `Γ(K)` is trivial.** -/
theorem eq_bot_of_unipotent [Infinite K] (N : Subgroup (GL (Fin D.n) K))
    (hN : N ≤ D.chevSub K) (hnorm : D.chevSub K ≤ Subgroup.normalizer (N : Set (GL (Fin D.n) K)))
    (hu : ∀ g ∈ N, ((g : Matrix (Fin D.n) (Fin D.n) K) - 1) ^ D.n = 0) :
    N = ⊥ := by
  have h1 := le_borelSub_of_unipotent N hN hnorm hu
  have h2 := le_borelSub_of_unipotent (D := D.neg) N hN hnorm hu
  rw [eq_bot_iff]
  intro g hg
  have hT : g ∈ D.torusSub K := by
    refine D.mem_torusSub_of_blockLevi (hN hg) fun c d hcd => ?_
    rcases lt_or_gt_of_ne hcd with h | h
    · exact (D.borelSub_le_btSub (h1 hg)) (OrderDual.toDual_lt_toDual.mpr h)
    · have h' : -D.ℓ (D.wt c) < -D.ℓ (D.wt d) := by omega
      exact (D.neg.borelSub_le_btSub (h2 hg)) (OrderDual.toDual_lt_toDual.mpr h')
  have hd := (isBT_of_mem_borelSub (h1 hg)).apply_self_eq_one (hu _ hg)
  obtain ⟨χ, rfl⟩ := hT
  rw [Subgroup.mem_bot]
  apply Units.ext
  ext c d
  by_cases hcd : c = d
  · subst hcd
    rw [hd c, Units.val_one, Matrix.one_apply_eq]
  · rw [coe_torusHom, Matrix.diagonal_apply_ne _ hcd, Units.val_one, Matrix.one_apply_ne hcd]

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
