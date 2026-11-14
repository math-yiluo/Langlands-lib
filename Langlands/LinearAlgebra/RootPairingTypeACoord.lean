import Mathlib.LinearAlgebra.RootSystem.WeylGroup
import Mathlib.GroupTheory.Perm.Sign

/-! # Weight coordinates of integral type `A` root pairings

A *type `A_n` coordinate system* on an integral root pairing consists of weights
`ε 0, …, ε n` spanning the weight lattice, with the single relation
`ε 0 + ⋯ + ε n = 0`, such that the roots are exactly the differences
`ε a - ε b` with `a ≠ b` and the coroot of `ε a - ε b` pairs with `ε y` as
`[y = a] - [y = b]`.  This is the character lattice of the diagonal torus of
`SL_{n+1}` with its roots.

The main result `mem_weylGroup_or_exists_neg` shows that every automorphism of
such a root pairing is a Weyl group element or the negative of one.
-/

namespace Langlands.LinearAlgebra.RootPairingTypeA

open RootPairing

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- Type `A_n` weight coordinates on an integral root pairing. -/
structure TypeACoord (P : RootPairing ι ℤ M N) (n : ℕ) where
  /-- The coordinate weights. -/
  ε : Fin (n + 1) → M
  /-- The coordinate weights span the weight lattice. -/
  exists_eq_sum : ∀ x : M, ∃ c : Fin (n + 1) → ℤ, x = ∑ y, c y • ε y
  /-- The coordinate weights sum to zero. -/
  sum_eq_zero : ∑ y, ε y = 0
  /-- The only linear relations are multiples of the sum relation. -/
  eq_of_sum_eq_zero : ∀ c : Fin (n + 1) → ℤ, ∑ y, c y • ε y = 0 → ∀ y z, c y = c z
  /-- Every root is a difference of two distinct coordinate weights. -/
  exists_root_eq : ∀ j, ∃ a b, a ≠ b ∧ P.root j = ε a - ε b
  /-- Every difference of two distinct coordinate weights is a root. -/
  exists_eq_root : ∀ a b, a ≠ b → ∃ j, P.root j = ε a - ε b
  /-- The coroot of `ε a - ε b` evaluates on the coordinate weights as
  `[y = a] - [y = b]`. -/
  coroot'_apply : ∀ j a b, P.root j = ε a - ε b → ∀ y,
    P.coroot' j (ε y) = (if y = a then 1 else 0) - (if y = b then 1 else 0)

namespace TypeACoord

variable {P : RootPairing ι ℤ M N} {n : ℕ} (C : TypeACoord P n)

theorem coroot'_sum {j : ι} {a b : Fin (n + 1)} (h : P.root j = C.ε a - C.ε b)
    (c : Fin (n + 1) → ℤ) : P.coroot' j (∑ y, c y • C.ε y) = c a - c b := by
  classical
  simp only [map_sum, map_smul, C.coroot'_apply j a b h, smul_eq_mul, mul_sub, mul_ite,
    mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

theorem coroot'_sub {j : ι} {p q : Fin (n + 1)} (h : P.root j = C.ε p - C.ε q)
    (a b : Fin (n + 1)) :
    P.coroot' j (C.ε a - C.ε b) =
      ((if a = p then 1 else 0) - (if a = q then 1 else 0)) -
        ((if b = p then 1 else 0) - (if b = q then 1 else 0)) := by
  rw [map_sub, C.coroot'_apply j p q h, C.coroot'_apply j p q h]

theorem ε_injective : Function.Injective C.ε := by
  intro a b h
  by_contra hab
  obtain ⟨j, hj⟩ := C.exists_eq_root a b hab
  rw [h, sub_self] at hj
  exact P.ne_zero j hj

theorem ε_ne_zero (hn : 1 ≤ n) (a : Fin (n + 1)) : C.ε a ≠ 0 := by
  classical
  intro h
  obtain ⟨b, hb⟩ : ∃ b : Fin (n + 1), b ≠ a := by
    by_cases ha : a = 0
    · exact ⟨Fin.last n, by
        rw [ha]; intro h0; exact absurd (congrArg Fin.val h0) (by simp; omega)⟩
    · exact ⟨0, Ne.symm ha⟩
  have hsum : ∑ y, (if y = a then (1 : ℤ) else 0) • C.ε y = 0 := by
    simp [h]
  have := C.eq_of_sum_eq_zero _ hsum a b
  simp [hb] at this

/-- Linear maps out of the weight lattice are determined by the coordinate
weights. -/
theorem linearMap_ext {M' : Type*} [AddCommGroup M'] {f g : M →ₗ[ℤ] M'}
    (h : ∀ y, f (C.ε y) = g (C.ε y)) : f = g := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨c, rfl⟩ := C.exists_eq_sum x
  simp only [map_sum, map_smul, h]

/-- Pairings with coordinate weights lie in `{-1, 0, 1}`. -/
theorem coroot'_ε_bounds (j : ι) (a : Fin (n + 1)) :
    -1 ≤ P.coroot' j (C.ε a) ∧ P.coroot' j (C.ε a) ≤ 1 := by
  obtain ⟨p, q, hpq, h⟩ := C.exists_root_eq j
  rw [C.coroot'_apply j p q h]
  constructor <;> split_ifs <;> omega

theorem eq_of_coroot'_ε_eq_one {j : ι} {a : Fin (n + 1)} (h1 : P.coroot' j (C.ε a) = 1) :
    ∃ q, q ≠ a ∧ P.root j = C.ε a - C.ε q := by
  obtain ⟨p, q, hpq, h⟩ := C.exists_root_eq j
  rw [C.coroot'_apply j p q h] at h1
  by_cases hap : a = p
  · subst hap
    refine ⟨q, Ne.symm hpq, h⟩
  · simp only [hap, ite_false] at h1
    split_ifs at h1 <;> omega

/-- The image of a coordinate weight under an automorphism is plus or minus a
coordinate weight. -/
theorem exists_weightEquiv_ε_eq (hn : 1 ≤ n) (δ : P.Aut) (a : Fin (n + 1)) :
    ∃ y, δ.weightEquiv (C.ε a) = C.ε y ∨ δ.weightEquiv (C.ε a) = -C.ε y := by
  classical
  obtain ⟨c, hc⟩ := C.exists_eq_sum (δ.weightEquiv (C.ε a))
  have hpair : ∀ i : ι, ∀ y z, P.root (δ.indexEquiv i) = C.ε y - C.ε z →
      c y - c z = P.coroot' i (C.ε a) := by
    intro i y z h
    rw [← C.coroot'_sum h c, ← hc, δ.coroot'_weightEquiv]
  have hroot : ∀ y z, y ≠ z → ∃ i, P.root (δ.indexEquiv i) = C.ε y - C.ε z := by
    intro y z hyz
    obtain ⟨i', hi'⟩ := C.exists_eq_root y z hyz
    exact ⟨δ.indexEquiv.symm i', by rw [Equiv.apply_symm_apply, hi']⟩
  have hdiff : ∀ y z, c y - c z ≤ 1 := by
    intro y z
    by_cases hyz : y = z
    · subst hyz; simp
    obtain ⟨i, hi⟩ := hroot y z hyz
    rw [hpair i y z hi]
    exact (C.coroot'_ε_bounds i a).2
  obtain ⟨z0, -, hz0⟩ := Finset.exists_min_image Finset.univ c Finset.univ_nonempty
  obtain ⟨y0, -, hy0⟩ := Finset.exists_max_image Finset.univ c Finset.univ_nonempty
  have hz0' : ∀ y, c z0 ≤ c y := fun y => hz0 y (Finset.mem_univ y)
  have hy0' : ∀ y, c y ≤ c y0 := fun y => hy0 y (Finset.mem_univ y)
  -- `c` is not constant
  have htop : c y0 = c z0 + 1 := by
    have h1 := hdiff y0 z0
    have h2 := hz0' y0
    by_contra hne
    have hconst : ∀ y, c y = c z0 := fun y => le_antisymm (by
      have := hy0' y; omega) (hz0' y)
    apply C.ε_ne_zero hn a
    apply δ.weightEquiv.injective
    rw [hc, map_zero]
    calc ∑ y, c y • C.ε y = ∑ y, c z0 • C.ε y :=
          Finset.sum_congr rfl fun y _ => by rw [hconst y]
      _ = 0 := by rw [← Finset.smul_sum, C.sum_eq_zero, smul_zero]
  have hval : ∀ y, c y = c z0 ∨ c y = c z0 + 1 := by
    intro y
    have := hz0' y
    have := hy0' y
    omega
  by_cases h2top : ∃ y1 y2, y1 ≠ y2 ∧ c y1 = c z0 + 1 ∧ c y2 = c z0 + 1
  · by_cases h2bot : ∃ z1 z2, z1 ≠ z2 ∧ c z1 = c z0 ∧ c z2 = c z0
    · exfalso
      obtain ⟨y1, y2, hy12, hy1, hy2⟩ := h2top
      obtain ⟨z1, z2, hz12, hz1, hz2⟩ := h2bot
      have hne : ∀ y z, c y = c z0 + 1 → c z = c z0 → y ≠ z := by
        rintro y z hy hz rfl; omega
      obtain ⟨i1, hi1⟩ := hroot y1 z1 (hne y1 z1 hy1 hz1)
      obtain ⟨i2, hi2⟩ := hroot y2 z2 (hne y2 z2 hy2 hz2)
      have h1 : P.coroot' i1 (C.ε a) = 1 := by rw [← hpair i1 y1 z1 hi1]; omega
      have h2 : P.coroot' i2 (C.ε a) = 1 := by rw [← hpair i2 y2 z2 hi2]; omega
      obtain ⟨q1, hq1, hr1⟩ := C.eq_of_coroot'_ε_eq_one h1
      obtain ⟨q2, hq2, hr2⟩ := C.eq_of_coroot'_ε_eq_one h2
      have hpairing := δ.toHom.pairing (i := i1) (j := i2)
      rw [← root_coroot'_eq_pairing, ← root_coroot'_eq_pairing, hi1, hr1,
        C.coroot'_sub hi2, C.coroot'_sub hr2] at hpairing
      have hy1z2 := hne y1 z2 hy1 hz2
      have hz1y2 := Ne.symm (hne y2 z1 hy2 hz1)
      simp only [hy12, hy1z2, hz1y2, hz12, ite_false, ite_true] at hpairing
      split_ifs at hpairing <;> omega
    · push Not at h2bot
      refine ⟨z0, Or.inr ?_⟩
      have hcy : ∀ y, c y = (c z0 + 1) - if y = z0 then 1 else 0 := by
        intro y
        split_ifs with h
        · subst h; ring
        · rcases hval y with hy | hy
          · exact absurd hy (by intro hy'; exact h (h2bot y z0 h hy' rfl).elim)
          · rw [hy]; ring
      rw [hc]
      calc ∑ y, c y • C.ε y =
            ∑ y, ((c z0 + 1) • C.ε y - if y = z0 then C.ε y else 0) :=
            Finset.sum_congr rfl fun y _ => by
              rw [hcy y]; split_ifs <;> simp [add_smul]
        _ = -C.ε z0 := by
          rw [Finset.sum_sub_distrib, ← Finset.smul_sum, C.sum_eq_zero, smul_zero,
            Finset.sum_ite_eq']
          simp
  · push Not at h2top
    refine ⟨y0, Or.inl ?_⟩
    have hcy : ∀ y, c y = c z0 + if y = y0 then 1 else 0 := by
      intro y
      split_ifs with h
      · subst h; exact htop
      · rcases hval y with hy | hy
        · rw [hy]; ring
        · exact absurd (h2top y y0 h hy htop) (by simp)
    rw [hc]
    calc ∑ y, c y • C.ε y = ∑ y, (c z0 • C.ε y + if y = y0 then C.ε y else 0) :=
          Finset.sum_congr rfl fun y _ => by
            rw [hcy y]; split_ifs <;> simp [add_smul]
      _ = C.ε y0 := by
        rw [Finset.sum_add_distrib, ← Finset.smul_sum, C.sum_eq_zero, smul_zero,
          Finset.sum_ite_eq']
        simp

/-- For `n ≥ 2`, a sum of two coordinate weights is never a difference of two
coordinate weights. -/
theorem ε_add_ε_ne (hn : 2 ≤ n) (y z p q : Fin (n + 1)) :
    C.ε y + C.ε z ≠ C.ε p - C.ε q := by
  classical
  intro h
  set d : Fin (n + 1) → ℤ := fun w => (if w = y then 1 else 0) + (if w = z then 1 else 0) +
    (if w = q then 1 else 0) - (if w = p then 1 else 0) with hd_def
  have hd : ∑ w, d w • C.ε w = 0 := by
    simp only [hd_def, sub_smul, add_smul, ite_smul, one_smul, zero_smul,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    rw [h]
    abel
  have hconst := C.eq_of_sum_eq_zero d hd
  have hsum : ∑ w, d w = 2 := by
    simp only [hd_def, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    norm_num
  have hsum' : ∑ w, d w = (n + 1 : ℤ) * d 0 := by
    rw [Finset.sum_congr rfl fun w _ => hconst w 0]
    simp
  rw [hsum'] at hsum
  have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
  rcases le_or_gt (d 0) 0 with h0 | h0 <;> nlinarith

/-- Every automorphism permutes the coordinate weights up to a uniform sign. -/
theorem exists_perm (δ : P.Aut) : ∃ σ : Fin (n + 1) → Fin (n + 1),
    (∀ a, δ.weightEquiv (C.ε a) = C.ε (σ a)) ∨ (∀ a, δ.weightEquiv (C.ε a) = -C.ε (σ a)) := by
  classical
  rcases Nat.lt_or_ge n 1 with hn | hn
  · obtain rfl : n = 0 := by omega
    refine ⟨id, Or.inl fun a => ?_⟩
    have h0 : C.ε a = 0 := by
      have := C.sum_eq_zero
      rwa [Fin.sum_univ_one, ← Fin.fin_one_eq_zero a] at this
    simp [h0]
  choose σ hσ using C.exists_weightEquiv_ε_eq hn δ
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · obtain rfl : n = 1 := by omega
    have hneg : ∀ y : Fin 2, ∃ z, -C.ε y = C.ε z := by
      have h := C.sum_eq_zero
      rw [Fin.sum_univ_two] at h
      intro y
      fin_cases y
      · exact ⟨1, by rw [neg_eq_iff_add_eq_zero]; exact h⟩
      · exact ⟨0, by rw [neg_eq_iff_add_eq_zero, add_comm]; exact h⟩
    choose τ hτ using hneg
    refine ⟨fun a => if δ.weightEquiv (C.ε a) = C.ε (σ a) then σ a else τ (σ a),
      Or.inl fun a => ?_⟩
    dsimp only
    split_ifs with h
    · exact h
    · rw [← hτ]; exact (hσ a).resolve_left h
  · by_cases hpos : ∀ a, δ.weightEquiv (C.ε a) = C.ε (σ a)
    · exact ⟨σ, Or.inl hpos⟩
    by_cases hneg : ∀ a, δ.weightEquiv (C.ε a) = -C.ε (σ a)
    · exact ⟨σ, Or.inr hneg⟩
    exfalso
    push Not at hpos hneg
    obtain ⟨b, hb⟩ := hpos
    obtain ⟨a, ha⟩ := hneg
    have hb' := (hσ b).resolve_left hb
    have ha' := (hσ a).resolve_right ha
    by_cases hab : a = b
    · subst hab
      apply C.ε_add_ε_ne hn2 (σ a) (σ a) a a
      rw [sub_self]
      rw [ha', eq_neg_iff_add_eq_zero] at hb'
      exact hb'
    · obtain ⟨j, hj⟩ := C.exists_eq_root a b hab
      obtain ⟨p, q, -, hpq⟩ := C.exists_root_eq (δ.indexEquiv j)
      apply C.ε_add_ε_ne hn2 (σ a) (σ b) p q
      rw [← hpq, ← δ.root_weightMap_apply P P j, ← δ.weightEquiv_apply, hj, map_sub, ha', hb',
        sub_neg_eq_add]

/-- Every permutation of the coordinate weights is realized by the Weyl
group. -/
theorem exists_weyl_perm (π : Equiv.Perm (Fin (n + 1))) :
    ∃ w ∈ P.weylGroup, ∀ y, w.weightEquiv (C.ε y) = C.ε (π y) := by
  classical
  induction π using Equiv.Perm.swap_induction_on with
  | one => exact ⟨1, one_mem _, fun y => by simp⟩
  | swap_mul f x y hxy ih =>
    obtain ⟨w, hw, hwf⟩ := ih
    obtain ⟨j, hj⟩ := C.exists_eq_root x y hxy
    refine ⟨Equiv.reflection P j * w, mul_mem (P.reflection_mem_weylGroup j) hw, fun z => ?_⟩
    change (Equiv.reflection P j * w) • C.ε z = _
    rw [mul_smul]
    change Equiv.reflection P j • w.weightEquiv (C.ε z) = _
    rw [hwf, Equiv.reflection_smul, reflection_apply, C.coroot'_apply j x y hj, hj,
      Equiv.Perm.mul_apply]
    generalize f z = u
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2 h2
    · exact absurd (h1.symm.trans h2) hxy
    · subst h1; simp
    · subst h2; simp
    · simp

include C in
/-- **Automorphisms of type `A` root pairings.** Every automorphism of an
integral root pairing with type `A_n` coordinates is either a Weyl group
element or acts on weights as the negative of one. -/
theorem mem_weylGroup_or_exists_neg (δ : P.Aut) :
    δ ∈ P.weylGroup ∨ ∃ w ∈ P.weylGroup, ∀ x, w.weightEquiv x = -δ.weightEquiv x := by
  obtain ⟨σ, hσ⟩ := C.exists_perm δ
  have hinj : Function.Injective σ := by
    intro a b hab
    apply C.ε_injective
    apply δ.weightEquiv.injective
    rcases hσ with h | h <;> rw [h, h, hab]
  let π := Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hinj)
  obtain ⟨w, hw, hwε⟩ := C.exists_weyl_perm π
  rcases hσ with h | h
  · left
    have hwδ : w = δ := by
      apply RootPairing.Equiv.weightHom_injective P
      apply LinearEquiv.toLinearMap_injective
      apply C.linearMap_ext
      intro y
      change w.weightEquiv (C.ε y) = δ.weightEquiv (C.ε y)
      rw [hwε, h]
      rfl
    exact hwδ ▸ hw
  · right
    refine ⟨w, hw, fun x => ?_⟩
    have hlin : w.weightEquiv.toLinearMap = -δ.weightEquiv.toLinearMap := by
      apply C.linearMap_ext
      intro y
      change w.weightEquiv (C.ε y) = -δ.weightEquiv (C.ε y)
      rw [hwε, h, neg_neg]
      rfl
    exact LinearMap.congr_fun hlin x

section Transport

variable {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [AddCommGroup N₂]
  {Q : RootPairing ι₂ ℤ M₂ N₂}

/-- Transport of type `A` coordinates along an equivalence of root pairings. -/
noncomputable def transport (e : P.Equiv Q) : TypeACoord Q n where
  ε y := e.weightEquiv (C.ε y)
  exists_eq_sum x := by
    obtain ⟨c, hc⟩ := C.exists_eq_sum (e.weightEquiv.symm x)
    refine ⟨c, ?_⟩
    simp only [← map_smul, ← map_sum, ← hc, LinearEquiv.apply_symm_apply]
  sum_eq_zero := by rw [← map_sum, C.sum_eq_zero, map_zero]
  eq_of_sum_eq_zero c hc := by
    apply C.eq_of_sum_eq_zero c
    apply e.weightEquiv.injective
    simpa only [map_sum, map_smul, map_zero] using hc
  exists_root_eq j := by
    obtain ⟨a, b, hab, h⟩ := C.exists_root_eq (e.indexEquiv.symm j)
    refine ⟨a, b, hab, ?_⟩
    rw [← map_sub, ← h, e.weightEquiv_apply, e.root_weightMap_apply P Q,
      Equiv.apply_symm_apply]
  exists_eq_root a b hab := by
    obtain ⟨j, hj⟩ := C.exists_eq_root a b hab
    exact ⟨e.indexEquiv j, by
      rw [← e.root_weightMap_apply P Q, ← e.weightEquiv_apply, hj, map_sub]⟩
  coroot'_apply j a b h y := by
    have h' : P.root (e.indexEquiv.symm j) = C.ε a - C.ε b := by
      apply e.weightEquiv.injective
      rw [map_sub, ← h, e.weightEquiv_apply, e.root_weightMap_apply P Q,
        Equiv.apply_symm_apply]
    rw [← C.coroot'_apply _ a b h' y, ← e.coroot'_weightEquiv, Equiv.apply_symm_apply]

@[simp]
theorem transport_ε (e : P.Equiv Q) (y : Fin (n + 1)) :
    (C.transport e).ε y = e.weightEquiv (C.ε y) :=
  rfl

end Transport

end TypeACoord

section Coroots

variable {P : RootPairing ι ℤ M N}

/-- Spanning of the coweight lattice by coroots transports along equivalences
of root pairings. -/
theorem span_coroot_eq_top_of_equiv {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [AddCommGroup N₂]
    {Q : RootPairing ι₂ ℤ M₂ N₂} (e : P.Equiv Q)
    (h : Submodule.span ℤ (Set.range P.coroot) = ⊤) :
    Submodule.span ℤ (Set.range Q.coroot) = ⊤ := by
  have hrange : Set.range Q.coroot =
      (e.coweightEquiv.symm.toLinearMap : N →ₗ[ℤ] N₂) '' Set.range P.coroot := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨P.coroot (e.indexEquiv.symm i), ⟨_, rfl⟩, ?_⟩
      rw [LinearEquiv.coe_coe, LinearEquiv.symm_apply_eq, Equiv.coweightEquiv_apply,
        Hom.coroot_coweightMap_apply]
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      refine ⟨e.indexEquiv i, ?_⟩
      rw [LinearEquiv.coe_coe, eq_comm, LinearEquiv.symm_apply_eq, Equiv.coweightEquiv_apply,
        Hom.coroot_coweightMap_apply, Equiv.symm_apply_apply]
  rw [hrange, Submodule.span_image, h, Submodule.map_top, LinearMap.range_eq_top]
  exact e.coweightEquiv.symm.surjective

/-- An automorphism fixing every index of a set whose coroots span the whole
coweight lattice is the identity. -/
theorem eq_one_of_indexEquiv_eq (θ : P.Aut) (s : Set ι)
    (hs : Submodule.span ℤ (P.coroot '' s) = ⊤) (hθ : ∀ i ∈ s, θ.indexEquiv i = i) :
    θ = 1 := by
  apply RootPairing.Equiv.coweightHom_injective P
  rw [map_one]
  change MulOpposite.op θ.coweightEquiv = MulOpposite.op 1
  congr 1
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.ext_on hs ?_
  rintro _ ⟨i, hi, rfl⟩
  have hsymm : θ.indexEquiv.symm i = i := by
    rw [Equiv.symm_apply_eq, hθ i hi]
  simp [Equiv.coweightEquiv_apply, Hom.coroot_coweightMap_apply, hsymm]

end Coroots

end Langlands.LinearAlgebra.RootPairingTypeA
