import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Group.Submonoid.Finsupp
import Mathlib.Order.Preorder.Finite

/-! # Dominant-weight triangularity in the group algebra of a root datum -/

noncomputable section

open scoped Pointwise

namespace Langlands.RootDatum.Triangular

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (P : RootPairing ι ℤ X Y) (b : P.Base)

/-- The additive monoid of nonnegative integral combinations of simple roots. -/
def positiveCone : AddSubmonoid X :=
  AddSubmonoid.closure (Set.range fun a : b.support => P.root a)

/-- A weight is dominant when it pairs nonnegatively with every simple coroot. -/
def IsDominant (x : X) : Prop :=
  ∀ a ∈ b.support, 0 ≤ P.toLinearMap x (P.coroot a)

/-- An element of the group algebra whose coefficients are invariant under every
root reflection. -/
def IsReflectionInvariant {k : Type*} [CommRing k] (f : AddMonoidAlgebra k X) : Prop :=
  ∀ (i : ι) (x : X), f.coeff (P.reflection i x) = f.coeff x

/-- An element of the group algebra with coefficient one at `ν` and every weight
of its support below `ν` in the simple-root order. -/
def IsTopWeight {k : Type*} [CommRing k] (ν : X) (g : AddMonoidAlgebra k X) : Prop :=
  g.coeff ν = 1 ∧ ∀ μ ∈ g.coeff.support, ν - μ ∈ positiveCone P b

/-- The weight `∑ j, m j • lam j` of the exponent vector `m`. -/
def expWeight {r : ℕ} (lam : Fin r → X) (m : Fin r → ℕ) : X :=
  ∑ j, m j • lam j

variable {P b}

section Cone

/-- The simple-root cone is pointed, by linear independence of the simple roots. -/
theorem eq_zero_of_mem_positiveCone_of_neg_mem {x : X}
    (hx : x ∈ positiveCone P b) (hx' : -x ∈ positiveCone P b) : x = 0 := by
  classical
  obtain ⟨n, rfl⟩ := AddSubmonoid.mem_closure_range_iff_of_fintype.1 hx
  obtain ⟨m, hm⟩ := AddSubmonoid.mem_closure_range_iff_of_fintype.1 hx'
  have hli : LinearIndependent ℤ (fun a : b.support => P.root a) := b.linearIndepOn_root
  have hsum : ∑ a : b.support, ((n a + m a : ℕ) : ℤ) • P.root a = 0 := by
    simp only [Nat.cast_add, add_smul, Finset.sum_add_distrib, Nat.cast_smul_eq_nsmul]
    rw [← hm]
    exact add_neg_cancel _
  have h0 := Fintype.linearIndependent_iff.1 hli _ hsum
  have hn : ∀ a, n a = 0 := fun a => by have := h0 a; omega
  simp [hn]

theorem positiveCone_le_rootSpan :
    positiveCone P b ≤ (P.rootSpan ℤ).toAddSubmonoid := by
  rw [positiveCone, AddSubmonoid.closure_le]
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨a, rfl⟩

/-- Every nonempty finite set of weights has a maximal element for the simple-root
order. -/
theorem exists_maximal_of_finset (T : Finset X) (hT : T.Nonempty) :
    ∃ ν ∈ T, ∀ μ ∈ T, μ - ν ∈ positiveCone P b → μ = ν := by
  let : Preorder X :=
    { le := fun x y => y - x ∈ positiveCone P b
      le_refl := fun x => by simp only [sub_self]; exact zero_mem _
      le_trans := fun x y z hxy hyz => by
        have := add_mem hyz hxy
        rwa [sub_add_sub_cancel] at this }
  obtain ⟨ν, hν⟩ := T.exists_maximal hT
  refine ⟨ν, hν.1, fun μ hμ hle => ?_⟩
  have h2 : ν - μ ∈ positiveCone P b := hν.2 hμ hle
  have h3 : -(μ - ν) ∈ positiveCone P b := by rwa [neg_sub]
  exact sub_eq_zero.1 (eq_zero_of_mem_positiveCone_of_neg_mem hle h3)

/-- A maximal element of a finite set stable under the simple reflections is
dominant. -/
theorem exists_isDominant_of_stable (T : Finset X) (hT : T.Nonempty)
    (hstab : ∀ a ∈ b.support, ∀ x ∈ T, P.reflection a x ∈ T) :
    ∃ x ∈ T, IsDominant P b x := by
  obtain ⟨ν, hν, hmax⟩ := exists_maximal_of_finset (P := P) (b := b) T hT
  refine ⟨ν, hν, fun a ha => ?_⟩
  by_contra hneg
  push Not at hneg
  have hmem : P.reflection a ν - ν ∈ positiveCone P b := by
    have hcast : (((-P.toLinearMap ν (P.coroot a)).toNat : ℕ) : ℤ) =
        -P.toLinearMap ν (P.coroot a) := Int.toNat_of_nonneg (by omega)
    have : P.reflection a ν - ν = (-P.toLinearMap ν (P.coroot a)).toNat • P.root a := by
      rw [← Nat.cast_smul_eq_nsmul ℤ, hcast, P.reflection_apply, neg_smul]
      simp
    rw [this]
    exact nsmul_mem (AddSubmonoid.subset_closure
      (Set.mem_range_self (f := fun a : b.support => P.root a) ⟨a, ha⟩)) _
  have heq := hmax _ (hstab a ha ν hν) hmem
  rw [P.reflection_apply, sub_eq_self] at heq
  have := congrArg (fun y => P.toLinearMap y (P.coroot a)) heq
  simp only [map_smul, LinearMap.smul_apply, map_zero, LinearMap.zero_apply,
    RootPairing.root_coroot_eq_pairing, RootPairing.pairing_same, smul_eq_mul] at this
  change P.toLinearMap ν (P.coroot a) * 2 = 0 at this
  omega

end Cone

section Form

variable [Fintype ι]

theorem two_mul_rootForm_root (a : ι) (x : X) :
    2 * P.RootForm (P.root a) x =
      P.RootForm (P.root a) (P.root a) * P.toLinearMap x (P.coroot a) := by
  have h := congrArg (fun y => P.toLinearMap x y) (P.rootForm_self_smul_coroot a)
  simp only [map_smul, map_nsmul, P.toLinearMap_apply_apply_Polarization, smul_eq_mul,
    nsmul_eq_mul] at h
  push_cast at h
  linarith

theorem rootForm_root_pos (a : ι) : 0 < P.RootForm (P.root a) (P.root a) :=
  P.rootForm_pos_of_ne_zero (Submodule.subset_span ⟨a, rfl⟩) (P.ne_zero a)

theorem rootForm_nonneg_of_mem_positiveCone {s x : X} (hs : s ∈ positiveCone P b)
    (hx : IsDominant P b x) : 0 ≤ P.RootForm s x := by
  induction hs using AddSubmonoid.closure_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    have h := two_mul_rootForm_root (P := P) a x
    have h1 := rootForm_root_pos (P := P) a
    have h2 := hx a a.2
    nlinarith
  | zero => simp
  | add y z _ _ hy hz =>
    simp only [map_add, LinearMap.add_apply]
    exact add_nonneg hy hz

/-- For dominant weights `μ ≤ ν`, the canonical form satisfies `B(μ,μ) ≤ B(ν,ν)`,
with equality only for `μ = ν`. -/
theorem rootForm_self_le_of_isDominant {μ ν : X} (hμ : IsDominant P b μ)
    (hν : IsDominant P b ν) (h : ν - μ ∈ positiveCone P b) :
    P.RootForm μ μ ≤ P.RootForm ν ν ∧ (P.RootForm μ μ = P.RootForm ν ν → μ = ν) := by
  have h1 := rootForm_nonneg_of_mem_positiveCone h hν
  have h2 := rootForm_nonneg_of_mem_positiveCone h hμ
  have hsymm : P.RootForm μ ν = P.RootForm ν μ := by
    simpa using LinearMap.isSymm_def.1 P.rootForm_symmetric μ ν
  have key : P.RootForm ν ν - P.RootForm μ μ =
      P.RootForm (ν - μ) ν + P.RootForm (ν - μ) μ := by
    simp only [map_sub, LinearMap.sub_apply]
    rw [hsymm]
    ring
  refine ⟨by linarith, fun heq => ?_⟩
  have e1 : P.RootForm (ν - μ) ν = 0 := by linarith
  have e2 : P.RootForm (ν - μ) μ = 0 := by linarith
  have e3 : P.RootForm (ν - μ) (ν - μ) = 0 := by rw [map_sub, e1, e2, sub_zero]
  have := P.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero (positiveCone_le_rootSpan h) e3
  exact (sub_eq_zero.1 this).symm

/-- When the root span has finite index, a weight pairing to zero with every simple
coroot is zero. -/
theorem eq_zero_of_forall_simple_coroot (hfin : Finite (X ⧸ P.rootSpan ℤ)) {x : X}
    (hx : ∀ a ∈ b.support, P.toLinearMap x (P.coroot a) = 0) : x = 0 := by
  have hspan : ∀ y ∈ Submodule.span ℤ (P.coroot '' b.support), P.toLinearMap x y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      exact hx a ha
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul t y _ hy => simp [hy]
  have hcor : ∀ i, P.toLinearMap x (P.coroot i) = 0 := fun i =>
    hspan _ (b.coroot_mem_span_int i)
  obtain ⟨n, hn, hnx⟩ :=
    (isOfFinAddOrder_of_finite (Submodule.Quotient.mk (p := P.rootSpan ℤ) x)).exists_nsmul_eq_zero
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hnx
  have hform : P.RootForm (n • x) (n • x) = 0 := by
    rw [P.rootForm_apply_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [hcor i]
  have hnx0 := P.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero hnx hform
  apply (LinearMap.IsPerfPair.bijective_left P.toLinearMap).injective
  rw [map_zero]
  ext y
  have h1 : P.toLinearMap (n • x) y = 0 := by simp [hnx0]
  rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h1
  rw [LinearMap.zero_apply]
  rcases mul_eq_zero.1 h1 with h | h
  · exact absurd (by exact_mod_cast h) hn.ne'
  · exact h

end Form

section TopWeight

variable {k : Type*} [CommRing k]

theorem isTopWeight_one : IsTopWeight P b (0 : X) (1 : AddMonoidAlgebra k X) := by
  classical
  refine ⟨by simp [AddMonoidAlgebra.one_def], fun μ hμ => ?_⟩
  have : μ = 0 := by
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single] at hμ
    exact Finset.mem_singleton.1 (Finsupp.support_single_subset hμ)
  subst this
  simp

theorem IsTopWeight.mul {ν ν' : X} {g h : AddMonoidAlgebra k X}
    (hg : IsTopWeight P b ν g) (hh : IsTopWeight P b ν' h) :
    IsTopWeight P b (ν + ν') (g * h) := by
  classical
  constructor
  · rw [AddMonoidAlgebra.coeff_mul, Finsupp.sum, Finset.sum_eq_single ν]
    · rw [Finsupp.sum, Finset.sum_eq_single ν']
      · simp [hg.1, hh.1]
      · intro m2 _ hne
        exact ite_eq_right_iff.2 fun hm => absurd (add_left_cancel hm) hne
      · intro hν
        simp [Finsupp.notMem_support_iff.1 hν]
    · intro m1 hm1 hne
      apply Finset.sum_eq_zero
      intro m2 hm2
      refine ite_eq_right_iff.2 fun hm => absurd ?_ hne
      have h1 := hg.2 m1 hm1
      have h2 := hh.2 m2 hm2
      have h3 : -(ν - m1) = ν' - m2 := by
        rw [neg_sub, sub_eq_sub_iff_add_eq_add, hm, add_comm]
      rw [← h3] at h2
      exact (sub_eq_zero.1 (eq_zero_of_mem_positiveCone_of_neg_mem h1 h2)).symm
    · intro hν
      simp [Finsupp.notMem_support_iff.1 hν]
  · intro μ hμ
    obtain ⟨a, ha, c, hc, rfl⟩ :=
      Finset.mem_add.1 (AddMonoidAlgebra.support_coeff_mul_subset g h hμ)
    have : ν + ν' - (a + c) = (ν - a) + (ν' - c) := by abel
    rw [this]
    exact add_mem (hg.2 a ha) (hh.2 c hc)

theorem IsTopWeight.pow {ν : X} {g : AddMonoidAlgebra k X} (hg : IsTopWeight P b ν g)
    (n : ℕ) : IsTopWeight P b (n • ν) (g ^ n) := by
  induction n with
  | zero => simpa using (isTopWeight_one (P := P) (b := b) (k := k))
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact ih.mul hg

theorem isTopWeight_prod {σ : Type*} (s : Finset σ) (ν : σ → X)
    (g : σ → AddMonoidAlgebra k X) (h : ∀ i ∈ s, IsTopWeight P b (ν i) (g i)) :
    IsTopWeight P b (∑ i ∈ s, ν i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isTopWeight_one (P := P) (b := b) (k := k))
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    exact (h j (Finset.mem_insert_self _ _)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isTopWeight_monomial {r : ℕ} {c : Fin r → AddMonoidAlgebra k X} {lam : Fin r → X}
    (hc : ∀ j, IsTopWeight P b (lam j) (c j)) (m : Fin r → ℕ) :
    IsTopWeight P b (expWeight lam m) (∏ j, c j ^ m j) :=
  isTopWeight_prod _ _ _ fun j _ => (hc j).pow (m j)

theorem IsReflectionInvariant.sub_smul {f g : AddMonoidAlgebra k X}
    (hf : IsReflectionInvariant P f) (hg : IsReflectionInvariant P g) (t : k) :
    IsReflectionInvariant P (f - t • g) := fun i x => by
  simp only [AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_smul, Finsupp.coe_sub,
    Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply, hf i x, hg i x]

end TopWeight

section Main

variable {k : Type*} [CommRing k] {r : ℕ}
  {c : Fin r → AddMonoidAlgebra k X} {lam : Fin r → X} {e : Fin r ≃ b.support}

theorem pairing_expWeight
    (hlam1 : ∀ j, P.toLinearMap (lam j) (P.coroot (e j)) = 1)
    (hlam0 : ∀ j (a : b.support), a ≠ e j → P.toLinearMap (lam j) (P.coroot a) = 0)
    (m : Fin r → ℕ) (a : b.support) :
    P.toLinearMap (expWeight lam m) (P.coroot a) = m (e.symm a) := by
  simp only [expWeight, map_sum, map_nsmul, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_eq_single (e.symm a)]
  · have h1 := hlam1 (e.symm a)
    rw [Equiv.apply_symm_apply] at h1
    rw [h1]
    simp
  · intro j _ hj
    rw [hlam0 j a fun h => hj (by rw [h, Equiv.symm_apply_apply]), smul_zero]
  · simp

theorem expWeight_injective
    (hlam1 : ∀ j, P.toLinearMap (lam j) (P.coroot (e j)) = 1)
    (hlam0 : ∀ j (a : b.support), a ≠ e j → P.toLinearMap (lam j) (P.coroot a) = 0) :
    Function.Injective (expWeight lam) := by
  intro m m' h
  funext j
  have := congrArg (fun x => P.toLinearMap x (P.coroot (e j))) h
  simp only [pairing_expWeight hlam1 hlam0, Equiv.symm_apply_apply] at this
  exact_mod_cast this

theorem aeval_eq_sum (q : MvPolynomial (Fin r) k) :
    MvPolynomial.aeval c q = ∑ m ∈ q.support, q.coeff m • ∏ j, c j ^ m j := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  simp only [Algebra.smul_def]

/-- Polynomials in elements with linearly independent top weights are injective. -/
theorem aeval_injective
    (hlam1 : ∀ j, P.toLinearMap (lam j) (P.coroot (e j)) = 1)
    (hlam0 : ∀ j (a : b.support), a ≠ e j → P.toLinearMap (lam j) (P.coroot a) = 0)
    (hc : ∀ j, IsTopWeight P b (lam j) (c j)) :
    Function.Injective (MvPolynomial.aeval (R := k) c) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro q hq
  by_contra hq0
  have hne : (q.support.image fun m : Fin r →₀ ℕ => expWeight lam ⇑m).Nonempty :=
    (Finset.nonempty_iff_ne_empty.2 (mt MvPolynomial.support_eq_empty.1 hq0)).image _
  obtain ⟨ν, hνT, hmax⟩ := exists_maximal_of_finset (P := P) (b := b) _ hne
  obtain ⟨m0, hm0, rfl⟩ := Finset.mem_image.1 hνT
  have hcoeff : (MvPolynomial.aeval c q).coeff (expWeight lam ⇑m0) = 0 := by
    simp [hq]
  rw [aeval_eq_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    Finset.sum_eq_single m0] at hcoeff
  · rw [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, (isTopWeight_monomial hc _).1,
      smul_eq_mul, mul_one] at hcoeff
    exact (MvPolynomial.mem_support_iff.1 hm0) hcoeff
  · intro m hm hne
    rw [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply]
    have : (∏ j, c j ^ m j).coeff (expWeight lam ⇑m0) = 0 := by
      by_contra hnz
      have hmem := (isTopWeight_monomial hc ⇑m).2 _ (Finsupp.mem_support_iff.2 hnz)
      have := hmax _ (Finset.mem_image_of_mem _ hm) hmem
      exact hne (DFunLike.coe_injective (expWeight_injective hlam1 hlam0 this))
    rw [this, smul_zero]
  · intro h
    exact absurd hm0 h

variable [Fintype ι]

/-- The finite set of weights of `f` with a fixed value of the canonical form is
stable under the simple reflections when `f` is reflection invariant. -/
theorem filter_rootForm_stable {f : AddMonoidAlgebra k X} (hf : IsReflectionInvariant P f)
    (t : ℤ) [DecidablePred fun μ : X => P.RootForm μ μ = t] :
    ∀ a ∈ b.support, ∀ x ∈ f.coeff.support.filter (fun μ => P.RootForm μ μ = t),
      P.reflection a x ∈ f.coeff.support.filter (fun μ => P.RootForm μ μ = t) := by
  intro a _ x hx
  rw [Finset.mem_filter, Finsupp.mem_support_iff] at hx ⊢
  rw [hf a x, P.rootForm_reflection_reflection_apply]
  exact hx

/-- A reflection-invariant element with dominant top weight `ν` has all its
weights of canonical length at most that of `ν`. -/
theorem rootForm_le_of_isTopWeight {g : AddMonoidAlgebra k X} {ν : X}
    (hg : IsTopWeight P b ν g) (hgi : IsReflectionInvariant P g) (hν : IsDominant P b ν)
    {μ : X} (hμ : μ ∈ g.coeff.support) : P.RootForm μ μ ≤ P.RootForm ν ν := by
  classical
  obtain ⟨μ', hμ', hdom⟩ := exists_isDominant_of_stable (P := P) (b := b)
    (g.coeff.support.filter fun x => P.RootForm x x = P.RootForm μ μ)
    ⟨μ, Finset.mem_filter.2 ⟨hμ, rfl⟩⟩ (filter_rootForm_stable hgi _)
  rw [Finset.mem_filter] at hμ'
  rw [← hμ'.2]
  exact (rootForm_self_le_of_isDominant hdom hν (hg.2 _ hμ'.1)).1

/-- Reflection-invariant elements are polynomials in reflection-invariant elements
with fundamental top weights, provided weights are detected by simple coroots. -/
theorem mem_range_aeval
    (hlam1 : ∀ j, P.toLinearMap (lam j) (P.coroot (e j)) = 1)
    (hlam0 : ∀ j (a : b.support), a ≠ e j → P.toLinearMap (lam j) (P.coroot a) = 0)
    (hc : ∀ j, IsTopWeight P b (lam j) (c j))
    (hinv : ∀ q, IsReflectionInvariant P (MvPolynomial.aeval (R := k) c q))
    (hss : ∀ x : X, (∀ a ∈ b.support, P.toLinearMap x (P.coroot a) = 0) → x = 0)
    (f : AddMonoidAlgebra k X) (hf : IsReflectionInvariant P f) :
    f ∈ (MvPolynomial.aeval (R := k) c).range := by
  classical
  -- the dominant weights of a given canonical length
  let D : ℕ → AddMonoidAlgebra k X → Finset X := fun n f =>
    f.coeff.support.filter fun μ => IsDominant P b μ ∧ P.RootForm μ μ = n
  -- with no dominant weight of length `n`, the length bound drops
  have hdrop : ∀ (n : ℕ) (f : AddMonoidAlgebra k X), IsReflectionInvariant P f →
      (∀ μ ∈ f.coeff.support, P.RootForm μ μ < n + 1) → D n f = ∅ →
      ∀ μ ∈ f.coeff.support, P.RootForm μ μ < n := by
    intro n f hf hfn hD μ hμ
    by_contra hge
    have hμn : P.RootForm μ μ = n := by have := hfn μ hμ; omega
    obtain ⟨x, hx, hdom⟩ := exists_isDominant_of_stable (P := P) (b := b)
      (f.coeff.support.filter fun x => P.RootForm x x = n)
      ⟨μ, Finset.mem_filter.2 ⟨hμ, hμn⟩⟩ (filter_rootForm_stable hf _)
    rw [Finset.mem_filter] at hx
    have : x ∈ D n f := Finset.mem_filter.2 ⟨hx.1, hdom, hx.2⟩
    rw [hD] at this
    exact Finset.notMem_empty _ this
  suffices H : ∀ n : ℕ, ∀ f : AddMonoidAlgebra k X, IsReflectionInvariant P f →
      (∀ μ ∈ f.coeff.support, P.RootForm μ μ < n) → f ∈ (MvPolynomial.aeval (R := k) c).range by
    refine H ((f.coeff.support.sup fun μ => (P.RootForm μ μ).toNat) + 1) f hf fun μ hμ => ?_
    have := Finset.le_sup (f := fun μ => (P.RootForm μ μ).toNat) hμ
    have h0 := P.zero_le_rootForm μ
    omega
  intro n
  induction n with
  | zero =>
    intro f _ hfn
    have hsupp : f.coeff.support = ∅ := Finset.eq_empty_of_forall_notMem fun μ hμ => by
      have := hfn μ hμ
      have h0 := P.zero_le_rootForm μ
      omega
    have : f = 0 := by
      rw [← AddMonoidAlgebra.coeff_eq_zero]
      exact Finsupp.support_eq_empty.1 hsupp
    rw [this]
    exact zero_mem _
  | succ n ih =>
    suffices H2 : ∀ d : ℕ, ∀ f : AddMonoidAlgebra k X, IsReflectionInvariant P f →
        (∀ μ ∈ f.coeff.support, P.RootForm μ μ < n + 1) → (D n f).card ≤ d →
          f ∈ (MvPolynomial.aeval (R := k) c).range by
      intro f hf hfn
      exact H2 _ f hf (by exact_mod_cast hfn) le_rfl
    intro d
    induction d with
    | zero =>
      intro f hf hfn hd
      exact ih f hf (hdrop n f hf hfn (Finset.card_eq_zero.1 (Nat.le_zero.1 hd)))
    | succ d ihd =>
      intro f hf hfn hd
      by_cases hD : D n f = ∅
      · exact ih f hf (hdrop n f hf hfn hD)
      obtain ⟨ν, hνD⟩ := Finset.nonempty_iff_ne_empty.2 hD
      have hνD' := Finset.mem_filter.1 hνD
      obtain ⟨hνf, hνdom, hνn⟩ := hνD'
      let m : Fin r → ℕ := fun j => (P.toLinearMap ν (P.coroot (e j))).toNat
      have hmν : expWeight lam m = ν := by
        apply sub_eq_zero.1
        apply hss
        intro a ha
        rw [map_sub, LinearMap.sub_apply, pairing_expWeight hlam1 hlam0 m ⟨a, ha⟩, sub_eq_zero]
        simp only [m, Equiv.apply_symm_apply]
        exact Int.toNat_of_nonneg (hνdom a ha)
      let g : AddMonoidAlgebra k X := ∏ j, c j ^ m j
      have hgr : g ∈ (MvPolynomial.aeval (R := k) c).range :=
        ⟨∏ j, MvPolynomial.X j ^ m j, by simp [g]⟩
      have hgtop : IsTopWeight P b ν g := hmν ▸ isTopWeight_monomial hc m
      have hgi : IsReflectionInvariant P g := by
        obtain ⟨q, hq⟩ := hgr
        rw [← hq]
        exact hinv q
      let f' := f - f.coeff ν • g
      have hf'i : IsReflectionInvariant P f' := hf.sub_smul hgi _
      have hsupp : ∀ μ ∈ f'.coeff.support, μ ∈ f.coeff.support ∨ μ ∈ g.coeff.support := by
        intro μ hμ
        by_contra hcon
        push Not at hcon
        rw [Finsupp.mem_support_iff] at hμ
        apply hμ
        simp only [f', AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_smul,
          Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply,
          Finsupp.notMem_support_iff.1 hcon.1, Finsupp.notMem_support_iff.1 hcon.2,
          smul_zero, sub_zero]
      have hf'n : ∀ μ ∈ f'.coeff.support, P.RootForm μ μ < n + 1 := by
        intro μ hμ
        rcases hsupp μ hμ with h | h
        · exact hfn μ h
        · have := rootForm_le_of_isTopWeight hgtop hgi hνdom h
          omega
      have hsub : D n f' ⊆ (D n f).erase ν := by
        intro μ hμ
        obtain ⟨hμf', hμdom, hμn⟩ := Finset.mem_filter.1 hμ
        have hμν : μ ≠ ν := by
          rintro rfl
          rw [Finsupp.mem_support_iff] at hμf'
          apply hμf'
          simp only [f', AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_smul,
            Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply, hgtop.1,
            smul_eq_mul, mul_one, sub_self]
        refine Finset.mem_erase.2 ⟨hμν, Finset.mem_filter.2 ⟨?_, hμdom, hμn⟩⟩
        rcases hsupp μ hμf' with h | h
        · exact h
        · exfalso
          apply hμν
          exact (rootForm_self_le_of_isDominant hμdom hνdom (hgtop.2 μ h)).2
            (by rw [hμn, hνn])
      have hcard : (D n f').card ≤ d := by
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hνD] at this
        omega
      have hf' := ihd f' hf'i hf'n hcard
      have := add_mem hf' (Subalgebra.smul_mem _ hgr (f.coeff ν))
      simpa [f'] using this

end Main

end Langlands.RootDatum.Triangular
