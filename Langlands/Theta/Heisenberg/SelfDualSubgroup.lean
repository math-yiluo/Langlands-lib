import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.Divisible
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Order.Zorn

/-!
# Alternating bicharacters and projective representations (internal)

The abstract part of the construction of the induced model of the Heisenberg group (GKT §1.2.1:
Lemma 1.3, Corollary 1.4, and the eigenvector arguments behind Proposition 1.12 and Theorem 1.31).
Let `W` be an abelian group and `c : W → W → ℂ` an alternating bicharacter (`c x x = 1`). A
projective representation `ρ` of `W` with cocycle `c` on a complex vector space
(`ρ x ∘ ρ y = c x y ρ (x+y)`)
satisfies `ρ x ρ y = c x y ² ρ y ρ x`. For a subgroup `A` that is its own orthogonal for
`c²` and a function `α` splitting `c` on `A`, this file proves:

* `exists_eigenvector`: an invariant subspace containing a vector fixed by the orthogonal of a
  set `T` (with `A / T^⊥` finite and `α = 1` on `T^⊥`) contains an `α`-eigenvector of `A`
  (averaging over `A / T^⊥` and the linear independence of characters);
* `exists_eq_smul_of_mem_span`: an `α`-eigenvector in the span of the translates `ρ x e` of an
  `α`-eigenvector `e` is a multiple of `e`;
* `exists_le_selfOrthogonal`: every self-orthogonal subgroup lies in a maximal one, which equals
  its orthogonal (Zorn);
* `exists_splitsOn`: on a self-orthogonal subgroup `c` is split by some `α`, extending a given
  splitting `1` on a subgroup where `c = 1` (injectivity of `ℂˣ` as an abelian group).

Everything here is internal to `Langlands.Theta.Heisenberg.SelfDual` and
`Langlands.Theta.Heisenberg.InducedModel`.
-/

noncomputable section

namespace Langlands.HeisenbergGroup.Internal

variable {W M : Type*} [AddCommGroup W] [AddCommGroup M] [Module ℂ M]

/-- `c` is an alternating bicharacter on `W`. -/
structure IsAlternatingBicharacter (c : W → W → ℂ) : Prop where
  map_add_left : ∀ x y z, c (x + y) z = c x z * c y z
  map_add_right : ∀ x y z, c x (y + z) = c x y * c x z
  apply_self : ∀ x, c x x = 1

variable {c : W → W → ℂ}

namespace IsAlternatingBicharacter

theorem mul_swap (h : IsAlternatingBicharacter c) (x y : W) : c x y * c y x = 1 := by
  have := h.apply_self (x + y)
  rw [h.map_add_left, h.map_add_right, h.map_add_right, h.apply_self, h.apply_self] at this
  simpa using this

theorem ne_zero (h : IsAlternatingBicharacter c) (x y : W) : c x y ≠ 0 :=
  left_ne_zero_of_mul_eq_one (h.mul_swap x y)

theorem zero_left (h : IsAlternatingBicharacter c) (y : W) : c 0 y = 1 := by
  have := h.map_add_left 0 0 y
  rw [add_zero] at this
  exact (mul_eq_left₀ (h.ne_zero 0 y)).1 this.symm

theorem zero_right (h : IsAlternatingBicharacter c) (y : W) : c y 0 = 1 := by
  have := h.mul_swap y 0
  rwa [h.zero_left, mul_one] at this

theorem sq_eq_one_swap (h : IsAlternatingBicharacter c) {x y : W} (hxy : c x y ^ 2 = 1) :
    c y x ^ 2 = 1 := by
  have := congrArg (· ^ 2) (h.mul_swap x y)
  simpa [mul_pow, hxy] using this

/-- The orthogonal `{x | c x t ² = 1 for all t ∈ T}` of a set `T`. -/
def orthogonal (h : IsAlternatingBicharacter c) (T : Set W) : AddSubgroup W where
  carrier := {x | ∀ t ∈ T, c x t ^ 2 = 1}
  add_mem' := fun {a b} ha hb t ht => by rw [h.map_add_left, mul_pow, ha t ht, hb t ht, mul_one]
  zero_mem' := fun t _ => by rw [h.zero_left, one_pow]
  neg_mem' := fun {a} ha t ht => by
    have := congrArg (· ^ 2) (h.map_add_left a (-a) t)
    simpa [mul_pow, ha t ht, h.zero_left] using this.symm

theorem mem_orthogonal (h : IsAlternatingBicharacter c) {T : Set W} {x : W} :
    x ∈ h.orthogonal T ↔ ∀ t ∈ T, c x t ^ 2 = 1 := Iff.rfl

theorem orthogonal_orthogonal_orthogonal_le (h : IsAlternatingBicharacter c) (T : Set W) :
    h.orthogonal (h.orthogonal (h.orthogonal T)) ≤ h.orthogonal T :=
  fun _ ha t ht => ha t fun _ hx => h.sq_eq_one_swap (hx t ht)

end IsAlternatingBicharacter

/-- `ρ` is a projective representation of `W` with cocycle `c`. -/
structure IsProjectiveRep (c : W → W → ℂ) (ρ : W → Module.End ℂ M) : Prop where
  apply_zero : ∀ v, ρ 0 v = v
  apply_apply : ∀ x y v, ρ x (ρ y v) = c x y • ρ (x + y) v

variable {ρ : W → Module.End ℂ M}

theorem IsProjectiveRep.comm (h : IsAlternatingBicharacter c) (hρ : IsProjectiveRep c ρ)
    (x y : W) (v : M) : ρ x (ρ y v) = c x y ^ 2 • ρ y (ρ x v) := by
  rw [hρ.apply_apply, hρ.apply_apply, smul_smul, add_comm y x, pow_two, mul_assoc, h.mul_swap,
    mul_one]

theorem IsProjectiveRep.eq_zero_of_apply_eq_zero (h : IsAlternatingBicharacter c)
    (hρ : IsProjectiveRep c ρ) {x : W} {v : M} (hv : ρ x v = 0) : v = 0 := by
  have := hρ.apply_apply (-x) x v
  rw [hv, map_zero, neg_add_cancel, hρ.apply_zero] at this
  exact (smul_eq_zero.1 this.symm).resolve_left (h.ne_zero _ _)

/-- `α` splits the cocycle `c` on the subgroup `A`. -/
structure SplitsOn (c : W → W → ℂ) (A : AddSubgroup W) (α : W → ℂ) : Prop where
  ne_zero : ∀ a ∈ A, α a ≠ 0
  mul : ∀ a ∈ A, ∀ b ∈ A, α a * α b = c a b * α (a + b)

variable {A : AddSubgroup W} {α : W → ℂ}

theorem SplitsOn.inv_smul_comp (hρ : IsProjectiveRep c ρ) (hα : SplitsOn c A α) {a b : W}
    (ha : a ∈ A) (hb : b ∈ A) (m : M) :
    (α a)⁻¹ • ρ a ((α b)⁻¹ • ρ b m) = (α (a + b))⁻¹ • ρ (a + b) m := by
  rw [map_smul, hρ.apply_apply, smul_smul, smul_smul]
  congr 1
  have := hα.mul a ha b hb
  have h1 := hα.ne_zero a ha
  have h2 := hα.ne_zero b hb
  have h3 := hα.ne_zero _ (A.add_mem ha hb)
  field_simp
  linear_combination -this

/-- Averaging `(α a)⁻¹ ρ a m` over `A / U` gives an `α`-eigenvector of `A`, when `m` is fixed by
`U ⊆ A` and `α = 1` on `U`. -/
theorem IsProjectiveRep.apply_average (hρ : IsProjectiveRep c ρ) (hα : SplitsOn c A α)
    (U : AddSubgroup W) (hU : ∀ u ∈ U, α u = 1) [Fintype (A ⧸ U.addSubgroupOf A)] (m : M)
    (hm : ∀ u ∈ U, ρ u m = m) (a : W) (ha : a ∈ A) :
    ρ a (∑ q : A ⧸ U.addSubgroupOf A, (α q.out.1)⁻¹ • ρ q.out.1 m)
      = α a • ∑ q : A ⧸ U.addSubgroupOf A, (α q.out.1)⁻¹ • ρ q.out.1 m := by
  rw [← inv_smul_eq_iff₀ (hα.ne_zero a ha), map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.addLeft ((⟨a, ha⟩ : A) : A ⧸ U.addSubgroupOf A)) _ _ fun q => ?_
  rw [hα.inv_smul_comp hρ ha q.out.2]
  set p := (Equiv.addLeft ((⟨a, ha⟩ : A) : A ⧸ U.addSubgroupOf A)) q with hp
  have h1 : (p.out : A ⧸ U.addSubgroupOf A) = ((⟨a, ha⟩ + q.out : A) : A ⧸ U.addSubgroupOf A) := by
    simp [hp]
  have h2 : -p.out.1 + (a + q.out.1) ∈ U := by
    have := QuotientAddGroup.eq.1 h1
    exact this
  have h3 := hα.inv_smul_comp hρ p.out.2 (A.add_mem (A.neg_mem p.out.2) (A.add_mem ha q.out.2)) m
  rw [hm _ h2, hU _ h2, add_neg_cancel_left] at h3
  rw [← h3]; simp

/-- An invariant subspace containing a non-zero vector fixed by the orthogonal of `T` contains a
non-zero `α`-eigenvector of `A`, when `A / T^⊥` is finite and `α = 1` on `T^⊥`. -/
theorem exists_eigenvector (h : IsAlternatingBicharacter c) (hρ : IsProjectiveRep c ρ)
    (hα : SplitsOn c A α) (T : Set W) (hU : ∀ u ∈ h.orthogonal T, α u = 1)
    [Finite (A ⧸ (h.orthogonal T).addSubgroupOf A)] (N : Submodule ℂ M)
    (hN : ∀ x, ∀ m ∈ N, ρ x m ∈ N) (v : M) (hvN : v ∈ N) (hv0 : v ≠ 0)
    (hv : ∀ u ∈ h.orthogonal T, ρ u v = v) :
    ∃ e ∈ N, e ≠ 0 ∧ ∀ a ∈ A, ρ a e = α a • e := by
  classical
  set U := h.orthogonal T with hUdef
  let := Fintype.ofFinite (A ⧸ U.addSubgroupOf A)
  by_contra hcon
  have hz : ∀ w ∈ h.orthogonal U, ∑ q : A ⧸ U.addSubgroupOf A,
      c q.out.1 w ^ 2 • ((α q.out.1)⁻¹ • ρ q.out.1 v) = 0 := by
    intro w hw
    have hm : ∀ u ∈ U, ρ u (ρ w v) = ρ w v := fun u hu => by
      rw [hρ.comm h, h.sq_eq_one_swap (hw u hu), one_smul, hv u hu]
    have h0 : ∑ q : A ⧸ U.addSubgroupOf A, (α q.out.1)⁻¹ • ρ q.out.1 (ρ w v) = 0 := by
      by_contra hne
      exact hcon ⟨_, N.sum_mem fun q _ => N.smul_mem _ (hN _ _ (hN _ _ hvN)), hne,
        hρ.apply_average hα U hU _ hm⟩
    refine hρ.eq_zero_of_apply_eq_zero h (x := w) ?_
    rw [map_sum, ← h0]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hρ.comm h q.out.1 w, map_smul, map_smul, smul_comm]
  let χ : A ⧸ U.addSubgroupOf A → (Multiplicative (h.orthogonal U) →* ℂ) := fun q =>
    { toFun := fun w => c q.out.1 w.toAdd.1 ^ 2
      map_one' := by simp [h.zero_right]
      map_mul' := fun x y => by simp [h.map_add_right, mul_pow] }
  have hχ : Function.Injective χ := by
    intro p q hpq
    rw [← p.out_eq, ← q.out_eq]
    refine QuotientAddGroup.eq.2 (h.orthogonal_orthogonal_orthogonal_le T fun w hw => ?_)
    have h1 : c p.out.1 w ^ 2 = c q.out.1 w ^ 2 :=
      DFunLike.congr_fun hpq (Multiplicative.ofAdd ⟨w, hw⟩)
    have h2 := h.map_add_left (-p.out.1) p.out.1 w
    rw [neg_add_cancel, h.zero_left] at h2
    show c (-p.out.1 + q.out.1) w ^ 2 = 1
    rw [h.map_add_left, mul_pow, ← h1, ← mul_pow, ← h2, one_pow]
  have hli := (linearIndependent_monoidHom (Multiplicative (h.orthogonal U)) ℂ).comp χ hχ
  have hq : ∀ q : A ⧸ U.addSubgroupOf A, (α q.out.1)⁻¹ • ρ q.out.1 v = 0 := by
    intro q
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun φ => ?_
    refine Fintype.linearIndependent_iff.1 hli (fun q => φ ((α q.out.1)⁻¹ • ρ q.out.1 v)) ?_ q
    funext w
    have := congrArg φ (hz w.toAdd.1 w.toAdd.2)
    rw [map_sum, map_zero] at this
    rw [Finset.sum_apply, Pi.zero_apply, ← this]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [φ.map_smul (c q.out.1 w.toAdd.1 ^ 2), smul_eq_mul, mul_comm]
    rfl
  have := (smul_eq_zero.1 (hq 0)).resolve_left
    (inv_ne_zero (hα.ne_zero _ (Quotient.out (0 : A ⧸ U.addSubgroupOf A)).2))
  exact hv0 (hρ.eq_zero_of_apply_eq_zero h this)

/-- A finite sum of eigenvectors of `A` for eigenvalue functions different from `α` that is an
`α`-eigenvector is zero. -/
theorem sum_eq_zero_of_eigenvalues_ne {ι : Type*} (s : Finset ι) (β : ι → W → ℂ)
    (hβ : ∀ i, ∃ a ∈ A, β i a ≠ α a) :
    ∀ (m : ι → M), (∀ i, ∀ a ∈ A, ρ a (m i) = β i a • m i) →
      (∀ a ∈ A, ρ a (∑ i ∈ s, m i) = α a • ∑ i ∈ s, m i) → ∑ i ∈ s, m i = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => intro m _ _; simp
  | insert j s hj ih =>
    intro m hm hv
    obtain ⟨a, ha, hne⟩ := hβ j
    have key : ∑ i ∈ s, (β i a - β j a) • m i = (α a - β j a) • ∑ i ∈ insert j s, m i := by
      rw [sub_smul, ← hv a ha, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib,
        Finset.sum_insert hj, hm j a ha, sub_self, zero_add]
      exact Finset.sum_congr rfl fun i _ => by rw [hm i a ha, sub_smul]
    have := ih (fun i => (β i a - β j a) • m i) (fun i b hb => by rw [map_smul, hm i b hb, smul_comm])
      (fun b hb => by rw [key, map_smul, hv b hb, smul_comm])
    rw [key] at this
    exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne.symm)

/-- When `A` contains its orthogonal, an `α`-eigenvector of `A` in the span of the translates
`ρ x e` of an `α`-eigenvector `e` is a multiple of `e`. -/
theorem exists_eq_smul_of_mem_span (h : IsAlternatingBicharacter c) (hρ : IsProjectiveRep c ρ)
    (hα : SplitsOn c A α) (hA : h.orthogonal A ≤ A) {e : M} (he : ∀ a ∈ A, ρ a e = α a • e)
    {v : M} (hv : v ∈ Submodule.span ℂ (Set.range fun x => ρ x e))
    (hva : ∀ a ∈ A, ρ a v = α a • v) : ∃ r : ℂ, v = r • e := by
  classical
  obtain ⟨f, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hv
  rw [Finsupp.sum, ← Finset.sum_filter_add_sum_filter_not _ (· ∈ A)] at hva ⊢
  have h1 : ∑ x ∈ f.support with x ∈ A, f x • ρ x e = (∑ x ∈ f.support with x ∈ A, f x * α x) • e := by
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun x hx => by rw [he x (Finset.mem_filter.1 hx).2, smul_smul]
  rw [h1] at hva ⊢
  refine ⟨_, add_eq_left.2 ?_⟩
  have h2 : ∑ x ∈ f.support with x ∉ A, f x • ρ x e =
      ∑ x ∈ f.support.subtype (· ∉ A), f x.1 • ρ x.1 e :=
    (Finset.sum_subtype_eq_sum_filter fun x => f x • ρ x e).symm
  rw [h2] at hva ⊢
  refine sum_eq_zero_of_eigenvalues_ne (ρ := ρ) (A := A) (α := α) _
    (fun x a => c a x.1 ^ 2 * α a) (fun x => ?_) _ (fun x a ha => ?_) fun a ha => ?_
  · by_contra hc
    push Not at hc
    exact x.2 (hA fun a ha => h.sq_eq_one_swap ((mul_eq_right₀ (hα.ne_zero a ha)).1 (hc a ha)))
  · rw [map_smul, hρ.comm h, he a ha, map_smul, smul_smul, smul_smul, smul_smul]
    congr 1; ring
  · have := hva a ha
    rwa [map_add, map_smul, he a ha, smul_add, smul_comm, add_right_inj] at this

/-- Every self-orthogonal subgroup is contained in a self-orthogonal subgroup that contains its
orthogonal. -/
theorem exists_le_selfOrthogonal (h : IsAlternatingBicharacter c) (L : AddSubgroup W)
    (hL : L ≤ h.orthogonal L) :
    ∃ A : AddSubgroup W, L ≤ A ∧ A ≤ h.orthogonal A ∧ h.orthogonal A ≤ A := by
  obtain ⟨A, hLA, hA, hmax⟩ := zorn_le_nonempty₀ {A : AddSubgroup W | A ≤ h.orthogonal A}
    (fun s hs hch y hy => by
      refine ⟨sSup s, fun a ha b hb => ?_, fun z hz => le_sSup hz⟩
      obtain ⟨P, hP, ha⟩ := (AddSubgroup.mem_sSup_of_directedOn ⟨y, hy⟩ hch.directedOn).1 ha
      obtain ⟨Q, hQ, hb⟩ := (AddSubgroup.mem_sSup_of_directedOn ⟨y, hy⟩ hch.directedOn).1 hb
      obtain ⟨R, hR, h1, h2⟩ := hch.directedOn P hP Q hQ
      exact hs hR (h1 ha) b (h2 hb)) L hL
  refine ⟨A, hLA, hA, fun x hx => ?_⟩
  have h1 : AddSubgroup.closure (insert x (A : Set W)) ≤ h.orthogonal (insert x (A : Set W)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro a (rfl | ha) b (rfl | hb)
    · rw [h.apply_self, one_pow]
    · exact hx b hb
    · exact h.sq_eq_one_swap (hx a ha)
    · exact hA ha b hb
  have h2 : AddSubgroup.closure (insert x (A : Set W)) ≤
      h.orthogonal (AddSubgroup.closure (insert x (A : Set W))) :=
    (AddSubgroup.closure_le _).2 fun a ha b hb => h.sq_eq_one_swap (h1 hb a ha)
  exact hmax h2 (fun a ha => AddSubgroup.subset_closure (Or.inr ha))
    (AddSubgroup.subset_closure (Or.inl rfl))

/-- The extension of `A` by `ℂˣ` with the symmetric cocycle `b`. -/
@[ext] structure TwistedProduct {A : Type*} [AddCommGroup A] (b : A →+ A →+ Additive ℂˣ)
    (hb : ∀ x y, b x y = b y x) where
  /-- The point of `A`. -/
  pt : A
  /-- The scalar. -/
  sc : Additive ℂˣ

instance {A : Type*} [AddCommGroup A] (b : A →+ A →+ Additive ℂˣ) (hb : ∀ x y, b x y = b y x) :
    AddCommGroup (TwistedProduct b hb) :=
  letI : Add (TwistedProduct b hb) := ⟨fun g k => ⟨g.pt + k.pt, g.sc + k.sc + b g.pt k.pt⟩⟩
  letI : Zero (TwistedProduct b hb) := ⟨⟨0, 0⟩⟩
  letI : Neg (TwistedProduct b hb) := ⟨fun g => ⟨-g.pt, -g.sc + b g.pt g.pt⟩⟩
  { AddGroup.ofLeftAxioms (G := TwistedProduct b hb)
      (fun x y z => TwistedProduct.ext (add_assoc _ _ _) (by
        show x.sc + y.sc + b x.pt y.pt + z.sc + b (x.pt + y.pt) z.pt =
          x.sc + (y.sc + z.sc + b y.pt z.pt) + b x.pt (y.pt + z.pt)
        simp only [map_add, AddMonoidHom.add_apply]; abel))
      (fun x => TwistedProduct.ext (zero_add _) (by
        show 0 + x.sc + b 0 x.pt = x.sc
        simp))
      (fun x => TwistedProduct.ext (neg_add_cancel _) (by
        show -x.sc + b x.pt x.pt + x.sc + b (-x.pt) x.pt = 0
        simp only [map_neg, AddMonoidHom.neg_apply]; abel)) with
    add_comm := fun x y => TwistedProduct.ext (add_comm _ _) (by
      show x.sc + y.sc + b x.pt y.pt = y.sc + x.sc + b y.pt x.pt
      rw [hb, add_comm x.sc]) }

/-- `ℂˣ` is an injective abelian group (it is divisible). -/
theorem baer_additiveUnits : Module.Baer ℤ (Additive ℂˣ) := by
  let : DivisibleBy (Additive ℂˣ) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn z => by
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (z.toMul : ℂ) (Nat.pos_of_ne_zero hn)
    have hw0 : w ≠ 0 := by
      rintro rfl
      exact z.toMul.ne_zero (by rw [← hw, zero_pow hn])
    exact ⟨Additive.ofMul (Units.mk0 w hw0), Additive.toMul.injective (Units.ext (by simpa using hw))⟩
  let := AddGroup.divisibleByIntOfDivisibleByNat (Additive ℂˣ)
  exact Module.Baer.of_divisible _

/-- On a self-orthogonal subgroup `A`, the cocycle `c` is split by a function `α` that is `1` on
a given subgroup `L ⊆ A` on which `c = 1`. -/
theorem exists_splitsOn (h : IsAlternatingBicharacter c) {L A : AddSubgroup W} (hLA : L ≤ A)
    (hL : ∀ x ∈ L, ∀ y ∈ L, c x y = 1) (hA : A ≤ h.orthogonal A) :
    ∃ α : W → ℂ, SplitsOn c A α ∧ ∀ x ∈ L, α x = 1 := by
  classical
  let b : A →+ A →+ Additive ℂˣ := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => Additive.ofMul (Units.mk0 (c x y) (h.ne_zero _ _)))
      fun y z => Additive.toMul.injective (Units.ext (by simp [h.map_add_right])))
    fun x y => by
      ext z
      simp [h.map_add_left]
  have hbv : ∀ x y, ((b x y).toMul : ℂ) = c x y := fun x y => rfl
  have hb : ∀ x y, b x y = b y x := fun x y => Additive.toMul.injective (Units.ext (by
    rw [hbv, hbv]
    exact mul_left_cancel₀ (h.ne_zero x y) (by rw [h.mul_swap, ← pow_two]; exact hA x.2 y y.2)))
  let f : L × Additive ℂˣ →+ TwistedProduct b hb :=
    AddMonoidHom.mk' (fun p => ⟨⟨p.1, hLA p.1.2⟩, p.2⟩) fun p q => TwistedProduct.ext rfl (by
      show p.2 + q.2 = p.2 + q.2 + b _ _
      rw [left_eq_add]
      exact Additive.toMul.injective (Units.ext (hL _ p.1.2 _ q.1.2)))
  have hf : Function.Injective f := fun p q hpq =>
    Prod.ext (Subtype.ext (congrArg (fun g : TwistedProduct b hb => g.pt.1) hpq))
      (congrArg TwistedProduct.sc hpq)
  obtain ⟨g, hg⟩ := baer_additiveUnits.extension_property_addMonoidHom f hf (AddMonoidHom.snd _ _)
  have hg' : ∀ p, g (f p) = p.2 := fun p => DFunLike.congr_fun hg p
  refine ⟨fun x => if hx : x ∈ A then ((g ⟨⟨x, hx⟩, 0⟩).toMul : ℂ) else 1,
    ⟨fun a ha => ?_, fun a ha a' ha' => ?_⟩, fun x hx => ?_⟩
  · simp [ha]
  · rw [dite_eq_left ha, dite_eq_left ha', dite_eq_left (A.add_mem ha ha')]
    have h1 : (⟨⟨a, ha⟩, 0⟩ + ⟨⟨a', ha'⟩, 0⟩ : TwistedProduct b hb) =
        f (0, b ⟨a, ha⟩ ⟨a', ha'⟩) + ⟨⟨a + a', A.add_mem ha ha'⟩, 0⟩ :=
      TwistedProduct.ext (Subtype.ext (zero_add _).symm) (by
        show 0 + 0 + b ⟨a, ha⟩ ⟨a', ha'⟩ = b ⟨a, ha⟩ ⟨a', ha'⟩ + 0 + b 0 _
        simp)
    have h2 := congrArg (fun t => ((g t).toMul : ℂ)) h1
    simpa only [map_add, toMul_add, Units.val_mul, hg', hbv] using h2
  · beta_reduce
    rw [dite_eq_left (hLA hx)]
    exact congrArg (fun t : Additive ℂˣ => (t.toMul : ℂ)) (hg' (⟨x, hx⟩, 0))

/-- Translation twisted by `c`: `(translate c x f) z = c z x * f (z + x)`. -/
def translate (c : W → W → ℂ) (x : W) : Module.End ℂ (W → ℂ) where
  toFun f z := c z x * f (z + x)
  map_add' f g := by funext z; simp [mul_add]
  map_smul' r f := by funext z; simp; ring

@[simp] theorem translate_apply (c : W → W → ℂ) (x : W) (f : W → ℂ) (z : W) :
    translate c x f z = c z x * f (z + x) := rfl

theorem isProjectiveRep_translate (h : IsAlternatingBicharacter c) :
    IsProjectiveRep c (translate c) where
  apply_zero v := by funext z; simp [h.zero_right]
  apply_apply x y v := by
    funext z; simp [h.map_add_left, h.map_add_right, add_assoc]; ring

theorem translate_indicator (hα : SplitsOn c A α) (a : W) (ha : a ∈ A) :
    translate c a ((A : Set W).indicator α) = α a • (A : Set W).indicator α := by
  funext z
  show c z a * (A : Set W).indicator α (z + a) = α a * (A : Set W).indicator α z
  by_cases hz : z ∈ A
  · rw [Set.indicator_of_mem (A.add_mem hz ha), Set.indicator_of_mem hz, mul_comm (α a),
      hα.mul z hz a ha]
  · have : z + a ∉ A := fun h => hz (by simpa using A.sub_mem h ha)
    simp [hz, this]

end Langlands.HeisenbergGroup.Internal
