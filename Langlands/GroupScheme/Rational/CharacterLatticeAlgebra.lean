import Mathlib

/-! # Commutative algebra for the finiteness of rational character lattices

Algebraic facts behind the finiteness of the rational characters of a smooth connected affine
group over a field `k`, stated for abstract algebras.

* `linearIndepOn_of_comul`: elements `a` of a `k`-vector space `O` with `Δ a = a ⊗ a` for a
  `k`-linear map `Δ : O → O ⊗ O`, and `a ≠ 0`, are linearly independent.
* `free_and_finite`: let `w : M → L` be a multiplicative map from an abelian group `M` to a
  field `L` over `k`, with `k`-linearly independent values, all lying in a finitely generated
  `k`-subalgebra of `L`. Then `M` is a free `ℤ`-module of finite rank.
-/

noncomputable section

open TensorProduct Function

namespace Langlands.GroupScheme.CharacterLattice

section Comul

variable {k O : Type*} [Field k] [AddCommGroup O] [Module k O]

/-- Nonzero elements `a` with `Δ a = a ⊗ a` for a linear map `Δ : O → O ⊗ O` are linearly
independent. This is Mathlib's `linearIndepOn_isGroupLikeElem`, whose proof uses only these two
properties of group-like elements. -/
theorem linearIndepOn_of_comul (Δ : O →ₗ[k] O ⊗[k] O) {S : Set O}
    (hS : ∀ a ∈ S, Δ a = a ⊗ₜ a) (h0 : ∀ a ∈ S, a ≠ 0) : LinearIndepOn k id S := by
  classical
  open Submodule in
  rw [linearIndepOn_iff_linearIndepOn_finset]
  rintro s hs
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
  simp only [Finset.cons_eq_insert, Finset.coe_insert, Set.insert_subset_iff] at hs
  obtain ⟨ha, hs⟩ := hs
  specialize ih hs
  rw [Finset.coe_cons]
  refine ih.id_insert' ?_
  simp only [Submodule.mem_span_finset, forall_exists_index, and_imp]
  rintro d c - hc
  replace ih := ih.tmul_of_isDomain ih
  simp_rw [← Finset.coe_product, linearIndepOn_finset_iffₛ, id] at ih
  have key := calc
        ∑ x ∈ s, ∑ y ∈ s, (if x = y then d * c x else 0) • x ⊗ₜ[k] y
    _ = d • ∑ x ∈ s, c x • x ⊗ₜ[k] x := by simp [Finset.smul_sum, mul_smul]
    _ = d • Δ (d • a) := by
        rw [← hc, map_sum]
        congr 1
        exact Finset.sum_congr rfl fun x hx => by rw [map_smul, hS x (hs (Finset.mem_coe.mpr hx))]
    _ = (d • a) ⊗ₜ (d • a) := by simp [hS a ha, smul_tmul, tmul_smul, -neg_smul]
    _ = ∑ x ∈ s, ∑ y ∈ s, (c x * c y) • x ⊗ₜ[k] y := by
      simp_rw [← hc, sum_tmul, smul_tmul, Finset.smul_sum, tmul_sum, tmul_smul, mul_smul]
  simp_rw [← Finset.sum_product'] at key
  apply ih at key
  replace key x (hx : x ∈ s) : c x = 0 := by
    by_contra! hcx
    have hcy (y) (hys : y ∈ s) (hyx : y ≠ x) : c y = 0 := by
      simpa [*] using (key (y, x) (by simp [*])).symm
    rw [Finset.sum_eq_single x (by simp +contextual [hcy]) (by simp [hx])] at hc
    have hcxa : d = c x := mul_left_injective₀ hcx (by simpa using (key (x, x) (by simp [*])))
    obtain rfl : x = a := by rwa [hcxa, smul_right_inj hcx] at hc
    contradiction
  simp_all [h0 a ha, eq_comm]

end Comul

section Lattice

variable {k L M : Type*} [Field k] [Field L] [Algebra k L] [AddCommGroup M]
  (w : Multiplicative M →* L)

/-- `w` as a function on the additive group `M`. -/
abbrev wa (m : M) : L := w (Multiplicative.ofAdd m)

theorem wa_add (a b : M) : wa w (a + b) = wa w a * wa w b := by
  simp [wa, ofAdd_add]

theorem wa_zero : wa w (0 : M) = 1 := by
  simp [wa]

theorem wa_nsmul (n : ℕ) (m : M) : wa w (n • m) = wa w m ^ n := by
  simp [wa, ofAdd_nsmul]

theorem wa_sum {ι : Type*} (s : Finset ι) (f : ι → M) :
    wa w (∑ i ∈ s, f i) = ∏ i ∈ s, wa w (f i) := by
  simp [wa, ofAdd_sum]

/-- A group `M` mapped multiplicatively, with `k`-linearly independent values, into a field (or
any domain) has no torsion: if `m` has order `d`, then `∑_{j<d} w(m)^j = 0`. -/
theorem isAddTorsionFree (hw : LinearIndependent k (wa w)) : IsAddTorsionFree M := by
  classical
  refine IsAddTorsionFree.of_not_isOfFinAddOrder fun m hm hfin => ?_
  set d := addOrderOf m
  have hd : 0 < d := hfin.addOrderOf_pos
  have hu1 : wa w m ≠ 1 := by
    intro h
    apply hm
    apply hw.injective
    rw [h, wa_zero]
  have hsum : ∑ j ∈ Finset.range d, wa w m ^ j = 0 := by
    have : (∑ j ∈ Finset.range d, wa w m ^ j) * (wa w m - 1) = 0 := by
      rw [geom_sum_mul, ← wa_nsmul, addOrderOf_nsmul_eq_zero, wa_zero, sub_self]
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hu1)
  rw [linearIndependent_iff'] at hw
  have hinj : Set.InjOn (fun j : ℕ => j • m) (Finset.range d : Set ℕ) := by
    rw [Finset.coe_range]
    exact nsmul_injOn_Iio_addOrderOf
  refine one_ne_zero (hw ((Finset.range d).image fun j : ℕ => j • m) (fun _ => (1 : k)) ?_ 0
    (Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hd, zero_smul _ _⟩))
  rw [Finset.sum_image hinj]
  simpa [wa_nsmul] using hsum

/-- The `k`-span of the values of `w` on a subgroup `P` is closed under multiplication, so it
contains the `k`-subalgebra they generate. -/
theorem mem_span_of_mem_adjoin (P : AddSubgroup M) {x : L}
    (hx : x ∈ Algebra.adjoin k (wa w '' P)) : x ∈ Submodule.span k (wa w '' P) := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact Submodule.subset_span hx
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, ← wa_zero w]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨0, P.zero_mem, rfl⟩)
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy =>
    have h := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a + b, P.add_mem ha hb, wa_add w a b⟩

/-- Representatives of distinct cosets of `P` are linearly independent over the algebra
generated by `w(P)`. -/
theorem linearIndependent_out_adjoin (hw : LinearIndependent k (wa w)) (P : AddSubgroup M) :
    LinearIndependent (Algebra.adjoin k (wa w '' P))
      (fun c : M ⧸ P => wa w (Quotient.out c)) := by
  classical
  rw [linearIndependent_iff']
  intro t g hg c hc
  have hmem : ∀ c : M ⧸ P, ∃ l ∈ Finsupp.supported k k (P : Set M),
      Finsupp.linearCombination k (wa w) l = (g c : L) := fun c =>
    (Finsupp.mem_span_image_iff_linearCombination k).mp (mem_span_of_mem_adjoin w P (g c).2)
  choose l hlP hlw using hmem
  have key : ∀ (c' : M ⧸ P) (q : M),
      ((l c').mapDomain (· + Quotient.out c')) (q + Quotient.out c') = l c' q := fun c' q =>
    Finsupp.mapDomain_apply_of_injective (add_left_injective _) _ _
  set T : M →₀ k := ∑ c ∈ t, (l c).mapDomain (· + Quotient.out c)
  have hT : Finsupp.linearCombination k (wa w) T = 0 := by
    rw [← hg]
    simp only [T, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finsupp.linearCombination_mapDomain, Subalgebra.smul_def, smul_eq_mul, ← hlw c,
      Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum_mul]
    refine Finsupp.sum_congr fun p _ => ?_
    simp only [Function.comp_apply, wa_add, smul_mul_assoc]
  have hT0 : T = 0 := linearIndependent_iff.mp hw T hT
  have hl0 : l c = 0 := by
    ext p
    by_cases hp : p ∈ P
    · have h := congrArg (fun f : M →₀ k => f (p + Quotient.out c)) hT0
      simp only [T, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_zero,
        Pi.zero_apply] at h
      rw [Finset.sum_eq_single c, key] at h
      · simpa using h
      · intro c' _ hc'
        rw [show p + Quotient.out c = (p + Quotient.out c - Quotient.out c') + Quotient.out c' by
          abel, key]
        by_contra hne
        have hq : p + Quotient.out c - Quotient.out c' ∈ P :=
          (Finsupp.mem_supported k _).mp (hlP c') (Finsupp.mem_support_iff.mpr hne)
        apply hc'
        have h1 : (QuotientAddGroup.mk (Quotient.out c') : M ⧸ P) =
            QuotientAddGroup.mk (Quotient.out c) := by
          rw [QuotientAddGroup.eq]
          have : -Quotient.out c' + Quotient.out c =
              (p + Quotient.out c - Quotient.out c') - p := by abel
          rw [this]
          exact P.sub_mem hq hp
        rwa [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at h1
      · intro h'
        exact absurd hc h'
    · by_contra hne
      exact hp ((Finsupp.mem_supported k _).mp (hlP c) (Finsupp.mem_support_iff.mpr hne))
  apply Subtype.ext
  rw [← hlw c, hl0, map_zero]
  rfl

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- Representatives of distinct cosets of `P` are linearly independent over the field generated
by `w(P)`. -/
theorem linearIndependent_out_field (hw : LinearIndependent k (wa w)) (P : AddSubgroup M) :
    LinearIndependent (IntermediateField.adjoin k (wa w '' P))
      (fun c : M ⧸ P => wa w (Quotient.out c)) :=
  (LinearIndependent.iff_fractionRing (Algebra.adjoin k (wa w '' P))
    (IntermediateField.adjoin k (wa w '' P))).mp (linearIndependent_out_adjoin w hw P)

/-- If every element of `M` has a positive multiple in `P` and the values of `w` lie in a
finitely generated `k`-subalgebra of `L`, then `M ⧸ P` is finite. With `K` the field generated by
`w(P)` and `B` the `K`-algebra generated by the generators, the coset representatives give
`K`-linearly independent elements of `B` that are algebraic over `K`; they stay independent in a
residue field `B ⧸ 𝔪`, which is finite over `K` by Zariski's lemma. -/
theorem finite_quotient (hw : LinearIndependent k (wa w)) (P : AddSubgroup M)
    (htors : ∀ m : M, ∃ n : ℕ, 0 < n ∧ n • m ∈ P) (g : Finset L)
    (hg : ∀ m : M, wa w m ∈ Algebra.adjoin k (g : Set L)) : Finite (M ⧸ P) := by
  classical
  set K := IntermediateField.adjoin k (wa w '' P)
  set B : Subalgebra K L := Algebra.adjoin K (g : Set L)
  have hB : ∀ m : M, wa w m ∈ B := by
    intro m
    have hle : Algebra.adjoin k (g : Set L) ≤ B.restrictScalars k :=
      Algebra.adjoin_le (Algebra.subset_adjoin (R := K))
    exact hle (hg m)
  have hint : ∀ m : M, IsIntegral K (wa w m) := by
    intro m
    obtain ⟨n, hn, hnP⟩ := htors m
    refine (IsAlgebraic.of_pow hn ?_).isIntegral
    rw [← wa_nsmul]
    have hK : wa w (n • m) ∈ K := IntermediateField.subset_adjoin k _ ⟨_, hnP, rfl⟩
    exact (isAlgebraic_algebraMap (⟨_, hK⟩ : K) : IsAlgebraic K (algebraMap K L ⟨_, hK⟩))
  have : Algebra.FiniteType K B := Algebra.FiniteType.adjoin_of_finite g.finite_toSet
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal B
  let := Ideal.Quotient.field 𝔪
  have : Algebra.FiniteType K (B ⧸ 𝔪) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K 𝔪)
      (Ideal.Quotient.mkₐ_surjective K 𝔪)
  have : Module.Finite K (B ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing K (B ⧸ 𝔪)
  set u : M ⧸ P → B := fun c => ⟨wa w (Quotient.out c), hB _⟩
  have hu : LinearIndependent K u :=
    LinearIndependent.of_comp B.val.toLinearMap (linearIndependent_out_field w hw P)
  have hspan : ∀ x ∈ Submodule.span K (Set.range u), (x : L) ∈ integralClosure K L := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      exact hint _
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul r x _ hx => exact Subalgebra.smul_mem _ hx r
  have hdisj : Disjoint (Submodule.span K (Set.range u))
      (LinearMap.ker (Ideal.Quotient.mkₐ K 𝔪).toLinearMap) := by
    rw [Submodule.disjoint_def]
    intro x hx hx𝔪
    by_contra hx0
    have hxL : (x : L) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hinv : (x : L)⁻¹ ∈ B :=
      B.inv_mem_of_algebraic (hspan x hx).isAlgebraic
    have h1 : x * ⟨_, hinv⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hxL)
    have hx𝔪' : x ∈ 𝔪 := by
      simpa [LinearMap.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hx𝔪
    exact h𝔪.ne_top ((Ideal.eq_top_iff_one _).mpr (h1 ▸ 𝔪.mul_mem_right _ hx𝔪'))
  exact (hu.map hdisj).finite

/-- If the values of `w` lie in a finitely generated `k`-subalgebra `A` of `L`, then every
`ℤ`-linearly independent subset `S` of `M` is finite: the values of `w` on `S` are algebraically
independent over `k` (monomials go to values of `w` at distinct elements of `M`), so `#S` is at
most the transcendence degree of `A`, which is finite. -/
theorem finite_of_linearIndepOn (hw : LinearIndependent k (wa w)) (g : Finset L)
    (hg : ∀ m : M, wa w m ∈ Algebra.adjoin k (g : Set L)) {S : Set M}
    (hS : LinearIndepOn ℤ id S) : S.Finite := by
  classical
  set A := Algebra.adjoin k (g : Set L)
  set μ : (S →₀ ℕ) → M := fun e =>
    Finsupp.linearCombination ℤ (fun s : S => (s : M)) (Finsupp.mapRange (Nat.cast : ℕ → ℤ)
      Nat.cast_zero e)
  have hμ : Injective μ :=
    (show Injective (Finsupp.linearCombination ℤ (fun s : S => (s : M))) from hS).comp
      (Finsupp.mapRange_injective _ Nat.cast_zero Nat.cast_injective)
  have hwμ : ∀ e, wa w (μ e) = e.prod fun s n => wa w s ^ n := by
    intro e
    simp only [μ, Finsupp.linearCombination_apply]
    rw [Finsupp.sum_mapRange_index (h := fun (i : S) (a : ℤ) => a • (i : M))
      (fun _ => zero_smul _ _), Finsupp.sum, wa_sum, Finsupp.prod]
    simp [natCast_zsmul, wa_nsmul]
  have key : ∀ p : MvPolynomial S k, MvPolynomial.aeval (fun s : S => wa w s) p =
      Finsupp.linearCombination k (wa w) (Finsupp.mapDomain μ p.coeff) := by
    intro p
    induction p using MvPolynomial.induction_on' with
    | monomial u a =>
      rw [MvPolynomial.aeval_monomial, ← MvPolynomial.single_eq_monomial,
        AddMonoidAlgebra.coeff_single, Finsupp.mapDomain_single,
        Finsupp.linearCombination_single, hwμ, Algebra.smul_def]
    | add p q hp hq =>
      rw [map_add, hp, hq, AddMonoidAlgebra.coeff_add, Finsupp.mapDomain_add, map_add]
  have hind : AlgebraicIndependent k (fun s : S => wa w s) := by
    rw [algebraicIndependent_iff_injective_aeval]
    intro p q hpq
    have h := hpq
    rw [key, key] at h
    exact AddMonoidAlgebra.coeff_injective (Finsupp.mapDomain_injective hμ (hw h))
  have hind' : AlgebraicIndependent k (fun s : S => (⟨wa w s, hg s⟩ : A)) :=
    AlgebraicIndependent.of_comp A.val hind
  have : Algebra.FiniteType k A := Algebra.FiniteType.adjoin_of_finite g.finite_toSet
  have hlt := hind'.lift_cardinalMk_le_trdeg.trans_lt
    (Cardinal.lift_lt_aleph0.mpr (trdeg_lt_aleph0_of_finiteType (R := k) (S := A)))
  rw [Cardinal.lift_lt_aleph0, Cardinal.mk_lt_aleph0_iff] at hlt
  exact Set.toFinite S

/-- A group `M` with a multiplicative map `w` to a field `L` over `k`, whose values are
`k`-linearly independent and lie in a finitely generated `k`-subalgebra of `L`, is a free
`ℤ`-module of finite rank. A maximal `ℤ`-linearly independent subset `S` of `M` is finite, the
quotient by its span is torsion, hence finite, so `M` is finitely generated; it is torsion-free,
hence free. -/
theorem free_and_finite (hw : LinearIndependent k (wa w)) (g : Finset L)
    (hg : ∀ m : M, wa w m ∈ Algebra.adjoin k (g : Set L)) :
    Module.Free ℤ M ∧ Module.Finite ℤ M := by
  classical
  obtain ⟨S, hS, hmax⟩ := exists_maximal_linearIndepOn ℤ (id : M → M)
  rw [Set.image_id] at hmax
  have hSfin : S.Finite := finite_of_linearIndepOn w hw g hg hS
  set P : AddSubgroup M := (Submodule.span ℤ S).toAddSubgroup
  have htors : ∀ m : M, ∃ n : ℕ, 0 < n ∧ n • m ∈ P := by
    intro m
    by_cases hm : m ∈ S
    · exact ⟨1, one_pos, by rw [one_smul]; exact Submodule.subset_span (R := ℤ) hm⟩
    · obtain ⟨a, ha, haS⟩ := hmax m hm
      refine ⟨a.natAbs, Int.natAbs_pos.mpr ha, ?_⟩
      change a.natAbs • m ∈ Submodule.span ℤ S
      rw [← natCast_zsmul]
      rcases Int.natAbs_eq a with h | h
      · rwa [← h]
      · rw [show ((a.natAbs : ℤ)) = -a by omega, neg_smul]
        exact neg_mem haS
  have : Finite (M ⧸ P) := finite_quotient w hw P htors g hg
  have hfin : Module.Finite ℤ M := by
    rw [Module.finite_def, Submodule.fg_def]
    refine ⟨S ∪ Set.range (Quotient.out : M ⧸ P → M), hSfin.union (Set.finite_range _), ?_⟩
    rw [eq_top_iff]
    intro m _
    have hq : -Quotient.out (QuotientAddGroup.mk m : M ⧸ P) + m ∈ P := by
      rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
    have hm : m = Quotient.out (QuotientAddGroup.mk m : M ⧸ P) +
        (-Quotient.out (QuotientAddGroup.mk m : M ⧸ P) + m) := by abel
    rw [hm]
    refine add_mem (Submodule.subset_span (Or.inr ⟨_, rfl⟩)) ?_
    exact Submodule.span_mono Set.subset_union_left hq
  have := isAddTorsionFree w hw
  exact ⟨inferInstance, hfin⟩

end Lattice


end Langlands.GroupScheme.CharacterLattice
