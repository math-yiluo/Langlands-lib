import Langlands.CommutativeAlgebra.DVRWeightedLeadingTerm
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced

/-! # Integrality of points of a positively graded algebra over a DVR

Let `B` be a finitely generated algebra over a field `k`, with a `ℤ`-grading given by a coaction
`c : B → B[T, T⁻¹]` and a counit `ε : B → k`. A point `a : B → R` is a *contracting point* when
it kills the components of negative weight and agrees with `ε` on the components of weight `0`;
these are the points of the dynamic unipotent subgroup when `B` is the coordinate ring of an
affine group and `c` is the conjugation coaction of a cocharacter.

Let `A` be a DVR over `k` with geometrically reduced residue field, and assume that every
nonzero finitely generated geometrically reduced `k`-algebra has a `k`-point. Let `M ⊆ B` be
stable under taking homogeneous components, such that the only contracting `k`-point that agrees
with `ε` on `M` is `ε`. Then a contracting point `ξ : B → Frac A` taking values in `A` on `M`
takes all its values in `A`.
-/

noncomputable section

universe u

open MvPolynomial IsLocalRing

namespace Langlands.CommutativeAlgebra

namespace GradedDVRIntegrality

section Grading

variable (k : Type*) [Field k] {B : Type*} [CommRing B] [Algebra k B]

/-- A coaction `c : B → B[T, T⁻¹]` is a grading of the `k`-algebra `B`: it fixes the scalars,
the components `c(b)ₙ` of every `b` sum to `b`, and `c(b)ₙ` is homogeneous of weight `n`. -/
structure IsGrading (c : B →+* LaurentPolynomial B) : Prop where
  map_algebraMap : ∀ r : k, c (algebraMap k B r) = LaurentPolynomial.C (algebraMap k B r)
  sum_coeff : ∀ b, ((c b).coeff.sum fun _ a => a) = b
  coeff_coeff : ∀ b n, c ((c b).coeff n) = AddMonoidAlgebra.single n ((c b).coeff n)

variable {k}

/-- A point `a : B → R` contracts to the counit `ε`: it kills the components of negative weight
and agrees with `ε` on the components of weight `0`. -/
def IsContracting (c : B →+* LaurentPolynomial B) (ε : B →ₐ[k] k) {R : Type*} [CommRing R]
    [Algebra k R] (a : B →ₐ[k] R) : Prop :=
  (∀ b, ∀ n < 0, a ((c b).coeff n) = 0) ∧ ∀ b, a ((c b).coeff 0) = algebraMap k R (ε b)

/-- The ideal cut out by the contracting points. -/
def contractingIdeal (c : B →+* LaurentPolynomial B) (ε : B →ₐ[k] k) : Ideal B :=
  Ideal.span ({d | ∃ b, ∃ n < 0, (c b).coeff n = d} ∪
    {d | ∃ b, (c b).coeff 0 - algebraMap k B (ε b) = d})

theorem isContracting_iff (c : B →+* LaurentPolynomial B) (ε : B →ₐ[k] k) {R : Type*}
    [CommRing R] [Algebra k R] (a : B →ₐ[k] R) :
    IsContracting c ε a ↔ ∀ y ∈ contractingIdeal c ε, a y = 0 := by
  have hle : ∀ s : Set B, (∀ y ∈ Ideal.span s, a y = 0) ↔ ∀ y ∈ s, a y = 0 := by
    intro s
    refine ⟨fun h y hy => h y (Ideal.subset_span hy), fun h y hy => ?_⟩
    have : Ideal.span s ≤ RingHom.ker a.toRingHom :=
      Ideal.span_le.2 fun y hy => RingHom.mem_ker.2 (h y hy)
    exact RingHom.mem_ker.1 (this hy)
  rw [contractingIdeal, hle]
  constructor
  · rintro ⟨hn, h0⟩ y (⟨b, n, hn', rfl⟩ | ⟨b, rfl⟩)
    · exact hn b n hn'
    · rw [map_sub, h0, AlgHom.commutes, sub_self]
  · intro h
    refine ⟨fun b n hn => h _ (Or.inl ⟨b, n, hn, rfl⟩), fun b => ?_⟩
    have := h _ (Or.inr ⟨b, rfl⟩)
    rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this

variable {c : B →+* LaurentPolynomial B}

/-- The coefficients of `c(r * y)` are combinations of those of `c(y)`. -/
theorem coeff_mul_mem (r y : B) (I : Ideal B) (hy : ∀ n, (c y).coeff n ∈ I) (n : ℤ) :
    (c (r * y)).coeff n ∈ I := by
  classical
  rw [map_mul]
  have hr : c r = ∑ m ∈ (c r).coeff.support, AddMonoidAlgebra.single m ((c r).coeff m) := by
    apply AddMonoidAlgebra.coeff_injective
    rw [AddMonoidAlgebra.coeff_sum]
    simp only [AddMonoidAlgebra.coeff_single]
    exact (Finsupp.sum_single _).symm
  rw [hr, Finset.sum_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Ideal.sum_mem _ fun m _ => ?_
  rw [AddMonoidAlgebra.coeff_single_mul_apply]
  exact I.mul_mem_left _ (hy _)

variable (hc : IsGrading k c) (ε : B →ₐ[k] k)
include hc

/-- The contracting ideal is stable under taking homogeneous components. -/
theorem coeff_mem_contractingIdeal {y : B} (hy : y ∈ contractingIdeal c ε) (n : ℤ) :
    (c y).coeff n ∈ contractingIdeal c ε := by
  classical
  induction hy using Submodule.span_induction generalizing n with
  | mem d hd =>
    rcases hd with ⟨b, m, hm, rfl⟩ | ⟨b, rfl⟩
    · rw [hc.coeff_coeff, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      split_ifs
      · exact Ideal.subset_span (Or.inl ⟨b, m, hm, rfl⟩)
      · exact zero_mem _
    · rw [map_sub, hc.coeff_coeff, hc.map_algebraMap, ← LaurentPolynomial.single_eq_C,
        ← AddMonoidAlgebra.single_sub, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      split_ifs
      · exact Ideal.subset_span (Or.inr ⟨b, rfl⟩)
      · exact zero_mem _
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact add_mem (hy n) (hz n)
  | smul r y _ hy =>
    rw [smul_eq_mul]
    exact coeff_mul_mem r y _ hy n

/-- Homogeneity of the image of a polynomial in homogeneous elements of positive weight. -/
theorem coeff_aeval {ι : Type*} (x : ι → B) (w : ι → ℕ)
    (hx : ∀ i, c (x i) = AddMonoidAlgebra.single (w i : ℤ) (x i)) (P : MvPolynomial ι k)
    (n : ℤ) :
    (c (aeval x P)).coeff n =
      if 0 ≤ n then aeval x (weightedHomogeneousComponent w n.toNat P) else 0 := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u r =>
    have hmon : c (aeval x (monomial u r)) =
        AddMonoidAlgebra.single (Finsupp.weight w u : ℤ) (aeval x (monomial u r)) := by
      rw [aeval_monomial, map_mul, hc.map_algebraMap, map_finsuppProd]
      simp only [map_pow, hx, AddMonoidAlgebra.single_pow]
      rw [AddMonoidAlgebra.finsuppProd_single, ← LaurentPolynomial.single_eq_C,
        AddMonoidAlgebra.single_mul_single, zero_add]
      congr 1
      simp only [Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum, nsmul_eq_mul, smul_eq_mul,
        Nat.cast_mul]
    rw [hmon, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hw : (Finsupp.weight w u : ℤ) = n
    · rw [ite_eq_left hw, ite_eq_left (hw ▸ Int.natCast_nonneg _)]
      have : n.toNat = Finsupp.weight w u := by rw [← hw, Int.toNat_natCast]
      rw [this, (isWeightedHomogeneous_monomial w u r rfl).weightedHomogeneousComponent_same]
    · rw [ite_eq_right hw]
      split_ifs with hn
      · rw [(isWeightedHomogeneous_monomial w u r rfl).weightedHomogeneousComponent_ne, map_zero]
        intro h
        apply hw
        rw [← h, Int.toNat_of_nonneg hn]
      · rfl
  | add p q hp hq =>
    rw [map_add, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
    split_ifs <;> simp

end Grading

/-- **Integrality of a contracting point.** Let `B` be a finitely generated `k`-algebra graded by
`c`, with counit `ε`, and `M ⊆ B` a subset stable under homogeneous components such that the
only contracting `k`-point agreeing with `ε` on `M` is `ε`. Let `A` be a DVR over `k` with
geometrically reduced residue field, and assume that every nonzero finitely generated
geometrically reduced `k`-algebra in `Type u` has a `k`-point. Then a contracting point
`ξ : B → Frac A` with `ξ(M) ⊆ A` satisfies `ξ(B) ⊆ A`. -/
theorem integral_of_contracting {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B]
    [hB : Algebra.FiniteType k B] {c : B →+* LaurentPolynomial B} (hc : IsGrading k c)
    (ε : B →ₐ[k] k) (hε : ∀ b n, ε ((c b).coeff n) = if n = 0 then ε b else 0)
    (M : Set B) (hM : ∀ m ∈ M, ∀ n, (c m).coeff n ∈ M)
    (hker : ∀ a : B →ₐ[k] k, IsContracting c ε a → (∀ m ∈ M, a m = ε m) → a = ε)
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra k A]
    (hF : Algebra.IsGeometricallyReduced k (ResidueField A))
    (hrat : ∀ (R : Type u) [CommRing R] [Algebra k R] [Algebra.FiniteType k R] [Nontrivial R]
      [Algebra.IsGeometricallyReduced k R], Nonempty (R →ₐ[k] k))
    (ξ : B →ₐ[k] FractionRing A) (hξ : IsContracting c ε ξ)
    (hint : ∀ m ∈ M, ξ m ∈ (algebraMap A (FractionRing A)).range) :
    ∀ b, ξ b ∈ (algebraMap A (FractionRing A)).range := by
  classical
  by_contra hcon
  obtain ⟨s, hs⟩ := hB.out
  set I := contractingIdeal c ε with hI
  have hεI : ∀ y ∈ I, ε y = 0 := by
    refine (isContracting_iff c ε ε).1 ⟨fun b n hn => ?_, fun b => ?_⟩
    · rw [hε, ite_eq_right hn.ne]
    · rw [hε, ite_eq_left rfl]
      rfl
  have hξI : ∀ y ∈ I, ξ y = 0 := (isContracting_iff c ε ξ).1 hξ
  -- Homogeneous generators of positive weight.
  let ι := Σ b : s, ((c b).coeff.support.filter (0 < ·) : Finset ℤ)
  let x : ι → B := fun i => (c i.1).coeff i.2
  let w : ι → ℕ := fun i => (i.2 : ℤ).toNat
  have hwpos : ∀ i : ι, 0 < (i.2 : ℤ) := fun i => (Finset.mem_filter.1 i.2.2).2
  have hw : ∀ i : ι, 0 < w i := fun i => Int.lt_toNat.2 (hwpos i)
  have hwz : ∀ i : ι, (w i : ℤ) = i.2 := fun i => Int.toNat_of_nonneg (hwpos i).le
  have hx : ∀ i, c (x i) = AddMonoidAlgebra.single (w i : ℤ) (x i) := fun i => by
    rw [hwz]
    exact hc.coeff_coeff _ _
  -- Every element is congruent modulo `I` to a polynomial in the generators.
  have hgen : ∀ b, ∃ P : MvPolynomial ι k, b - aeval x P ∈ I := by
    intro b
    have hb : b ∈ Algebra.adjoin k (s : Set B) := hs ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem b hb =>
      refine ⟨C (ε b) + ∑ n : ((c b).coeff.support.filter (0 < ·) : Finset ℤ),
        X ⟨⟨b, hb⟩, n⟩, ?_⟩
      have hsum : aeval x (∑ n : ((c b).coeff.support.filter (0 < ·) : Finset ℤ),
          (X ⟨⟨b, hb⟩, n⟩ : MvPolynomial ι k)) =
          ∑ n ∈ (c b).coeff.support.filter (0 < ·), (c b).coeff n := by
        rw [map_sum]
        simp only [aeval_X]
        exact Finset.sum_coe_sort _ (fun n => (c b).coeff n)
      rw [map_add, aeval_C, hsum]
      have hb' : b = ∑ n ∈ (c b).coeff.support, (c b).coeff n := (hc.sum_coeff b).symm
      have hsplit := Finset.sum_filter_add_sum_filter_not (c b).coeff.support (0 < ·)
        (fun n => (c b).coeff n)
      have hsplit' := Finset.sum_filter_add_sum_filter_not
        ((c b).coeff.support.filter (¬ 0 < ·)) (· < 0) (fun n => (c b).coeff n)
      have hzero : ∑ n ∈ ((c b).coeff.support.filter (¬ 0 < ·)).filter (¬ · < 0),
          (c b).coeff n = (c b).coeff 0 := by
        apply Finset.sum_eq_single
        · intro n hn hn0
          simp only [Finset.mem_filter] at hn
          omega
        · intro h0
          by_contra hne
          exact h0 (by simp [Finsupp.mem_support_iff, hne])
      have hneg : ∑ n ∈ ((c b).coeff.support.filter (¬ 0 < ·)).filter (· < 0),
          (c b).coeff n ∈ I := by
        refine Ideal.sum_mem _ fun n hn => Ideal.subset_span (Or.inl ⟨b, n, ?_, rfl⟩)
        exact (Finset.mem_filter.1 hn).2
      have h0 : (c b).coeff 0 - algebraMap k B (ε b) ∈ I :=
        Ideal.subset_span (Or.inr ⟨b, rfl⟩)
      have e : b = ∑ n ∈ (c b).coeff.support.filter (0 < ·), (c b).coeff n +
          (∑ n ∈ ((c b).coeff.support.filter (¬ 0 < ·)).filter (· < 0), (c b).coeff n +
            (c b).coeff 0) := by
        rw [← hzero, hsplit', hsplit]
        exact hb'
      have : b - (algebraMap k B (ε b) + ∑ n ∈ (c b).coeff.support.filter (0 < ·), (c b).coeff n)
          = ∑ n ∈ ((c b).coeff.support.filter (¬ 0 < ·)).filter (· < 0), (c b).coeff n +
            ((c b).coeff 0 - algebraMap k B (ε b)) := by
        calc _ = (∑ n ∈ (c b).coeff.support.filter (0 < ·), (c b).coeff n +
              (∑ n ∈ ((c b).coeff.support.filter (¬ 0 < ·)).filter (· < 0), (c b).coeff n +
                (c b).coeff 0)) -
              (algebraMap k B (ε b) + ∑ n ∈ (c b).coeff.support.filter (0 < ·), (c b).coeff n) := by
              rw [← e]
          _ = _ := by ring
      rw [this]
      exact add_mem hneg h0
    | algebraMap r => exact ⟨C r, by rw [aeval_C, sub_self]; exact zero_mem _⟩
    | add b b' _ _ hb hb' =>
      obtain ⟨P, hP⟩ := hb
      obtain ⟨P', hP'⟩ := hb'
      refine ⟨P + P', ?_⟩
      rw [map_add]
      convert add_mem hP hP' using 1
      ring
    | mul b b' _ _ hb hb' =>
      obtain ⟨P, hP⟩ := hb
      obtain ⟨P', hP'⟩ := hb'
      refine ⟨P * P', ?_⟩
      rw [map_mul]
      have : b * b' - aeval x P * aeval x P' =
          b' * (b - aeval x P) + aeval x P * (b' - aeval x P') := by ring
      rw [this]
      exact add_mem (I.mul_mem_left _ hP) (I.mul_mem_left _ hP')
  -- The polynomial equations.
  let S : Set (MvPolynomial ι k) :=
    {P | (∃ d : ℕ, 0 < d ∧ P.IsWeightedHomogeneous w d) ∧
      (aeval x P ∈ I ∨ ∃ y ∈ M, y - aeval x P ∈ I)}
  let K := FractionRing A
  let ξx : ι → K := fun i => ξ (x i)
  have hξP : ∀ P : MvPolynomial ι k, ξ (aeval x P) = aeval ξx P := fun P =>
    comp_aeval_apply (R := k) x ξ P
  let S' : Set (MvPolynomial ι A) := (MvPolynomial.map (algebraMap k A)) '' S
  have hS' : ∀ g ∈ S', ∃ d : ℕ, 0 < d ∧ g.IsWeightedHomogeneous w d := by
    rintro g ⟨P, ⟨⟨d, hd, hPd⟩, -⟩, rfl⟩
    refine ⟨d, hd, fun {m} hm => ?_⟩
    rw [coeff_map] at hm
    exact hPd fun h => hm (by rw [h, map_zero])
  have hint' : ∀ g ∈ S', aeval ξx g ∈ (algebraMap A K).range := by
    rintro g ⟨P, ⟨-, hP⟩, rfl⟩
    rw [aeval_map_algebraMap, ← hξP]
    rcases hP with hP | ⟨y, hy, hyP⟩
    · rw [hξI _ hP]
      exact zero_mem _
    · have : ξ (aeval x P) = ξ y - ξ (y - aeval x P) := by rw [map_sub]; ring
      rw [this, hξI _ hyP, sub_zero]
      exact hint y hy
  have hξ' : ¬ ∀ i, ξx i ∈ (algebraMap A K).range := by
    intro hall
    apply hcon
    intro b
    obtain ⟨P, hP⟩ := hgen b
    choose y hy using hall
    have : ξ b = algebraMap A K (aeval y P) := by
      have hb : ξ b = ξ (b - aeval x P) + ξ (aeval x P) := by rw [map_sub]; ring
      rw [hb, hξI _ hP, zero_add, hξP, ← aeval_algebraMap_apply,
        show ξx = ⇑(algebraMap A K) ∘ y from funext fun i => (hy i).symm]
    exact ⟨_, this.symm⟩
  obtain ⟨abar, habar, hzero⟩ :=
    DVRWeightedLeadingTerm.exists_ne_zero_forall_aeval_eq_zero w hw S' hS' ξx hint' hξ'
  have hzero' : ∀ P ∈ S, aeval abar P = 0 := by
    intro P hP
    have := hzero _ ⟨P, hP, rfl⟩
    rwa [aeval_map_algebraMap] at this
  -- A rational point of the subalgebra generated by `abar` and an inverse.
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp habar
  let sR : Set (ResidueField A) := insert (abar i0)⁻¹ (Set.range abar)
  have hsR : sR.Finite := (Set.finite_range abar).insert _
  let R := Algebra.adjoin k sR
  have : Algebra.FiniteType k R := Algebra.FiniteType.adjoin_of_finite hsR
  have : Algebra.IsGeometricallyReduced k R :=
    Algebra.IsGeometricallyReduced.of_injective R.val Subtype.val_injective
  obtain ⟨ψ⟩ := hrat R
  let abar' : ι → R := fun i =>
    ⟨abar i, Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨i, rfl⟩)⟩
  let inv' : R := ⟨(abar i0)⁻¹, Algebra.subset_adjoin (Set.mem_insert _ _)⟩
  let a : ι → k := fun i => ψ (abar' i)
  have ha : ∀ P ∈ S, aeval a P = 0 := by
    intro P hP
    have hR : aeval abar' P = 0 := by
      apply Subtype.val_injective
      have := comp_aeval_apply (R := k) abar' R.val P
      simp only [Subalgebra.coe_val] at this
      rw [Subalgebra.coe_zero, this]
      exact hzero' P hP
    change aeval (fun i => ψ (abar' i)) P = 0
    rw [← comp_aeval_apply, hR, map_zero]
  have hai0 : a i0 ≠ 0 := by
    have hmul : abar' i0 * inv' = 1 := Subtype.ext (mul_inv_cancel₀ hi0)
    intro h
    have := congrArg ψ hmul
    rw [map_mul, map_one] at this
    change a i0 * ψ inv' = 1 at this
    rw [h, zero_mul] at this
    exact zero_ne_one this
  -- `a` is a common zero of the whole kernel of the presentation.
  have haker : ∀ P : MvPolynomial ι k, aeval x P ∈ I → aeval a P = 0 := by
    intro P hP
    have hcomp : ∀ d : ℕ, aeval a (weightedHomogeneousComponent w d P) = 0 := by
      intro d
      have hmem : aeval x (weightedHomogeneousComponent w d P) ∈ I := by
        have := coeff_mem_contractingIdeal hc ε hP (d : ℤ)
        rwa [coeff_aeval hc x w hx, ite_eq_left (Int.natCast_nonneg d), Int.toNat_natCast] at this
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · rw [weightedHomogeneousComponent_zero _ fun i => (hw i).ne'] at hmem ⊢
        rw [aeval_C] at hmem ⊢
        have := hεI _ hmem
        rw [AlgHom.commutes] at this
        rw [this]
      · exact ha _ ⟨⟨d, hd, weightedHomogeneousComponent_isWeightedHomogeneous _ _⟩,
          Or.inl hmem⟩
    have hsum := (aeval a).toLinearMap.toAddMonoidHom.map_finsum
      (weightedHomogeneousComponent_finsupp (w := w) P)
    rw [sum_weightedHomogeneousComponent] at hsum
    change aeval a P = _ at hsum
    rw [hsum]
    exact finsum_eq_zero_of_forall_eq_zero fun d => hcomp d
  -- The corresponding contracting `k`-point of `B`.
  let φ : MvPolynomial ι k →ₐ[k] B ⧸ I := (Ideal.Quotient.mkₐ k I).comp (aeval x)
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mkₐ_surjective k I z
    obtain ⟨P, hP⟩ := hgen b
    refine ⟨P, ?_⟩
    change Ideal.Quotient.mk I (aeval x P) = Ideal.Quotient.mk I b
    rw [Ideal.Quotient.eq]
    rw [← neg_mem_iff, neg_sub]
    exact hP
  have hkerφ : RingHom.ker φ ≤ RingHom.ker (aeval a) := by
    intro P hP
    rw [RingHom.mem_ker] at hP ⊢
    apply haker
    change Ideal.Quotient.mk I (aeval x P) = 0 at hP
    exact Ideal.Quotient.eq_zero_iff_mem.1 hP
  let ev : (MvPolynomial ι k ⧸ RingHom.ker φ) →ₐ[k] k :=
    Ideal.Quotient.liftₐ (RingHom.ker φ) (aeval a) fun P hP => hkerφ hP
  let atil : B →ₐ[k] k :=
    (ev.comp (Ideal.quotientKerAlgEquivOfSurjective hφ).symm.toAlgHom).comp
      (Ideal.Quotient.mkₐ k I)
  have hatilI : ∀ y ∈ I, atil y = 0 := by
    intro y hy
    change ev ((Ideal.quotientKerAlgEquivOfSurjective hφ).symm (Ideal.Quotient.mk I y)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hy, map_zero, map_zero]
  have hatilP : ∀ P : MvPolynomial ι k, atil (aeval x P) = aeval a P := by
    intro P
    change ev ((Ideal.quotientKerAlgEquivOfSurjective hφ).symm (φ P)) = _
    rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
    rfl
  have hatil : IsContracting c ε atil := (isContracting_iff c ε atil).2 hatilI
  -- It agrees with `ε` on `M`.
  have hatilM : ∀ m ∈ M, atil m = ε m := by
    intro m hm
    have hn : ∀ n, atil ((c m).coeff n) = ε ((c m).coeff n) := by
      intro n
      rcases lt_trichotomy n 0 with hn | rfl | hn
      · rw [hatil.1 m n hn, hε, ite_eq_right hn.ne]
      · rw [hatil.2 m, hε, ite_eq_left rfl]
        rfl
      · rw [hε, ite_eq_right hn.ne']
        set y := (c m).coeff n
        obtain ⟨P', hP'⟩ := hgen y
        set P := weightedHomogeneousComponent w n.toNat P'
        have hyP : y - aeval x P ∈ I := by
          have h1 := coeff_mem_contractingIdeal hc ε hP' n
          rw [map_sub, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_aeval hc x w hx,
            ite_eq_left hn.le, hc.coeff_coeff, AddMonoidAlgebra.coeff_single,
            Finsupp.single_eq_same] at h1
          exact h1
        have hPS : P ∈ S := by
          refine ⟨⟨n.toNat, Int.lt_toNat.2 hn,
            weightedHomogeneousComponent_isWeightedHomogeneous _ _⟩, Or.inr ⟨y, hM m hm n, hyP⟩⟩
        have : atil y = atil (y - aeval x P) + atil (aeval x P) := by rw [map_sub]; ring
        rw [this, hatilI _ hyP, hatilP, ha P hPS, add_zero]
    have hsum := hc.sum_coeff m
    conv_lhs => rw [← hsum]
    conv_rhs => rw [← hsum]
    rw [map_finsuppSum, map_finsuppSum]
    exact Finsupp.sum_congr fun n _ => hn n
  have heq := hker atil hatil hatilM
  apply hai0
  have hx0 : ε (x i0) = 0 := by
    change ε ((c i0.1).coeff i0.2) = 0
    rw [hε, ite_eq_right (hwpos i0).ne']
  rw [← hx0, ← heq, ← aeval_X (R := k) x i0, hatilP, aeval_X]

end GradedDVRIntegrality

end Langlands.CommutativeAlgebra
