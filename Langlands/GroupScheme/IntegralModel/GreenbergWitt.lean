import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.Algebra.Module.PID
import Mathlib.FieldTheory.Perfect

/-! # Witt-vector inputs for Greenberg rings

Truncated Witt vectors as a functor, the vanishing lemma which makes the Greenberg
coordinates well defined, the ghost-component ring map from Witt vectors of a perfect
residue field into a local ring with nilpotent maximal ideal, and coordinate data for a
finite torsion module over the Witt vectors.
-/

noncomputable section

universe u v

open WittVector

namespace Langlands.GroupScheme.IntegralModel.Greenberg

variable (p : ℕ) [hp : Fact p.Prime]

local notation "𝕎" => WittVector p

section TruncMap

variable {R S : Type*} [CommRing R] [CommRing S]

theorem truncate_map_eq_zero (m : ℕ) (f : R →+* S) {x : 𝕎 R}
    (hx : truncate m x = 0) : truncate m (map f x) = 0 := by
  rw [← RingHom.mem_ker, mem_ker_truncate] at hx ⊢
  intro i hi
  rw [map_coeff, hx i hi, map_zero]

/-- Truncated Witt vectors are functorial in the coefficient ring. -/
def truncMap (m : ℕ) (f : R →+* S) :
    TruncatedWittVector p m R →+* TruncatedWittVector p m S :=
  (truncate m).liftOfSurjective (truncate_surjective p m R)
    ⟨(truncate m).comp (map f), fun x hx => by
      rw [RingHom.mem_ker] at hx ⊢
      exact truncate_map_eq_zero p m f hx⟩

@[simp] theorem truncMap_truncate (m : ℕ) (f : R →+* S) (x : 𝕎 R) :
    truncMap p m f (truncate m x) = truncate m (map f x) :=
  RingHom.liftOfSurjective_comp_apply _ _ _ x

theorem truncMap_comp {U : Type*} [CommRing U] (m : ℕ) (f : R →+* S) (g : S →+* U)
    (x : TruncatedWittVector p m R) :
    truncMap p m g (truncMap p m f x) = truncMap p m (g.comp f) x := by
  obtain ⟨y, rfl⟩ := truncate_surjective p m R x
  rw [truncMap_truncate, truncMap_truncate, truncMap_truncate]
  congr 1

theorem truncMap_id (m : ℕ) (x : TruncatedWittVector p m R) :
    truncMap p m (RingHom.id R) x = x := by
  obtain ⟨y, rfl⟩ := truncate_surjective p m R x
  rw [truncMap_truncate, map_id]
  rfl

end TruncMap

section Vanishing

variable {k : Type u} [Field k] [CharP k p] [PerfectRing k p]

/-- **The vanishing lemma.** If `p ^ a * c` vanishes in `W_j(k)` and the first `a`
coefficients of `w ∈ W(T)` vanish, then `w * c` vanishes in `W_j(T)`. -/
theorem truncate_mul_map_eq_zero {T : Type*} [CommRing T] [Algebra k T] {a j : ℕ}
    {c : 𝕎 k} (hc : truncate j ((p : 𝕎 k) ^ a * c) = 0) {w : 𝕎 T}
    (hw : ∀ i < a, w.coeff i = 0) : truncate j (w * map (algebraMap k T) c) = 0 := by
  rcases subsingleton_or_nontrivial T with hT | hT
  · ext i
    exact Subsingleton.elim _ _
  have : CharP T p := charP_of_injective_algebraMap (algebraMap k T).injective p
  rw [← RingHom.mem_ker, mem_ker_truncate]
  rw [eq_iterate_verschiebung hw]
  by_cases haj : j ≤ a
  · intro i hi
    rw [iterate_verschiebung_mul_left]
    exact iterate_verschiebung_coeff_eq_zero _ (lt_of_lt_of_le hi haj)
  · rw [not_le] at haj
    have hmem : (p : 𝕎 k) ^ a * c ∈ Ideal.span {((p : 𝕎 k) ^ j)} := by
      rw [mem_span_p_pow_iff_le_coeff_eq_zero]
      rw [← RingHom.mem_ker, mem_ker_truncate] at hc
      exact hc
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hmem
    have hc' : c = (p : 𝕎 k) ^ (j - a) * d := by
      have hp0 : ((p : 𝕎 k) ^ a) ≠ 0 := pow_ne_zero _ (p_nonzero p k)
      apply mul_left_cancel₀ hp0
      rw [← hd, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' haj.le, mul_comm]
    rw [hc', map_mul, map_pow, map_natCast, mul_comm ((p : 𝕎 T) ^ (j - a)),
      ← iterate_verschiebung_iterate_frobenius, iterate_verschiebung_mul,
      Nat.add_sub_cancel' haj.le]
    intro i hi
    exact iterate_verschiebung_coeff_eq_zero _ hi

end Vanishing

section Ghost

variable {A : Type v} [CommRing A]

/-- The ghost components as explicit sums. -/
theorem ghostComponent_eq_sum (N : ℕ) (x : 𝕎 A) :
    ghostComponent N x =
      ∑ i ∈ Finset.range (N + 1), (p : A) ^ i * x.coeff i ^ p ^ (N - i) := by
  rw [ghostComponent_apply, wittPolynomial, MvPolynomial.aeval_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [MvPolynomial.aeval_monomial, map_pow]

/-- A ghost component of a Witt vector with coefficients in an ideal containing `p`. -/
theorem ghostComponent_mem_pow (I : Ideal A) (hpI : (p : A) ∈ I) (x : 𝕎 A)
    (hx : ∀ i, x.coeff i ∈ I) (N : ℕ) : ghostComponent N x ∈ I ^ (N + 1) := by
  rw [ghostComponent_eq_sum]
  refine Ideal.sum_mem _ fun i hi => ?_
  have hi' : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h1 : (p : A) ^ i ∈ I ^ i := Ideal.pow_mem_pow hpI i
  have h2 : x.coeff i ^ p ^ (N - i) ∈ I ^ (N - i + 1) := by
    apply Ideal.pow_le_pow_right (show N - i + 1 ≤ p ^ (N - i) from
      ((N - i).lt_two_pow_self).succ_le.trans (Nat.pow_le_pow_left hp.out.two_le _))
    exact Ideal.pow_mem_pow (hx i) _
  have := Ideal.mul_mem_mul h1 h2
  rwa [← pow_add, show i + (N - i + 1) = N + 1 by omega] at this

variable {k : Type u} [Field k] [CharP k p]

/-- Reducing a ghost component to a field of characteristic `p`. -/
theorem residue_ghostComponent (r : A →+* k) (x : 𝕎 A) (N : ℕ) :
    r (ghostComponent N x) = r (x.coeff 0) ^ p ^ N := by
  rw [ghostComponent_eq_sum, map_sum, Finset.sum_range_succ']
  simp [CharP.cast_eq_zero]

variable [PerfectRing k p] (r : A →+* k) (hr : Function.Surjective r) (N : ℕ)
  (hN : RingHom.ker r ^ (N + 1) = ⊥)

omit [PerfectRing k p] in
include hN in
theorem ghostComponent_eq_zero_of_map_eq_zero (x : 𝕎 A) (hx : map r x = 0) :
    ghostComponent N x = 0 := by
  have hpI : (p : A) ∈ RingHom.ker r := by
    rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
  have hxI : ∀ i, x.coeff i ∈ RingHom.ker r := by
    intro i
    rw [RingHom.mem_ker, ← map_coeff, hx, zero_coeff]
  have := ghostComponent_mem_pow p _ hpI x hxI N
  rwa [hN, Ideal.mem_bot] at this

/-- The ghost-component map before the Frobenius untwist. -/
def wittToLocal₀ : 𝕎 k →+* A :=
  (map r).liftOfSurjective (map_surjective r hr)
    ⟨ghostComponent N, fun x hx => by
      rw [RingHom.mem_ker] at hx ⊢
      exact ghostComponent_eq_zero_of_map_eq_zero p r N hN x hx⟩

/-- **The Witt-vector structure map.** A ring map `W(k) → A` into a ring whose residue
map onto the perfect field `k` has nilpotent kernel, normalized so that it lifts the
zeroth coefficient. -/
def wittToLocal : 𝕎 k →+* A :=
  (wittToLocal₀ p r hr N hN).comp (map ((iterateFrobeniusEquiv k p N).symm : k →+* k))

theorem residue_wittToLocal (w : 𝕎 k) : r (wittToLocal p r hr N hN w) = w.coeff 0 := by
  obtain ⟨x, hx⟩ := map_surjective r hr
    (map ((iterateFrobeniusEquiv k p N).symm : k →+* k) w)
  have h1 : wittToLocal p r hr N hN w = ghostComponent N x := by
    change wittToLocal₀ p r hr N hN (map _ w) = _
    rw [← hx]
    exact RingHom.liftOfSurjective_comp_apply _ _ _ x
  rw [h1, residue_ghostComponent, ← map_coeff, hx, map_coeff]
  change ((iterateFrobeniusEquiv k p N).symm (w.coeff 0)) ^ p ^ N = _
  rw [← iterateFrobeniusEquiv_def, RingEquiv.apply_symm_apply]

end Ghost

section Decomposition

variable {k : Type u} [Field k] [CharP k p] [PerfectRing k p] {A : Type u} [CommRing A]

/-- Cyclic coordinates of a finite torsion module over `W(k)`, presented by a ring map
`ψ : W(k) → A`: generators `e i` and `W(k)`-semilinear coordinate maps into truncated Witt
vectors of length `m i`, dual to the generators and determining every element. -/
structure WittDecomposition (ψ : 𝕎 k →+* A) where
  ι : Type u
  [fintype : Fintype ι]
  [decEq : DecidableEq ι]
  m : ι → ℕ
  e : ι → A
  coord : (i : ι) → A →+ TruncatedWittVector p (m i) k
  coord_mul : ∀ i (c : 𝕎 k) (a : A), coord i (ψ c * a) = truncate (m i) c * coord i a
  coord_e_self : ∀ i, coord i (e i) = 1
  coord_e_ne : ∀ i j, j ≠ i → coord i (e j) = 0
  eq_sum : ∀ (a : A) (c : ι → 𝕎 k), (∀ i, truncate (m i) (c i) = coord i a) →
    a = ∑ i, ψ (c i) * e i

attribute [instance] WittDecomposition.fintype WittDecomposition.decEq

variable {p}

theorem span_irreducible_pow_eq {q : 𝕎 k} (hq : Irreducible q) (n : ℕ) :
    Ideal.span {q ^ n} = Ideal.span {(p : 𝕎 k) ^ n} := by
  rw [Ideal.span_singleton_eq_span_singleton]
  exact (IsDiscreteValuationRing.associated_of_irreducible _ hq
    (WittVector.irreducible p)).pow_pow

theorem mem_ker_truncate_iff_mem_span (n : ℕ) (x : 𝕎 k) :
    truncate n x = 0 ↔ x ∈ Ideal.span {(p : 𝕎 k) ^ n} := by
  rw [mem_span_p_pow_iff_le_coeff_eq_zero, ← RingHom.mem_ker, mem_ker_truncate]

variable (p)

/-- **Existence of cyclic coordinates.** A finitely generated `W(k)`-module killed by a
power of `p` has a coordinate decomposition. -/
theorem nonempty_wittDecomposition (ψ : 𝕎 k →+* A) {σ : Type*} [Fintype σ] (g : σ → A)
    (hs : ∀ a, ∃ c : σ → 𝕎 k, a = ∑ x, ψ (c x) * g x) (M : ℕ) (hM : (p : A) ^ M = 0) :
    Nonempty (WittDecomposition p ψ) := by
  classical
  let _ : Algebra (𝕎 k) A := ψ.toAlgebra
  have hsmul : ∀ (c : 𝕎 k) (a : A), c • a = ψ c * a := fun c a => by
    rw [Algebra.smul_def]
    rfl
  have hfin : Module.Finite (𝕎 k) A := by
    refine ⟨⟨Finset.univ.image g, ?_⟩⟩
    rw [eq_top_iff]
    intro a _
    obtain ⟨c, rfl⟩ := hs a
    refine Submodule.sum_mem _ fun x _ => ?_
    rw [← hsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      (Finset.mem_coe.2 (Finset.mem_image_of_mem g (Finset.mem_univ x))))
  have htors : Module.IsTorsion (𝕎 k) A := by
    intro a
    refine ⟨⟨(p : 𝕎 k) ^ M, mem_nonZeroDivisors_of_ne_zero
      (pow_ne_zero _ (p_nonzero p k))⟩, ?_⟩
    change ((p : 𝕎 k) ^ M) • a = 0
    rw [hsmul, map_pow, map_natCast, hM, zero_mul]
  obtain ⟨ι, fι, q, hq, m, ⟨Φ⟩⟩ := Module.equiv_directSum_of_isTorsion htors
  have hle : ∀ i, Ideal.span {q i ^ m i} ≤ RingHom.ker (truncate (p := p) (R := k) (m i)) := by
    intro i x hx
    rw [span_irreducible_pow_eq (hq i)] at hx
    rw [RingHom.mem_ker, mem_ker_truncate_iff_mem_span]
    exact hx
  let L : (i : ι) → (𝕎 k ⧸ Ideal.span {q i ^ m i}) →+* TruncatedWittVector p (m i) k :=
    fun i => Ideal.Quotient.lift (Ideal.span {q i ^ m i}) (truncate (m i)) (hle i)
  let comp : (i : ι) → A →ₗ[𝕎 k] (𝕎 k ⧸ Ideal.span {q i ^ m i}) :=
    fun i => (DirectSum.component (𝕎 k) ι (fun i => 𝕎 k ⧸ (𝕎 k ∙ q i ^ m i)) i).comp
      Φ.toLinearMap
  have hL_inj : ∀ i (c : 𝕎 k) (y : 𝕎 k ⧸ Ideal.span {q i ^ m i}),
      truncate (m i) c = L i y → y = Ideal.Quotient.mk _ c := by
    intro i c y hy
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.eq]
    have : L i (Ideal.Quotient.mk _ z) = truncate (m i) z := Ideal.Quotient.lift_mk _ _ _
    rw [this] at hy
    rw [span_irreducible_pow_eq (hq i), ← mem_ker_truncate_iff_mem_span, map_sub, hy,
      sub_self]
  refine ⟨{
    ι := ι
    m := m
    e := fun i => Φ.symm (DirectSum.lof (𝕎 k) ι (fun i => 𝕎 k ⧸ (𝕎 k ∙ q i ^ m i)) i 1)
    coord := fun i => (L i).toAddMonoidHom.comp (comp i).toAddMonoidHom
    coord_mul := ?_
    coord_e_self := ?_
    coord_e_ne := ?_
    eq_sum := ?_ }⟩
  · intro i c a
    change L i (comp i (ψ c * a)) = truncate (m i) c * L i (comp i a)
    rw [← hsmul, LinearMap.map_smul]
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (comp i a)
    rw [← hz]
    change L i (Ideal.Quotient.mk _ (c * z)) = _
    rw [map_mul (Ideal.Quotient.mk _), map_mul]
    congr 1
  · intro i
    change L i (comp i (Φ.symm _)) = 1
    simp only [comp, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply, DirectSum.component.lof_self]
    exact map_one (L i)
  · intro i j hji
    change L i (comp i (Φ.symm _)) = 0
    simp only [comp, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply, DirectSum.component.of, hji, ↓reduceDIte]
    exact map_zero (L i)
  · intro a c hc
    have hcomp : ∀ i, comp i a = Ideal.Quotient.mk _ (c i) := fun i => hL_inj i _ _ (hc i)
    calc a = Φ.symm (Φ a) := (Φ.symm_apply_apply a).symm
      _ = Φ.symm (∑ i, DirectSum.lof (𝕎 k) ι (fun i => 𝕎 k ⧸ (𝕎 k ∙ q i ^ m i)) i
            (Ideal.Quotient.mk _ (c i))) := by
          congr 1
          conv_lhs => rw [← DirectSum.sum_univ_of (Φ a)]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← hcomp i]
          rfl
      _ = ∑ i, ψ (c i) *
            Φ.symm (DirectSum.lof (𝕎 k) ι (fun i => 𝕎 k ⧸ (𝕎 k ∙ q i ^ m i)) i 1) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← hsmul, ← LinearEquiv.map_smul, ← LinearMap.map_smul]
          congr 2
          change Submodule.Quotient.mk (c i) = c i • Submodule.Quotient.mk 1
          rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]

end Decomposition

end Langlands.GroupScheme.IntegralModel.Greenberg
