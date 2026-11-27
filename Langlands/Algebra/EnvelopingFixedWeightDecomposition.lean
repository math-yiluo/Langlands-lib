import Langlands.Algebra.EnvelopingFixedWeightDecompositionStatement
import Langlands.Algebra.OrderedPBWBasis
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Fin

/-! # Fixed points of a weight-scaling automorphism of an enveloping algebra -/

noncomputable section

universe u v

set_option autoImplicit false

namespace Langlands.Algebra.UniversalEnveloping

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L]

local notation "U" => UniversalEnvelopingAlgebra k L
local notation "ι" => UniversalEnvelopingAlgebra.ι k


section Products

variable {A : Type*} [Ring A] [Algebra k A]

/-- Scalars pulled out of an ordered product. -/
theorem ofFn_prod_smul : ∀ {n : ℕ} (a : Fin n → k) (x : Fin n → A),
    (List.ofFn fun i => a i • x i).prod = (∏ i, a i) • (List.ofFn x).prod
  | 0, _, _ => by simp
  | n + 1, a, x => by
    rw [List.ofFn_succ, List.prod_cons, ofFn_prod_smul (fun i => a i.succ) (fun i => x i.succ),
      List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ, smul_mul_smul_comm]

/-- An ordered product of powers with a positive-weight letter begins with a positive-weight
letter, for weights decreasing along the order. -/
theorem ofFn_prod_pow_mem_span_of_pos : ∀ {n : ℕ} (x : Fin n → A) (d : Fin n → ℤ),
    Antitone d → ∀ (e : Fin n → ℕ), (∃ i, e i ≠ 0 ∧ 0 < d i) →
      (List.ofFn fun i => x i ^ e i).prod ∈
        Submodule.span k {u | ∃ a, 0 < d a ∧ ∃ v : A, u = x a * v}
  | 0, _, _, _, _, ⟨i, _⟩ => i.elim0
  | n + 1, x, d, hd, e, ⟨i, hei, hdi⟩ => by
    rw [List.ofFn_succ, List.prod_cons]
    by_cases he0 : e 0 = 0
    · rw [he0, pow_zero, one_mul]
      induction i using Fin.cases with
      | zero => exact absurd he0 hei
      | succ j =>
        have hd' : Antitone (fun i : Fin n => d i.succ) :=
          hd.comp_monotone (Fin.strictMono_succ.monotone)
        refine Submodule.span_mono ?_ (ofFn_prod_pow_mem_span_of_pos (fun i => x i.succ)
          (fun i => d i.succ) hd' (fun i => e i.succ) ⟨j, hei, hdi⟩)
        rintro u ⟨a, ha, v, rfl⟩
        exact ⟨a.succ, ha, v, rfl⟩
    · have h0 : 0 < d 0 := lt_of_lt_of_le hdi (hd (Fin.zero_le i))
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero he0
      rw [hm, pow_succ', mul_assoc]
      exact Submodule.subset_span ⟨0, h0, _, rfl⟩

/-- An ordered product of powers of letters with indices in `p` lies in the subalgebra they
generate. -/
theorem ofFn_prod_pow_mem_adjoin : ∀ {n : ℕ} (x : Fin n → A) (p : Fin n → Prop) (e : Fin n → ℕ),
    (∀ i, e i ≠ 0 → p i) →
      (List.ofFn fun i => x i ^ e i).prod ∈ Algebra.adjoin k {u | ∃ a, p a ∧ u = x a}
  | 0, _, _, _, _ => by simp
  | n + 1, x, p, e, h => by
    rw [List.ofFn_succ, List.prod_cons]
    refine Subalgebra.mul_mem _ ?_ ?_
    · by_cases he0 : e 0 = 0
      · rw [he0, pow_zero]
        exact Subalgebra.one_mem _
      · exact Subalgebra.pow_mem _ (Algebra.subset_adjoin
          (show x 0 ∈ {u | ∃ a, p a ∧ u = x a} from ⟨0, h 0 he0, rfl⟩)) _
    · refine Algebra.adjoin_mono ?_ (ofFn_prod_pow_mem_adjoin (fun i => x i.succ)
        (fun i => p i.succ) (fun i => e i.succ) fun i hi => h i.succ hi)
      rintro u ⟨a, ha, rfl⟩
      exact ⟨a.succ, ha, rfl⟩

/-- If the total weight vanishes and no letter of positive weight occurs, every occurring letter
has weight zero. -/
theorem weight_eq_zero_of_sum_eq_zero {n : ℕ} (d : Fin n → ℤ) (e : Fin n → ℕ)
    (hsum : ∑ i, (e i : ℤ) * d i = 0) (hpos : ¬ ∃ i, e i ≠ 0 ∧ 0 < d i) :
    ∀ i, e i ≠ 0 → d i = 0 := by
  push Not at hpos
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin n)), (e i : ℤ) * d i ≤ 0 := by
    intro i _
    by_cases hei : e i = 0
    · simp [hei]
    · exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hpos i hei)
  have hzero := (Finset.sum_eq_zero_iff_of_nonpos hle).mp hsum
  intro i hei
  have hi := hzero i (Finset.mem_univ i)
  rcases mul_eq_zero.mp hi with h | h
  · exact absurd (by exact_mod_cast h) hei
  · exact h

end Products

section Basis

variable {n : ℕ} (b : Module.Basis (Fin n) k L)

/-- The ordered Poincaré–Birkhoff–Witt basis of the enveloping algebra. -/
def orderedPBWBasisOf : Module.Basis (Fin n → ℕ) k U :=
  Module.Basis.mk (orderedPBWBasis.{u, v} k L n b).1 (orderedPBWBasis.{u, v} k L n b).2.ge

theorem orderedPBWBasisOf_apply (e : Fin n → ℕ) :
    orderedPBWBasisOf b e = orderedPBWMonomial b e :=
  Module.Basis.mk_apply _ _ _

/-- The weight of an exponent vector. -/
def monomialWeight (d : Fin n → ℤ) (e : Fin n → ℕ) : ℤ := ∑ i, (e i : ℤ) * d i

theorem prod_units_zpow (c : kˣ) : ∀ {m : ℕ} (w : Fin m → ℤ), ∏ i, c ^ w i = c ^ ∑ i, w i
  | 0, _ => by simp
  | m + 1, w => by
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ, prod_units_zpow c (fun i => w i.succ), zpow_add]

variable (d : Fin n → ℤ) (c : kˣ)

/-- An algebra endomorphism scaling each generator `ι(b a)` by `c ^ d a` scales each ordered
monomial by `c` to the power of its weight. -/
theorem map_orderedPBWMonomial (φ : U →ₐ[k] U)
    (hφ : ∀ a, φ (ι (b a)) = ((c ^ d a : kˣ) : k) • ι (b a)) (e : Fin n → ℕ) :
    φ (orderedPBWMonomial b e) = ((c ^ monomialWeight d e : kˣ) : k) • orderedPBWMonomial b e := by
  rw [orderedPBWMonomial, map_list_prod, List.map_ofFn]
  have h : (φ ∘ fun i => ι (b i) ^ e i) =
      fun i => ((c ^ d i : kˣ) : k) ^ e i • ι (b i) ^ e i := by
    funext i
    simp only [Function.comp_apply, map_pow, hφ, smul_pow]
  rw [h, ofFn_prod_smul]
  congr 1
  have hpow (i : Fin n) : ((c ^ d i : kˣ) : k) ^ e i = ((c ^ ((e i : ℤ) * d i) : kˣ) : k) := by
    rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul, mul_comm]
  simp_rw [hpow]
  rw [← Units.coe_prod, prod_units_zpow]
  rfl

/-- The coordinates of an image under such an endomorphism. -/
theorem orderedPBWBasisOf_repr_map (φ : U →ₐ[k] U)
    (hφ : ∀ a, φ (ι (b a)) = ((c ^ d a : kˣ) : k) • ι (b a)) (z : U) (e : Fin n → ℕ) :
    (orderedPBWBasisOf b).repr (φ z) e =
      ((c ^ monomialWeight d e : kˣ) : k) * (orderedPBWBasisOf b).repr z e := by
  have h : (orderedPBWBasisOf b).coord e ∘ₗ φ.toLinearMap =
      ((c ^ monomialWeight d e : kˣ) : k) • (orderedPBWBasisOf b).coord e := by
    refine (orderedPBWBasisOf b).ext fun f => ?_
    change (orderedPBWBasisOf b).coord e (φ (orderedPBWBasisOf b f)) =
      ((c ^ monomialWeight d e : kˣ) : k) • (orderedPBWBasisOf b).coord e (orderedPBWBasisOf b f)
    rw [orderedPBWBasisOf_apply, map_orderedPBWMonomial b d c φ hφ, ← orderedPBWBasisOf_apply,
      map_smul]
    obtain rfl | hne := eq_or_ne f e
    · rfl
    · have h0 : (orderedPBWBasisOf b).coord e (orderedPBWBasisOf b f) = 0 := by
        rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne' hne]
      rw [h0, smul_zero, smul_zero]
  exact LinearMap.congr_fun h z

/-- Fixed points of a weight-scaling endomorphism, for weights decreasing along the basis order:
every fixed element lies in the sum of the positive-weight right span and the weight-zero
subalgebra. -/
theorem mem_sup_of_fixed_of_antitone (hd : Antitone d) (hc : ∀ m : ℤ, c ^ m = 1 → m = 0)
    (φ : U →ₐ[k] U) (hφ : ∀ a, φ (ι (b a)) = ((c ^ d a : kˣ) : k) • ι (b a))
    (z : U) (hz : φ z = z) :
    z ∈ positiveWeightGeneratorSpan (k := k) b d ⊔
      (zeroWeightGeneratorSubalgebra (k := k) b d).toSubmodule := by
  let B := orderedPBWBasisOf b
  have hsupport (e : Fin n → ℕ) (he : e ∈ (B.repr z).support) : monomialWeight d e = 0 := by
    have h := orderedPBWBasisOf_repr_map b d c φ hφ z e
    rw [hz] at h
    have h' : (((c ^ monomialWeight d e : kˣ) : k) - 1) * B.repr z e = 0 := by
      rw [sub_mul, ← h, one_mul, sub_self]
    have hne := Finsupp.mem_support_iff.mp he
    have h1 := sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hne)
    exact hc _ (Units.val_eq_one.mp h1)
  rw [← B.linearCombination_repr z, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun e he => Submodule.smul_mem _ _ ?_
  rw [orderedPBWBasisOf_apply, orderedPBWMonomial]
  by_cases hpos : ∃ i, e i ≠ 0 ∧ 0 < d i
  · exact Submodule.mem_sup_left (ofFn_prod_pow_mem_span_of_pos _ d hd e hpos)
  · exact Submodule.mem_sup_right
      (ofFn_prod_pow_mem_adjoin (k := k) _ (fun a => d a = 0) e
        (weight_eq_zero_of_sum_eq_zero d e (hsupport e he) hpos))

end Basis

section ListProducts

/-- Removing factors equal to one from a product. -/
theorem list_prod_map_filter {α M : Type*} [Monoid M] (p : α → Bool) (g : α → M) :
    ∀ l : List α, (∀ a ∈ l, p a = false → g a = 1) →
      (l.map g).prod = ((l.filter p).map g).prod
  | [], _ => rfl
  | a :: l, h => by
    have ih := list_prod_map_filter p g l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    cases ha : p a
    · simp [ha, h a List.mem_cons_self ha, ih]
    · simp [ha, ih]

/-- Filtering `finRange n` by the range of an order embedding gives the image of `finRange m`. -/
theorem filter_finRange_range {n m : ℕ} (ψ : Fin m ↪o Fin n) :
    (List.finRange n).filter (fun i => decide (i ∈ Set.range ψ)) = (List.finRange m).map ψ := by
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·))
  · exact (List.pairwise_lt_finRange n).filter _
  · exact List.pairwise_map.mpr ((List.pairwise_lt_finRange m).imp fun h => ψ.strictMono h)
  · intro i
    simp [List.mem_filter, List.mem_map, List.mem_finRange]

/-- An ordered product of powers whose exponents vanish off the range of an order embedding is
the ordered product along that embedding. -/
theorem ofFn_prod_pow_orderEmbedding {A : Type*} [Monoid A] {n m : ℕ} (ψ : Fin m ↪o Fin n)
    (x : Fin n → A) (e : Fin n → ℕ) (he : ∀ i, i ∉ Set.range ψ → e i = 0) :
    (List.ofFn fun i => x i ^ e i).prod = (List.ofFn fun j => x (ψ j) ^ e (ψ j)).prod := by
  rw [List.ofFn_eq_map, List.ofFn_eq_map,
    list_prod_map_filter (fun i => decide (i ∈ Set.range ψ)) _ _ (fun i _ hi => by
      rw [he i (by simpa using hi), pow_zero]),
    filter_finRange_range, List.map_map]
  rfl

/-- An ordered product of powers splits along exponents whose supports are ordered. -/
theorem ofFn_prod_pow_add {A : Type*} [Monoid A] : ∀ {n : ℕ} (x : Fin n → A) (e₁ e₂ : Fin n → ℕ),
    (∀ i j, e₁ i ≠ 0 → e₂ j ≠ 0 → i < j) →
      (List.ofFn fun i => x i ^ (e₁ i + e₂ i)).prod =
        (List.ofFn fun i => x i ^ e₁ i).prod * (List.ofFn fun i => x i ^ e₂ i).prod
  | 0, _, _, _, _ => by simp
  | n + 1, x, e₁, e₂, h => by
    by_cases h2 : e₂ 0 = 0
    · have ih := ofFn_prod_pow_add (fun i => x i.succ) (fun i => e₁ i.succ) (fun i => e₂ i.succ)
        (fun i j hi hj => Fin.succ_lt_succ_iff.mp (h i.succ j.succ hi hj))
      simp only [List.ofFn_succ, List.prod_cons, h2, add_zero, pow_zero, one_mul, ih, mul_assoc]
    · have h1 : ∀ i, e₁ i = 0 := fun i => by
        by_contra hi
        exact absurd (h i 0 hi h2) (Fin.not_lt_zero i)
      simp only [h1, zero_add, pow_zero, List.ofFn_const, List.prod_replicate, one_pow, one_mul]

end ListProducts

section Uniqueness

variable {n : ℕ} (b : Module.Basis (Fin n) k L)

/-- Coordinates of an element of the span of some basis vectors vanish off those vectors. -/
theorem repr_eq_zero_of_mem_span {ι' M : Type*} [AddCommGroup M] [Module k M]
    (B : Module.Basis ι' k M) (E : Set ι') {y : M} (hy : y ∈ Submodule.span k (B '' E))
    {e : ι'} (he : e ∉ E) : B.repr y e = 0 := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    have hne : f ≠ e := fun h => he (h ▸ hf)
    rw [Module.Basis.repr_self, Finsupp.single_eq_of_ne' hne]
  | zero => rw [map_zero, Finsupp.zero_apply]
  | add x y _ _ h₁ h₂ => rw [map_add, Finsupp.add_apply, h₁, h₂, add_zero]
  | smul t x _ h => rw [map_smul, Finsupp.smul_apply, h, smul_zero]

variable (p : Fin n → Prop) [DecidablePred p]

/-- The Lie subalgebra spanned by the basis vectors with indices in `p`, for a set of indices
closed under brackets. -/
def basisSpanLieSubalgebra
    (hp : ∀ a a', p a → p a' → ⁅b a, b a'⁆ ∈ Submodule.span k (b '' {i | p i})) :
    LieSubalgebra k L :=
  { Submodule.span k (b '' {i | p i}) with
    lie_mem' := by
      intro x y hx hy
      change ⁅x, y⁆ ∈ Submodule.span k (b '' {i | p i})
      change x ∈ Submodule.span k (b '' {i | p i}) at hx
      change y ∈ Submodule.span k (b '' {i | p i}) at hy
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨a', ha', rfl⟩ := hy
          exact hp a a' ha ha'
        | zero => rw [lie_zero]; exact Submodule.zero_mem _
        | add y y' _ _ h₁ h₂ => rw [lie_add]; exact Submodule.add_mem _ h₁ h₂
        | smul t y _ h => rw [lie_smul]; exact Submodule.smul_mem _ t h
      | zero => rw [zero_lie]; exact Submodule.zero_mem _
      | add x x' _ _ h₁ h₂ => rw [add_lie]; exact Submodule.add_mem _ h₁ h₂
      | smul t x _ h => rw [smul_lie]; exact Submodule.smul_mem _ t h }

variable (hp : ∀ a a', p a → p a' → ⁅b a, b a'⁆ ∈ Submodule.span k (b '' {i | p i}))

/-- The increasing enumeration of the indices satisfying `p`. -/
def indexEmbedding : Fin (Finset.univ.filter p).card ↪o Fin n :=
  (Finset.univ.filter p).orderEmbOfFin rfl

theorem range_indexEmbedding : Set.range (indexEmbedding p) = {i | p i} := by
  rw [indexEmbedding, Finset.range_orderEmbOfFin]
  ext i
  simp

theorem range_basis_indexEmbedding :
    Set.range (fun j => b (indexEmbedding p j)) = b '' {i | p i} := by
  rw [← range_indexEmbedding p, ← Set.range_comp]
  rfl

/-- The basis of the Lie subalgebra spanned by the basis vectors with indices in `p`. -/
def basisSpanLieSubalgebraBasis :
    Module.Basis (Fin (Finset.univ.filter p).card) k (basisSpanLieSubalgebra b p hp) :=
  (Module.Basis.span (b.linearIndependent.comp _ (indexEmbedding p).injective)).map
    (LinearEquiv.ofEq _ (basisSpanLieSubalgebra b p hp).toSubmodule
      (range_basis_indexEmbedding b p ▸ rfl))

theorem basisSpanLieSubalgebraBasis_apply (j : Fin (Finset.univ.filter p).card) :
    (basisSpanLieSubalgebraBasis b p hp j : L) = b (indexEmbedding p j) := by
  simp only [basisSpanLieSubalgebraBasis, Module.Basis.map_apply, Module.Basis.span_apply]
  rfl

include hp in
/-- The subalgebra generated by the generators with indices in a bracket-closed set of indices is
spanned by the ordered monomials in those generators. -/
theorem adjoin_le_span_orderedPBWBasisOf :
    (Algebra.adjoin k {u | ∃ a, p a ∧ u = ι (b a)}).toSubmodule ≤
      Submodule.span k ((orderedPBWBasisOf b) '' {e | ∀ i, e i ≠ 0 → p i}) := by
  let S := basisSpanLieSubalgebra b p hp
  let bS := basisSpanLieSubalgebraBasis b p hp
  let ψ := indexEmbedding p
  let φ : UniversalEnvelopingAlgebra k S →ₐ[k] U :=
    UniversalEnvelopingAlgebra.lift k ((UniversalEnvelopingAlgebra.ι k).comp S.incl)
  have hφ (j : Fin (Finset.univ.filter p).card) :
      φ (UniversalEnvelopingAlgebra.ι k (bS j)) = ι (b (ψ j)) := by
    simp only [φ, UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.comp_apply,
      LieSubalgebra.coe_incl]
    rw [basisSpanLieSubalgebraBasis_apply]
  have hle : Algebra.adjoin k {u | ∃ a, p a ∧ u = ι (b a)} ≤ φ.range := by
    rw [Algebra.adjoin_le_iff]
    rintro u ⟨a, ha, rfl⟩
    refine (AlgHom.mem_range φ).mpr ⟨UniversalEnvelopingAlgebra.ι k
      (⟨b a, Submodule.subset_span ⟨a, ha, rfl⟩⟩ : S), ?_⟩
    simp only [φ, UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.comp_apply,
      LieSubalgebra.coe_incl]
  intro x hx
  obtain ⟨y, rfl⟩ := (AlgHom.mem_range φ).mp (hle hx)
  clear hx
  have hy : y ∈ Submodule.span k (Set.range (orderedPBWMonomial bS)) := by
    rw [(orderedPBWBasis.{u, v} k S _ bS).2]
    trivial
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, rfl⟩ := hx
    let e : Fin n → ℕ := Function.extend ψ f 0
    have he_apply (j : Fin (Finset.univ.filter p).card) : e (ψ j) = f j :=
      ψ.injective.extend_apply f 0 j
    have he_zero (i : Fin n) (hi : i ∉ Set.range ψ) : e i = 0 := by
      simp only [e]
      rw [Function.extend_apply' _ _ _ (fun ⟨j, hj⟩ => hi ⟨j, hj⟩)]
      rfl
    refine Submodule.subset_span ⟨e, fun i hi => ?_, ?_⟩
    · by_contra hpi
      have hnot : i ∉ Set.range ψ := by
        rw [show ψ = indexEmbedding p from rfl, range_indexEmbedding]
        exact hpi
      exact hi (he_zero i hnot)
    · rw [orderedPBWBasisOf_apply, orderedPBWMonomial, orderedPBWMonomial, map_list_prod,
        List.map_ofFn, ofFn_prod_pow_orderEmbedding ψ _ e he_zero]
      congr 1
      refine congrArg List.ofFn (funext fun j => ?_)
      simp only [Function.comp_apply, map_pow, hφ, he_apply]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  | smul t x _ h => rw [map_smul]; exact Submodule.smul_mem _ t h

end Uniqueness

section Weights

variable {n : ℕ} (b : Module.Basis (Fin n) k L) (d : Fin n → ℤ) (c : kˣ)
  (hc : ∀ m : ℤ, c ^ m = 1 → m = 0)
  (T : L →ₗ⁅k⁆ L) (hT : ∀ a, T (b a) = ((c ^ d a : kˣ) : k) • b a)

include hT in
theorem repr_lieHom_apply (x : L) (i : Fin n) :
    b.repr (T x) i = ((c ^ d i : kˣ) : k) * b.repr x i := by
  have h : b.coord i ∘ₗ T.toLinearMap = ((c ^ d i : kˣ) : k) • b.coord i := by
    refine b.ext fun j => ?_
    change b.coord i (T (b j)) = ((c ^ d i : kˣ) : k) • b.coord i (b j)
    rw [hT, map_smul]
    obtain rfl | hne := eq_or_ne j i
    · rfl
    · have h0 : b.coord i (b j) = 0 := by
        rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne' hne]
      rw [h0, smul_zero, smul_zero]
  exact LinearMap.congr_fun h x

include hc hT in
/-- An eigenvector of `T` with eigenvalue `c ^ m` lies in the span of the basis vectors of
weight `m`. -/
theorem mem_span_of_eigen (m : ℤ) (x : L) (hx : T x = ((c ^ m : kˣ) : k) • x) :
    x ∈ Submodule.span k (b '' {i | d i = m}) := by
  rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  have h := repr_lieHom_apply b d c T hT x i
  rw [hx, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
  have hne := Finsupp.mem_support_iff.mp hi
  have heq : ((c ^ m : kˣ) : k) = ((c ^ d i : kˣ) : k) := mul_right_cancel₀ hne h
  have hdi : d i = m := by
    have h1 : c ^ (d i - m) = 1 := by
      rw [zpow_sub, ← Units.val_inj.mp heq, mul_inv_cancel]
    exact (sub_eq_zero.mp (hc _ h1))
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hdi, rfl⟩)

include hc hT in
/-- Brackets add weights. -/
theorem lie_mem_span_weight (a a' : Fin n) :
    ⁅b a, b a'⁆ ∈ Submodule.span k (b '' {i | d i = d a + d a'}) := by
  refine mem_span_of_eigen b d c hc T hT _ _ ?_
  rw [LieHom.map_lie, hT, hT, smul_lie, lie_smul, smul_smul, zpow_add, Units.val_mul]

include hc hT in
theorem lie_mem_span_pos (a a' : Fin n) (ha : 0 < d a) (ha' : 0 < d a') :
    ⁅b a, b a'⁆ ∈ Submodule.span k (b '' {i | 0 < d i}) :=
  Submodule.span_mono (Set.image_mono fun i (hi : d i = d a + d a') =>
    show 0 < d i by omega) (lie_mem_span_weight b d c hc T hT a a')

include hc hT in
theorem lie_mem_span_zero (a a' : Fin n) (ha : d a = 0) (ha' : d a' = 0) :
    ⁅b a, b a'⁆ ∈ Submodule.span k (b '' {i | d i = 0}) := by
  have h := lie_mem_span_weight b d c hc T hT a a'
  rwa [ha, ha', add_zero] at h

/-- The span of the ordered monomials having a letter of positive weight. -/
def positiveLetterSpan : Submodule k U :=
  Submodule.span k ((orderedPBWBasisOf b) '' {e | ∃ i, e i ≠ 0 ∧ 0 < d i})

/-- The span of the ordered monomials all of whose letters have weight zero. -/
def zeroLetterSpan : Submodule k U :=
  Submodule.span k ((orderedPBWBasisOf b) '' {e | ∀ i, e i ≠ 0 → d i = 0})

theorem positiveLetterSpan_inf_zeroLetterSpan :
    positiveLetterSpan b d ⊓ zeroLetterSpan b d = ⊥ := by
  rw [eq_bot_iff]
  intro y ⟨hP, hZ⟩
  rw [Submodule.mem_bot]
  apply (orderedPBWBasisOf b).repr.injective
  ext e
  rw [map_zero, Finsupp.zero_apply]
  by_cases h : ∃ i, e i ≠ 0 ∧ 0 < d i
  · obtain ⟨i, hi, hdi⟩ := h
    exact repr_eq_zero_of_mem_span _ _ hZ fun he => (he i hi ▸ hdi).false
  · exact repr_eq_zero_of_mem_span _ _ hP h

include hc hT in
theorem zeroWeightGeneratorSubalgebra_le :
    (zeroWeightGeneratorSubalgebra (k := k) b d).toSubmodule ≤ zeroLetterSpan b d :=
  adjoin_le_span_orderedPBWBasisOf b (fun a => d a = 0)
    (fun a a' ha ha' => lie_mem_span_zero b d c hc T hT a a' ha ha')

include hc hT in
/-- Left multiplication by a positive-weight generator keeps a monomial in the span of the
monomials with a positive-weight letter, for weights decreasing along the basis order. -/
theorem generator_mul_mem_positiveLetterSpan (hd : Antitone d) (a : Fin n) (ha : 0 < d a)
    (e : Fin n → ℕ) :
    ι (b a) * orderedPBWMonomial b e ∈ positiveLetterSpan b d := by
  classical
  let φ : U →ₐ[k] U := UniversalEnvelopingAlgebra.lift k ((UniversalEnvelopingAlgebra.ι k).comp T)
  have hφ (a : Fin n) : φ (ι (b a)) = ((c ^ d a : kˣ) : k) • ι (b a) := by
    simp only [φ, UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.comp_apply, hT, map_smul]
  let e₁ : Fin n → ℕ := fun i => if 0 < d i then e i else 0
  let e₂ : Fin n → ℕ := fun i => if 0 < d i then 0 else e i
  have hord (f : Fin n → ℕ) (hf : ∀ i, f i ≠ 0 → 0 < d i) :
      ∀ i j, f i ≠ 0 → e₂ j ≠ 0 → i < j := by
    intro i j hi hj
    have hdi := hf i hi
    have hdj : ¬ 0 < d j := by
      intro h
      simp [e₂, h] at hj
    by_contra hij
    exact hdj (lt_of_lt_of_le hdi (hd (not_lt.mp hij)))
  have he₁ : ∀ i, e₁ i ≠ 0 → 0 < d i := by
    intro i hi
    by_contra h
    simp [e₁, h] at hi
  have hsplit : orderedPBWMonomial b e = orderedPBWMonomial b e₁ * orderedPBWMonomial b e₂ := by
    rw [orderedPBWMonomial, orderedPBWMonomial, orderedPBWMonomial,
      ← ofFn_prod_pow_add _ e₁ e₂ (hord e₁ he₁)]
    congr 1
    refine congrArg List.ofFn (funext fun i => ?_)
    by_cases h : 0 < d i <;> simp [e₁, e₂, h]
  let x := ι (b a) * orderedPBWMonomial b e₁
  have hx_adj : x ∈ Algebra.adjoin k {u | ∃ a, 0 < d a ∧ u = ι (b a)} :=
    Subalgebra.mul_mem _ (Algebra.subset_adjoin ⟨a, ha, rfl⟩)
      (ofFn_prod_pow_mem_adjoin _ (fun a => 0 < d a) e₁ he₁)
  have hx_span : x ∈ Submodule.span k ((orderedPBWBasisOf b) '' {f | ∀ i, f i ≠ 0 → 0 < d i}) :=
    adjoin_le_span_orderedPBWBasisOf b (fun a => 0 < d a)
      (fun a a' ha ha' => lie_mem_span_pos b d c hc T hT a a' ha ha') hx_adj
  have hφx : φ x = ((c ^ (d a + monomialWeight d e₁) : kˣ) : k) • x := by
    simp only [x, map_mul, hφ, map_orderedPBWMonomial b d c φ hφ, smul_mul_smul_comm,
      zpow_add, Units.val_mul]
  have hw₁ : 0 ≤ monomialWeight d e₁ := by
    refine Finset.sum_nonneg fun i _ => ?_
    by_cases h : e₁ i = 0
    · simp [h]
    · exact mul_nonneg (Nat.cast_nonneg _) (he₁ i h).le
  have hsupport (f : Fin n → ℕ) (hf : f ∈ ((orderedPBWBasisOf b).repr x).support) :
      (∀ i, f i ≠ 0 → 0 < d i) ∧ ∃ i, f i ≠ 0 ∧ 0 < d i := by
    have hne := Finsupp.mem_support_iff.mp hf
    have hpos : ∀ i, f i ≠ 0 → 0 < d i := by
      by_contra h
      exact hne (repr_eq_zero_of_mem_span _ _ hx_span h)
    refine ⟨hpos, ?_⟩
    have h := orderedPBWBasisOf_repr_map b d c φ hφ x f
    rw [hφx, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
    have heq : ((c ^ (d a + monomialWeight d e₁) : kˣ) : k) =
        ((c ^ monomialWeight d f : kˣ) : k) := mul_right_cancel₀ hne h
    have hwf : monomialWeight d f = d a + monomialWeight d e₁ := by
      have h1 : c ^ (monomialWeight d f - (d a + monomialWeight d e₁)) = 1 := by
        rw [zpow_sub, ← Units.val_inj.mp heq, mul_inv_cancel]
      exact sub_eq_zero.mp (hc _ h1)
    by_contra hnone
    push Not at hnone
    have hzero : monomialWeight d f = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases h : f i = 0
      · simp [h]
      · exact absurd (hpos i h) (not_lt.mpr (hnone i h))
    omega
  rw [hsplit, ← mul_assoc]
  change x * orderedPBWMonomial b e₂ ∈ positiveLetterSpan b d
  rw [← (orderedPBWBasisOf b).linearCombination_repr x, Finsupp.linearCombination_apply,
    Finsupp.sum, Finset.sum_mul]
  refine Submodule.sum_mem _ fun f hf => ?_
  rw [smul_mul_assoc]
  refine Submodule.smul_mem _ _ ?_
  obtain ⟨hpos, i, hi, hdi⟩ := hsupport f hf
  refine Submodule.subset_span ⟨fun j => f j + e₂ j, ⟨i, show f i + e₂ i ≠ 0 by omega, hdi⟩, ?_⟩
  rw [orderedPBWBasisOf_apply, orderedPBWBasisOf_apply, orderedPBWMonomial, orderedPBWMonomial,
    orderedPBWMonomial, ofFn_prod_pow_add _ f e₂ (hord f hpos)]

include hc hT in
theorem positiveWeightGeneratorSpan_le (hd : Antitone d) :
    positiveWeightGeneratorSpan (k := k) b d ≤ positiveLetterSpan b d := by
  rw [positiveWeightGeneratorSpan, Submodule.span_le]
  rintro u ⟨a, ha, v, rfl⟩
  rw [← (orderedPBWBasisOf b).linearCombination_repr v, Finsupp.linearCombination_apply,
    Finsupp.sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun e _ => ?_
  rw [mul_smul_comm, orderedPBWBasisOf_apply]
  exact Submodule.smul_mem _ _ (generator_mul_mem_positiveLetterSpan b d c hc T hT hd a ha e)

include hc hT in
theorem disjoint_of_antitone (hd : Antitone d) :
    Disjoint (positiveWeightGeneratorSpan (k := k) b d)
      (zeroWeightGeneratorSubalgebra (k := k) b d).toSubmodule := by
  rw [disjoint_iff, eq_bot_iff, ← positiveLetterSpan_inf_zeroLetterSpan b d]
  exact inf_le_inf (positiveWeightGeneratorSpan_le b d c hc T hT hd)
    (zeroWeightGeneratorSubalgebra_le b d c hc T hT)

end Weights

section Reindex

variable {I I' : Type*} (b : I → L) (d : I → ℤ) (σ : I' ≃ I)

theorem positiveWeightGeneratorSpan_comp_equiv :
    positiveWeightGeneratorSpan (k := k) (b ∘ σ) (d ∘ σ) = positiveWeightGeneratorSpan b d := by
  unfold positiveWeightGeneratorSpan
  congr 1
  ext u
  constructor
  · rintro ⟨a, ha, v, rfl⟩
    exact ⟨σ a, ha, v, rfl⟩
  · rintro ⟨a, ha, v, rfl⟩
    exact ⟨σ.symm a, by simpa using ha, v, by simp⟩

theorem zeroWeightGeneratorSubalgebra_comp_equiv :
    zeroWeightGeneratorSubalgebra (k := k) (b ∘ σ) (d ∘ σ) = zeroWeightGeneratorSubalgebra b d := by
  unfold zeroWeightGeneratorSubalgebra
  congr 1
  ext u
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨σ a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨σ.symm a, by simpa using ha, by simp⟩

end Reindex

/-- Fixed points of a weight-scaling automorphism of the enveloping algebra. Let `b` be a finite
basis of a Lie algebra `L` over a field `k`, `d` an integer weight on its indices and `c` a unit
of `k` that is not a root of unity. If a Lie algebra endomorphism `T` of `L` scales each `b a`
by `c ^ d a`, then every element of `U(L)` fixed by the induced algebra endomorphism lies in the
sum of the right ideal generated by the positive-weight generators and the subalgebra generated
by the weight-zero generators, and this sum is direct. -/
theorem envelopingFixedWeightDecomposition : EnvelopingFixedWeightDecompositionStatement.{u, v} := by
  intro k _ L _ _ n b d c hc T hT
  let σ := Tuple.sort (fun i => -d i)
  have hmono := Tuple.monotone_sort (fun i => -d i)
  let b' := b.reindex σ.symm
  have hb' : ⇑b' = ⇑b ∘ σ := by
    funext i
    simp [b', Module.Basis.reindex_apply]
  let d' := d ∘ σ
  have hd' : Antitone d' := fun i j hij => by
    have h := hmono hij
    simp only [Function.comp_apply, neg_le_neg_iff] at h
    exact h
  have hT' : ∀ a, T (b' a) = ((c ^ d' a : kˣ) : k) • b' a := by
    intro a
    rw [hb']
    exact hT (σ a)
  have hspan : positiveWeightGeneratorSpan (k := k) b' d' = positiveWeightGeneratorSpan b d := by
    rw [hb']
    exact positiveWeightGeneratorSpan_comp_equiv (⇑b) d σ
  have halg : zeroWeightGeneratorSubalgebra (k := k) b' d' = zeroWeightGeneratorSubalgebra b d := by
    rw [hb']
    exact zeroWeightGeneratorSubalgebra_comp_equiv (⇑b) d σ
  refine ⟨fun z hz => ?_, ?_⟩
  · let φ : UniversalEnvelopingAlgebra k L →ₐ[k] UniversalEnvelopingAlgebra k L :=
      UniversalEnvelopingAlgebra.lift k ((UniversalEnvelopingAlgebra.ι k).comp T)
    have hφ (a : Fin n) :
        φ (UniversalEnvelopingAlgebra.ι k (b' a)) =
          ((c ^ d' a : kˣ) : k) • UniversalEnvelopingAlgebra.ι k (b' a) := by
      simp only [φ, UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.comp_apply, hT', map_smul]
    rw [← hspan, ← halg]
    exact mem_sup_of_fixed_of_antitone b' d' c hd' hc φ hφ z hz
  · rw [← hspan, ← halg]
    exact disjoint_of_antitone b' d' c hc T hT' hd'

end Langlands.Algebra.UniversalEnveloping
