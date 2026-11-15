import Langlands.Representation.Archimedean.Kostant.Coadjoint
import Langlands.Representation.Archimedean.RealGenericLargeReduction
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Matumoto's lemma: symbols of the annihilator vanish at the Whittaker point

Let `π` be a representation of `L = ∏ᵢ 𝔤𝔩_{n i}(ℂ)` on `V` and `ℓ ≠ 0` a linear functional with
`ℓ(π(X) v) = η(X) ℓ(v)` for blockwise strictly upper triangular `X`, where
`η(X) = ∑ a_{i,p} X_{i,p,p+1}`. If `P ∈ U_N` acts by `0`, then its symbol `σ_N(P)` vanishes at the
point `ψ` with coordinates `ψ⟨i, p, p+1⟩ = a_{i,p}` and `0` elsewhere (Matumoto 1987, Theorem 1,
for the grading by `deg E⟨i,p,q⟩ = q - p`).

Proof. Grade `U` by `D = ad h`, `h = diag(-p)` in each block, so `D E^α = (∑ α_c deg c) E^α`.
Write `P` in ordered monomials whose factors decrease in degree. A polynomial in `D` (Lagrange
interpolation) extracts from `P` its part `P_N` of `D`-degree `N`, which still acts by `0`.
For an ordered monomial of length at most `N` and degree `N`, either all factors have degree `1`
(then `ℓ(E^α v) = ψ(X^α) ℓ(v)`), or its first factor has degree at least `2` (then
`ℓ(E^α v) = 0 = ψ(σ_N E^α)`). Monomials of degree different from `N` have `ψ(σ_N E^α) = 0`.
Hence `ψ(σ_N P) ℓ(v) = ℓ(P_N v) = 0`.
-/

noncomputable section

set_option autoImplicit false

-- Entries of tuples of matrices are applied through the `Matrix` definition.
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.Kostant

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Algebra.UniversalEnveloping MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ι → ℕ)

local notation "U" => UniversalEnvelopingAlgebra ℂ (GLProd ℂ n)

/-! ## The grading and an ordered enumeration -/

/-- The degree `q - p` of the coordinate `⟨i, p, q⟩`. -/
def deg (c : Coord n) : ℤ := (c.2.2 : ℤ) - (c.2.1 : ℤ)

/-- An enumeration of the coordinates in decreasing degree. -/
def sortedCoords : List (Coord n) :=
  (Finset.univ : Finset (Coord n)).toList.mergeSort fun c c' => decide (deg n c' ≤ deg n c)

omit [DecidableEq ι] in
theorem sortedCoords_nodup : (sortedCoords n).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)

omit [DecidableEq ι] in
theorem mem_sortedCoords (c : Coord n) : c ∈ sortedCoords n :=
  (List.mergeSort_perm _ _).mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ c))

omit [DecidableEq ι] in
theorem sortedCoords_pairwise :
    (sortedCoords n).Pairwise fun c c' => deg n c' ≤ deg n c := by
  have h := List.pairwise_mergeSort (le := fun c c' : Coord n => decide (deg n c' ≤ deg n c))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    (Finset.univ : Finset (Coord n)).toList
  unfold sortedCoords
  simpa only [decide_eq_true_eq] using h

/-- The diagonal element `h` with `⁅h, E⟨i,p,q⟩⁆ = (q - p) E⟨i,p,q⟩`. -/
def hdiag : GLProd ℂ n := fun _ => Matrix.diagonal fun p => -((p : ℕ) : ℂ)

omit [Fintype ι] in
theorem lie_hdiag_unit (i : ι) (p q : Fin (n i)) :
    ⁅hdiag n, unit ℂ n i p q⁆ = (deg n ⟨i, p, q⟩ : ℂ) • unit ℂ n i p q := by
  rw [lie_unit]
  simp only [hdiag, Matrix.diagonal_apply, ite_smul, zero_smul, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, deg]
  rw [← sub_smul]
  congr 1
  push_cast
  ring

/-- The grading derivation `D = ad h` of `U`. -/
def gradDer : Module.End ℂ U :=
  LinearMap.mulLeft ℂ (UniversalEnvelopingAlgebra.ι ℂ (hdiag n)) -
    LinearMap.mulRight ℂ (UniversalEnvelopingAlgebra.ι ℂ (hdiag n))

omit [Fintype ι] [DecidableEq ι] in
theorem gradDer_apply (u : U) :
    gradDer n u = UniversalEnvelopingAlgebra.ι ℂ (hdiag n) * u -
      u * UniversalEnvelopingAlgebra.ι ℂ (hdiag n) := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem gradDer_mul (u v : U) : gradDer n (u * v) = gradDer n u * v + u * gradDer n v := by
  simp only [gradDer_apply]
  noncomm_ring

theorem gradDer_basis (c : Coord n) :
    gradDer n (UniversalEnvelopingAlgebra.ι ℂ (glBasis ℂ n c)) =
      (deg n c : ℂ) • UniversalEnvelopingAlgebra.ι ℂ (glBasis ℂ n c) := by
  rw [gradDer_apply]
  have h := (UniversalEnvelopingAlgebra.ι ℂ (L := GLProd ℂ n)).map_lie (hdiag n) (glBasis ℂ n c)
  rw [Ring.lie_def (UniversalEnvelopingAlgebra.ι ℂ (hdiag n))] at h
  rw [← h, glBasis_apply, lie_hdiag_unit, map_smul]

theorem gradDer_word (l : List (Coord n)) :
    gradDer n (word ℂ (GLProd ℂ n) (l.map (glBasis ℂ n))) =
      (((l.map (deg n)).sum : ℤ) : ℂ) • word ℂ (GLProd ℂ n) (l.map (glBasis ℂ n)) := by
  induction l with
  | nil => simp [word, gradDer_apply]
  | cons c l ih =>
    rw [List.map_cons, word_cons, gradDer_mul, ih, gradDer_basis, List.map_cons, List.sum_cons,
      mul_smul_comm, smul_mul_assoc, ← add_smul]
    push_cast
    ring_nf

/-- The weighted degree of an ordered monomial. -/
def wdeg (α : Coord n →₀ ℕ) : ℤ := ((expand (sortedCoords n) α).map (deg n)).sum

theorem gradDer_orderedMonomial (α : Coord n →₀ ℕ) :
    gradDer n (orderedMonomial ℂ (GLProd ℂ n) (glBasis ℂ n) (sortedCoords n) α) =
      (wdeg n α : ℂ) • orderedMonomial ℂ (GLProd ℂ n) (glBasis ℂ n) (sortedCoords n) α :=
  gradDer_word n _

/-! ## The action on `V` -/

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (π : GLProd ℂ n →ₗ⁅ℂ⁆ Module.End ℂ V)

omit [Fintype ι] [DecidableEq ι] in
theorem envelopingAction_word (l : List (GLProd ℂ n)) :
    envelopingAction π (word ℂ (GLProd ℂ n) l) = (l.map π).prod := by
  induction l with
  | nil => simp [word]
  | cons x l ih =>
    rw [word_cons, map_mul, ih, envelopingAction, UniversalEnvelopingAlgebra.lift_ι_apply]
    rfl

omit [Fintype ι] [DecidableEq ι] in
theorem envelopingAction_gradDer {u : U} (hu : envelopingAction π u = 0) :
    envelopingAction π (gradDer n u) = 0 := by
  rw [gradDer_apply, map_sub, map_mul, map_mul, hu, mul_zero, zero_mul, sub_zero]

omit [Fintype ι] [DecidableEq ι] in
theorem envelopingAction_aeval_gradDer (p : Polynomial ℂ) {u : U}
    (hu : envelopingAction π u = 0) :
    envelopingAction π (Polynomial.aeval (gradDer n) p u) = 0 := by
  induction p using Polynomial.induction_on generalizing u with
  | C c =>
    rw [Polynomial.aeval_C, Module.algebraMap_end_apply, map_smul, hu, smul_zero]
  | add p q hp hq => rw [map_add, LinearMap.add_apply, map_add, hp hu, hq hu, add_zero]
  | monomial k c hk =>
    rw [pow_succ, ← mul_assoc, map_mul, Module.End.mul_apply, Polynomial.aeval_X]
    exact hk (envelopingAction_gradDer n π hu)

/-! ## The Whittaker character and the point `ψ` -/

variable (a : ∀ i, Fin (n i) → ℂ)

/-- The character `η(X) = ∑ a_{i,p} X_{i,p,p+1}`. -/
def whitChar (X : GLProd ℂ n) : ℂ :=
  ∑ i : ι, ∑ p : Fin (n i), ∑ q : Fin (n i), if (q : ℕ) = p + 1 then a i p * X i p q else 0

/-- The Whittaker point `ψ`. -/
def whitPoint (v : Coord n) : ℂ := if (v.2.2 : ℕ) = v.2.1 + 1 then a v.1 v.2.1 else 0

theorem whitChar_unit (c : Coord n) :
    whitChar n a (unit ℂ n c.1 c.2.1 c.2.2) = whitPoint n a c := by
  have h : ∀ (i : ι) (p q : Fin (n i)), (if (q : ℕ) = p + 1 then
      a i p * unit ℂ n c.1 c.2.1 c.2.2 i p q else 0) =
        if (⟨i, p, q⟩ : Coord n) = c then whitPoint n a ⟨i, p, q⟩ else 0 := by
    intro i p q
    have hu := unit_apply ℂ n c.1 c.2.1 c.2.2 ⟨i, p, q⟩
    simp only at hu
    rw [hu, whitPoint]
    by_cases hc : (⟨i, p, q⟩ : Coord n) = c
    · subst hc; simp
    · simp [hc]
  simp only [whitChar, h]
  have hs : ∀ g : Coord n → ℂ, ∑ v, g v = ∑ i, ∑ p : Fin (n i), ∑ q : Fin (n i), g ⟨i, p, q⟩ := by
    intro g
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
  rw [← hs (fun v => if v = c then whitPoint n a v else 0)]
  simp

omit [Fintype ι] in
theorem unit_strictUpper (c : Coord n) (hc : (c.2.1 : ℕ) < c.2.2) :
    ∀ (i : ι) (p q : Fin (n i)), (q : ℕ) ≤ p → unit ℂ n c.1 c.2.1 c.2.2 i p q = 0 := by
  intro i p q hqp
  have hu := unit_apply ℂ n c.1 c.2.1 c.2.2 ⟨i, p, q⟩
  simp only at hu
  rw [hu, ite_eq_right_iff]
  intro he
  exfalso
  obtain ⟨j, r, s⟩ := c
  simp only [Sigma.mk.inj_iff] at he
  obtain ⟨rfl, he⟩ := he
  simp only [heq_eq_eq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  simp only at hc
  omega

/-- The functional `ℓ` is a Whittaker vector for `η` on strictly upper triangular `X`. -/
def IsWhittaker (ℓ : V →ₗ[ℂ] ℂ) : Prop :=
  ∀ X : GLProd ℂ n, (∀ (i : ι) (p q : Fin (n i)), (q : ℕ) ≤ p → X i p q = 0) →
    ∀ v : V, ℓ (π X v) = whitChar n a X * ℓ v

variable {π a} {ℓ : V →ₗ[ℂ] ℂ}

theorem whittaker_basis (hℓ : IsWhittaker n π a ℓ) (c : Coord n) (hc : (c.2.1 : ℕ) < c.2.2)
    (v : V) : ℓ (π (glBasis ℂ n c) v) = whitPoint n a c * ℓ v := by
  rw [glBasis_apply, hℓ _ (unit_strictUpper n c hc), whitChar_unit]

/-! ## Words of degree `N` -/

theorem eval_symbol_word {N : ℕ} (l : List (Coord n)) (hl : l.length = N) :
    eval (whitPoint n a) ((glSymbol ℂ n).symbol N (word ℂ (GLProd ℂ n) (l.map (glBasis ℂ n)))) =
      (l.map (whitPoint n a)).prod := by
  rw [(glSymbol ℂ n).symbol_word_of_length_eq _ (by simpa using hl), List.map_map, map_list_prod,
    List.map_map]
  congr 1
  refine List.map_congr_left fun c _ => ?_
  simp only [Function.comp_apply, AssocSymbol.symbolData_ξ_basis, MvPolynomial.eval_X]

omit [Fintype ι] [DecidableEq ι] in
theorem whitPoint_eq_zero {c : Coord n} (hc : deg n c ≠ 1) : whitPoint n a c = 0 := by
  rw [whitPoint, ite_eq_right]
  intro h
  apply hc
  simp only [deg]
  omega

theorem whittaker_word_of_deg_one (hℓ : IsWhittaker n π a ℓ) :
    ∀ (l : List (Coord n)), (∀ c ∈ l, deg n c = 1) → ∀ v : V,
      ℓ (envelopingAction π (word ℂ (GLProd ℂ n) (l.map (glBasis ℂ n))) v) =
        (l.map (whitPoint n a)).prod * ℓ v := by
  intro l
  induction l with
  | nil => intro _ v; simp [word]
  | cons c l ih =>
    intro hl v
    rw [List.map_cons, envelopingAction_word, List.map_cons, List.prod_cons,
      Module.End.mul_apply, ← envelopingAction_word]
    have hc : (c.2.1 : ℕ) < c.2.2 := by
      have := hl c List.mem_cons_self; simp only [deg] at this; omega
    rw [whittaker_basis n hℓ c hc, ih (fun c' hc' => hl c' (List.mem_cons_of_mem _ hc')),
      List.map_cons, List.prod_cons, mul_assoc]

/-- Integers at most `1` whose sum is at least the length are all equal to `1`. -/
theorem all_eq_one_of_sum (xs : List ℤ) (h1 : ∀ x ∈ xs, x ≤ 1) (hs : (xs.length : ℤ) ≤ xs.sum) :
    ∀ x ∈ xs, x = 1 := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    simp only [List.length_cons, List.sum_cons, Nat.cast_add, Nat.cast_one] at hs
    have hy := h1 y List.mem_cons_self
    have hys : ys.sum ≤ ys.length := by
      have : ∀ zs : List ℤ, (∀ z ∈ zs, z ≤ 1) → zs.sum ≤ zs.length := by
        intro zs
        induction zs with
        | nil => simp
        | cons z zs ihz =>
          intro hz
          simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
          have := hz z List.mem_cons_self
          have := ihz fun w hw => hz w (List.mem_cons_of_mem _ hw)
          omega
      exact this ys fun w hw => h1 w (List.mem_cons_of_mem _ hw)
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · exact ih (fun w hw => h1 w (List.mem_cons_of_mem _ hw)) (by omega) x hx

/-- Matumoto's identity for a decreasingly ordered word of length at most `N` and degree `N`. -/
theorem whittaker_word (hℓ : IsWhittaker n π a ℓ) {N : ℕ} (l : List (Coord n))
    (hsort : l.Pairwise fun c c' => deg n c' ≤ deg n c) (hlen : l.length ≤ N)
    (hdeg : (l.map (deg n)).sum = N) (v : V) :
    ℓ (envelopingAction π (word ℂ (GLProd ℂ n) (l.map (glBasis ℂ n))) v) =
      eval (whitPoint n a)
        ((glSymbol ℂ n).symbol N (word ℂ (GLProd ℂ n) (l.map (glBasis ℂ n)))) * ℓ v := by
  by_cases hall : ∀ c ∈ l, deg n c = 1
  · have hl : l.length = N := by
      have : (l.map (deg n)).sum = l.length := by
        rw [List.map_congr_left (g := fun _ => (1 : ℤ)) hall]
        simp
      omega
    rw [eval_symbol_word n l hl, whittaker_word_of_deg_one n hℓ l hall]
  · push Not at hall
    obtain ⟨c, hcl, hc⟩ := hall
    have hrhs : eval (whitPoint n a)
        ((glSymbol ℂ n).symbol N (word ℂ (GLProd ℂ n) (l.map (glBasis ℂ n)))) = 0 := by
      rcases hlen.lt_or_eq with hlt | heq
      · rw [(glSymbol ℂ n).symbol_word_of_length_lt _ (by simpa using hlt), map_zero]
      · rw [eval_symbol_word n l heq]
        exact List.prod_eq_zero (List.mem_map.mpr ⟨c, hcl, whitPoint_eq_zero n hc⟩)
    rw [hrhs, zero_mul]
    obtain ⟨c₀, l', rfl⟩ : ∃ c₀ l', l = c₀ :: l' := List.exists_cons_of_ne_nil
      (List.ne_nil_of_mem hcl)
    have hhead : 2 ≤ deg n c₀ := by
      by_contra hlt
      push Not at hlt
      have hle : ∀ c' ∈ c₀ :: l', deg n c' ≤ 1 := by
        intro c' hc'
        rcases List.mem_cons.mp hc' with rfl | hc'
        · omega
        · have := (List.pairwise_cons.mp hsort).1 c' hc'; omega
      have hone := all_eq_one_of_sum ((c₀ :: l').map (deg n))
        (fun x hx => by
          obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hx; exact hle c' hc')
        (by rw [List.length_map, hdeg]; exact_mod_cast hlen)
      exact hc (hone _ (List.mem_map.mpr ⟨c, hcl, rfl⟩))
    have hc₀ : (c₀.2.1 : ℕ) < c₀.2.2 := by simp only [deg] at hhead; omega
    rw [List.map_cons, envelopingAction_word, List.map_cons, List.prod_cons,
      Module.End.mul_apply, whittaker_basis n hℓ c₀ hc₀,
      whitPoint_eq_zero n (by omega : deg n c₀ ≠ 1), zero_mul]

/-! ## Matumoto's lemma -/

theorem eval_symbol_word_eq_zero {N : ℕ} (l : List (Coord n)) (hlen : l.length ≤ N)
    (hdeg : (l.map (deg n)).sum ≠ N) :
    eval (whitPoint n a)
      ((glSymbol ℂ n).symbol N (word ℂ (GLProd ℂ n) (l.map (glBasis ℂ n)))) = 0 := by
  rcases hlen.lt_or_eq with hlt | heq
  · rw [(glSymbol ℂ n).symbol_word_of_length_lt _ (by simpa using hlt), map_zero]
  · rw [eval_symbol_word n l heq]
    by_contra hne
    apply hdeg
    have hall : ∀ c ∈ l, deg n c = 1 := by
      intro c hc
      by_contra h
      exact hne (List.prod_eq_zero (List.mem_map.mpr ⟨c, hc, whitPoint_eq_zero n h⟩))
    rw [List.map_congr_left (g := fun _ => (1 : ℤ)) hall]
    simp [heq]

/-- **Matumoto's lemma.** If `P ∈ U_N` acts by `0` on a module with a nonzero Whittaker
functional, then `σ_N(P)` vanishes at the Whittaker point. -/
theorem eval_symbol_eq_zero (hℓ : IsWhittaker n π a ℓ) (hℓ0 : ℓ ≠ 0) {N : ℕ} {P : U}
    (hP : P ∈ degreeFiltration ℂ (GLProd ℂ n) N) (hPV : envelopingAction π P = 0) :
    eval (whitPoint n a) ((glSymbol ℂ n).symbol N P) = 0 := by
  set bs := sortedCoords n
  set E := orderedMonomial ℂ (GLProd ℂ n) (glBasis ℂ n) bs
  have hP' := degreeFiltration_le_orderedSpan ℂ (GLProd ℂ n) (glBasis ℂ n)
    (sortedCoords_nodup n) (mem_sortedCoords n) N hP
  obtain ⟨c, hc, hPc⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).mp hP'
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hPc
  -- the Lagrange projection onto `D`-degree `N`
  set T : Finset ℂ := (c.support.image fun α => (wdeg n α : ℂ)).erase (N : ℂ)
  set lag : Polynomial ℂ := ∏ m ∈ T,
    (Polynomial.C ((N : ℂ) - m)⁻¹ * (Polynomial.X - Polynomial.C m))
  have hlag : ∀ α ∈ c.support, lag.eval (wdeg n α : ℂ) = if wdeg n α = N then 1 else 0 := by
    intro α hα
    split_ifs with h
    · rw [h, Polynomial.eval_prod]
      refine Finset.prod_eq_one fun m hm => ?_
      have hm' : (N : ℂ) - m ≠ 0 := sub_ne_zero.mpr (Finset.ne_of_mem_erase hm).symm
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
      push_cast
      exact inv_mul_cancel₀ hm'
    · rw [Polynomial.eval_prod]
      refine Finset.prod_eq_zero (i := (wdeg n α : ℂ)) ?_ ?_
      · refine Finset.mem_erase.mpr ⟨?_, Finset.mem_image.mpr ⟨α, hα, rfl⟩⟩
        exact_mod_cast h
      · simp
  set PN := Polynomial.aeval (gradDer n) lag P
  have hPN : PN = ∑ α ∈ c.support, (if wdeg n α = N then c α else 0) • E α := by
    rw [show PN = Polynomial.aeval (gradDer n) lag P from rfl, ← hPc, map_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [map_smul, Module.End.aeval_apply_of_mem_apply_eq_smul
      (gradDer_orderedMonomial n α), hlag α hα, smul_smul]
    split_ifs <;> simp [E, bs]
  have hPNV : envelopingAction π PN = 0 := envelopingAction_aeval_gradDer n π lag hPV
  -- monomials of degree different from `N` vanish at `ψ`
  have hdegα : ∀ α ∈ c.support, (α.degree ≤ N) := fun α hα => hc hα
  have hexp : ∀ α : Coord n →₀ ℕ, (expand bs α).length = α.degree :=
    length_expand (sortedCoords_nodup n) (mem_sortedCoords n)
  have hsorted : ∀ α : Coord n →₀ ℕ,
      (expand bs α).Pairwise fun c c' => deg n c' ≤ deg n c := by
    intro α
    unfold expand
    refine List.pairwise_flatMap.mpr ⟨fun c _ => ?_, ?_⟩
    · exact List.pairwise_replicate.mpr (Or.inr le_rfl)
    · refine (sortedCoords_pairwise n).imp_of_mem fun {c c'} _ _ h => ?_
      intro x hx y hy
      rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy]
      exact h
  have hsym : eval (whitPoint n a) ((glSymbol ℂ n).symbol N P) =
      eval (whitPoint n a) ((glSymbol ℂ n).symbol N PN) := by
    rw [← hPc, hPN, map_sum, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [LinearMap.map_smul, LinearMap.map_smul, MvPolynomial.smul_eval, MvPolynomial.smul_eval]
    split_ifs with h
    · rfl
    · rw [zero_mul]
      have := eval_symbol_word_eq_zero n (a := a) (expand bs α) (by rw [hexp]; exact hdegα α hα) h
      simp only [orderedMonomial] at this ⊢
      rw [this, mul_zero]
  -- Matumoto's identity for `P_N`
  have hmat : ∀ v : V, ℓ (envelopingAction π PN v) =
      eval (whitPoint n a) ((glSymbol ℂ n).symbol N PN) * ℓ v := by
    intro v
    rw [hPN, map_sum, map_sum, map_sum, LinearMap.sum_apply, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α hα => ?_
    split_ifs with h
    · rw [map_smul, LinearMap.smul_apply, map_smul, LinearMap.map_smul, MvPolynomial.smul_eval,
        smul_eq_mul, mul_assoc]
      congr 1
      exact whittaker_word n hℓ (expand bs α) (hsorted α) (by rw [hexp]; exact hdegα α hα) h v
    · simp
  obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓ0 (LinearMap.ext h)
  have := hmat v
  rw [hPNV, LinearMap.zero_apply, map_zero] at this
  rw [hsym]
  exact (mul_eq_zero.mp this.symm).resolve_right hv

end Langlands.Archimedean.Kostant
