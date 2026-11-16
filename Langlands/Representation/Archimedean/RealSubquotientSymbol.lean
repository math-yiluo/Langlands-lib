import Langlands.Representation.Archimedean.RealSubquotientProjection
import Langlands.Representation.Archimedean.Kostant.OrderedMonomials
import Mathlib.Analysis.Matrix.Spectrum
import Langlands.Algebra.UniversalEnvelopingFilteredMaps

/-!
# Symbols and the injectivity of the principal-series projection

Helper results for Harish-Chandra's subquotient theorem (`RealPrincipalSeriesSubquotientStatement`).

* `bB`: a basis of `ℂ ⊗ 𝔤𝔩_n(ℝ)` consisting of the matrix units `E_pq`, `p ≤ q`, and the
  antisymmetric matrices `E_pq - E_qp`, `p > q`; `symB` the symbols in the coordinates of `bB`.
* `mem_of_symbol_vanish`: an element of `U_{D+1}` whose degree-`(D+1)` symbol vanishes on the
  real symmetric matrices lies in `U_D + U_D 𝔨` (Poincaré–Birkhoff–Witt in the order `𝔟`, `𝔨`).
* `evMat_symbol_conj`, `exists_orth_diag`, `typeDerivative_conj`: `O(n)`-equivariance of symbols
  evaluated at real symmetric matrices, the spectral theorem, and `τ(k) D(Y) = D(k Y kᵀ) τ(k)`.
* `Kspan D`: the relations `u Y ⊗ x - u ⊗ D(Y) x` (`Y` antisymmetric) in `U(𝔤)^d`; `PhiT_Kspan`:
  `Φ_T(w) = ∑ⱼ P(wⱼ) T(eⱼ)` kills them for every `K`-intertwiner `T`.
* `psiVec_mem_Kspan` (**descent**) and `act_eq_zero_of_chat_eq_zero` (**injectivity**): a
  `K`-invariant `b` with `ĉ(b) = 0` acts by zero on every `K`-intertwiner from `τ` into every
  `(𝔤𝔩_n(ℝ), O(n))`-module.
-/

noncomputable section

open scoped Matrix TensorProduct Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

namespace RealSubquotient

open Kostant MvPolynomial Langlands.Algebra.UniversalEnveloping InfinitesimalCharacter

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

/-! ## An adapted basis -/

/-- `Θ X = X - Lᵀ`, `L` the strictly lower triangular part of `X`. -/
def theta (n : ℕ) : Matrix (Fin n) (Fin n) ℝ ≃ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun X := Matrix.of fun i j => X i j - if i < j then X j i else 0
  invFun Z := Matrix.of fun i j => Z i j + if i < j then Z j i else 0
  map_add' X Y := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> ring
  map_smul' c X := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring
  left_inv X := by
    ext i j
    simp only [Matrix.of_apply]
    by_cases h : i < j
    · simp [h, not_lt.mpr h.le]
    · simp [h]
  right_inv Z := by
    ext i j
    simp only [Matrix.of_apply]
    by_cases h : i < j
    · simp [h, not_lt.mpr h.le]
    · simp [h]

theorem theta_apply (X : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    theta n X i j = X i j - if i < j then X j i else 0 := by
  simp [theta]

theorem theta_single (p q : Fin n) :
    theta n (Matrix.single p q 1) =
      Matrix.single p q 1 - if q < p then Matrix.single q p 1 else 0 := by
  ext i j
  rw [theta_apply]
  by_cases h : p = j ∧ q = i
  · obtain ⟨rfl, rfl⟩ := h
    by_cases h' : q < p
    · simp [Matrix.single_apply, h']
    · simp [Matrix.single_apply, h']
  · have h'' : ¬ (q = i ∧ p = j) := fun hh => h ⟨hh.2, hh.1⟩
    by_cases h' : q < p
    · simp [Matrix.single_apply, h, h'', h']
    · simp [Matrix.single_apply, h, h']

/-- The real basis `E_pq` (`p ≤ q`), `E_pq - E_qp` (`p > q`) of `𝔤𝔩_n(ℝ)`. -/
def basisR (n : ℕ) : Module.Basis (Fin n × Fin n) ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  (Matrix.stdBasis ℝ (Fin n) (Fin n)).map (theta n)

/-- The complexified basis of `ℂ ⊗ 𝔤𝔩_n(ℝ)`. -/
def bB (n : ℕ) : Module.Basis (Fin n × Fin n) ℂ (LL n) :=
  Algebra.TensorProduct.basis ℂ (basisR n)

theorem bB_apply (c : Fin n × Fin n) :
    bB n c = (1 : ℂ) ⊗ₜ (Matrix.single c.1 c.2 (1 : ℝ) -
      if c.2 < c.1 then Matrix.single c.2 c.1 1 else 0) := by
  rw [bB, Algebra.TensorProduct.basis_apply, basisR, Module.Basis.map_apply,
    Matrix.stdBasis_eq_single, theta_single]

/-! ## Symbols in the adapted coordinates -/

theorem realSymbol_ξ_single (p q : Fin n) :
    (realSymbol n).ξ ((1 : ℂ) ⊗ₜ Matrix.single p q (1 : ℝ)) =
      MvPolynomial.X (⟨(), p, q⟩ : Coord (fun _ : Unit => n)) := by
  rw [realSymbol_ξ_tmul, Finset.sum_eq_single ⟨(), p, q⟩]
  · simp
  · rintro ⟨u, p', q'⟩ _ hne
    have : ¬ (p = p' ∧ q = q') := by
      rintro ⟨rfl, rfl⟩
      exact hne rfl
    simp [this]
  · simp

/-- The change of coordinates from the matrix units to the basis `bB`. -/
def psiB (n : ℕ) :
    MvPolynomial (Coord (fun _ : Unit => n)) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
  aeval fun c => if c.2.2 < c.2.1 then X (c.2.1, c.2.2) + X (c.2.2, c.2.1) else X (c.2.1, c.2.2)

/-- The symbol data of `ℂ ⊗ 𝔤𝔩_n(ℝ)` in the coordinates of `bB`. -/
def symB (n : ℕ) : SymbolData ℂ (LL n)
    (AssocSymbol.CoordRing ℂ (B := Coord (fun _ : Unit => n))) (MvPolynomial (Fin n × Fin n) ℂ) where
  ρ := (realSymbol n).ρ
  leibniz := (realSymbol n).leibniz
  𝔪 := (realSymbol n).𝔪
  ε := (psiB n).comp (realSymbol n).ε
  ε_eq_zero a ha := by rw [AlgHom.comp_apply, (realSymbol n).ε_eq_zero a ha, map_zero]
  l := (realSymbol n).l
  l_mem := (realSymbol n).l_mem

theorem symB_ξ (x : LL n) : (symB n).ξ x = psiB n ((realSymbol n).ξ x) := rfl

theorem symB_symbol (N : ℕ) (u : UU n) :
    (symB n).symbol N u = psiB n ((realSymbol n).symbol N u) := by
  simp only [SymbolData.symbol, LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, map_smul]
  rfl

theorem symB_ξ_basis (c : Fin n × Fin n) : (symB n).ξ (bB n c) = X c := by
  obtain ⟨p, q⟩ := c
  rw [symB_ξ, bB_apply]
  by_cases h : q < p
  · simp [h, not_lt.mpr h.le, TensorProduct.tmul_sub, realSymbol_ξ_single, psiB]
  · simp [h, realSymbol_ξ_single, psiB]

/-! ## The ordered monomials with the antisymmetric letters last -/

/-- The basis indices, those of `𝔟` (`p ≤ q`) first and the antisymmetric ones (`p > q`) last. -/
def bsList (n : ℕ) : List (Fin n × Fin n) :=
  (Finset.univ.filter fun c : Fin n × Fin n => ¬ c.2 < c.1).toList ++
    (Finset.univ.filter fun c : Fin n × Fin n => c.2 < c.1).toList

theorem bsList_nodup : (bsList n).Nodup := by
  refine List.nodup_append.2 ⟨Finset.nodup_toList _, Finset.nodup_toList _, ?_⟩
  intro a ha b hb hab
  subst hab
  simp only [Finset.mem_toList, Finset.mem_filter] at ha hb
  exact ha.2 hb.2

theorem mem_bsList (c : Fin n × Fin n) : c ∈ bsList n := by
  by_cases h : c.2 < c.1
  · simp [bsList, h]
  · simp [bsList, h, not_lt.mp h]

/-- An ordered monomial containing an antisymmetric letter ends with one. -/
theorem orderedMonomial_eq_mul (α : Fin n × Fin n →₀ ℕ) {c : Fin n × Fin n} (hc : c.2 < c.1)
    (hα : α c ≠ 0) :
    ∃ (l : List (LL n)) (c' : Fin n × Fin n), c'.2 < c'.1 ∧ l.length + 1 = α.degree ∧
      orderedMonomial ℂ (LL n) (bB n) (bsList n) α =
        word ℂ (LL n) l * UniversalEnvelopingAlgebra.ι ℂ (bB n c') := by
  set l1 := expand (Finset.univ.filter fun c : Fin n × Fin n => ¬ c.2 < c.1).toList α
  set l2 := expand (Finset.univ.filter fun c : Fin n × Fin n => c.2 < c.1).toList α
  have hsplit : expand (bsList n) α = l1 ++ l2 := List.flatMap_append
  have hmem : c ∈ l2 := List.mem_flatMap.2 ⟨c, by simp [hc], List.mem_replicate.2 ⟨hα, rfl⟩⟩
  rcases List.eq_nil_or_concat l2 with h0 | ⟨l2', c', hl2⟩
  · rw [h0] at hmem; simp at hmem
  have hc' : c'.2 < c'.1 := by
    have : c' ∈ l2 := by rw [hl2]; simp
    obtain ⟨c'', hc'', hmem'⟩ := List.mem_flatMap.1 this
    rw [List.mem_replicate] at hmem'
    rw [hmem'.2]
    simpa using hc''
  refine ⟨(l1 ++ l2').map (bB n), c', hc', ?_, ?_⟩
  · have h := length_expand bsList_nodup mem_bsList α
    rw [hsplit, hl2] at h
    simp only [List.length_append, List.concat_eq_append, List.length_singleton] at h
    simp only [List.length_map, List.length_append]
    omega
  · rw [orderedMonomial, hsplit, hl2]
    simp [word, List.map_append, List.prod_append, mul_assoc]

/-! ## Elements whose top symbol vanishes on the symmetric matrices -/

/-- The point of the coordinates of `bB` attached to a real vector: the antisymmetric
coordinates vanish. -/
def yfun (y : Fin n × Fin n → ℝ) (c : Fin n × Fin n) : ℂ := if c.2 < c.1 then 0 else (y c : ℂ)

theorem eval_yfun_monomial_of_low (y : Fin n × Fin n → ℝ) {α : Fin n × Fin n →₀ ℕ}
    {c : Fin n × Fin n} (hc : c.2 < c.1) (hα : α c ≠ 0) :
    eval (yfun y) (monomial α (1 : ℂ)) = 0 := by
  rw [eval_monomial, one_mul, Finsupp.prod]
  refine Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hα) ?_
  simp [yfun, hc, zero_pow hα]

theorem eval_yfun_of_support {y : Fin n × Fin n → ℝ} {P : MvPolynomial (Fin n × Fin n) ℂ}
    (hP : ∀ α ∈ P.support, ∀ c : Fin n × Fin n, c.2 < c.1 → α c = 0) :
    eval (yfun y) P = eval (fun c => (y c : ℂ)) P := by
  rw [eval_eq, eval_eq]
  refine Finset.sum_congr rfl fun α hα => ?_
  congr 1
  refine Finset.prod_congr rfl fun c hc => ?_
  have : ¬ c.2 < c.1 := fun h => (Finsupp.mem_support_iff.1 hc) (hP α hα c h)
  simp [yfun, this]

/-- **Claim B.** An element of `U_{D+1}` whose degree-`(D+1)` symbol vanishes at every real
point with vanishing antisymmetric coordinates lies in `U_D + U_D 𝔨`. -/
theorem mem_of_symbol_vanish {D : ℕ} {u : UU n} (hu : u ∈ degreeFiltration ℂ (LL n) (D + 1))
    (h0 : ∀ y : Fin n × Fin n → ℝ, eval (yfun y) ((symB n).symbol (D + 1) u) = 0) :
    u ∈ degreeFiltration ℂ (LL n) D ⊔ Submodule.span ℂ
      {w | ∃ (v : UU n) (c : Fin n × Fin n), v ∈ degreeFiltration ℂ (LL n) D ∧ c.2 < c.1 ∧
        w = v * UniversalEnvelopingAlgebra.ι ℂ (bB n c)} := by
  classical
  set Wt := degreeFiltration ℂ (LL n) D ⊔ Submodule.span ℂ
      {w | ∃ (v : UU n) (c : Fin n × Fin n), v ∈ degreeFiltration ℂ (LL n) D ∧ c.2 < c.1 ∧
        w = v * UniversalEnvelopingAlgebra.ι ℂ (bB n c)}
  have hspan := degreeFiltration_le_orderedSpan ℂ (LL n) (bB n) bsList_nodup mem_bsList (D + 1) hu
  obtain ⟨coef, hcoef, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).mp hspan
  set m := orderedMonomial ℂ (LL n) (bB n) (bsList n)
  -- `P3 α`: top degree, no antisymmetric letter
  let P3 : (Fin n × Fin n →₀ ℕ) → Prop := fun α => α.degree = D + 1 ∧ ∀ c, c.2 < c.1 → α c = 0
  have hdeg : ∀ α ∈ coef.support, α.degree ≤ D + 1 := fun α hα => hcoef hα
  -- the symbol of each ordered monomial
  have hsym : ∀ α, α.degree ≤ D + 1 →
      (symB n).symbol (D + 1) (m α) = if α.degree = D + 1 then monomial α 1 else 0 :=
    fun α hα => symbol_orderedMonomial ℂ (LL n) (bB n) (symB n) symB_ξ_basis bsList_nodup
      mem_bsList hα
  -- the part outside `P3` lies in `Wt`
  have hR : Finsupp.linearCombination ℂ m (coef.filter fun α => ¬ P3 α) ∈ Wt := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun α hα => Submodule.smul_mem _ _ ?_
    have hα' := Finsupp.mem_support_iff.1 hα
    rw [Finsupp.filter_apply] at hα'
    have hnP : ¬ P3 α := by
      intro h; simp [h] at hα'
    have hαc : α ∈ coef.support := by
      rw [Finsupp.mem_support_iff]; intro h0; simp [h0] at hα'
    rcases Nat.lt_or_ge α.degree (D + 1) with hlt | hge
    · exact Submodule.mem_sup_left (degreeFiltration_mono ℂ (LL n) (by omega)
        (orderedMonomial_mem_degreeFiltration ℂ (LL n) (bB n) bsList_nodup mem_bsList α))
    · have hdeq : α.degree = D + 1 := le_antisymm (hdeg α hαc) hge
      have : ∃ c : Fin n × Fin n, c.2 < c.1 ∧ α c ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hnP ⟨hdeq, hcon⟩
      obtain ⟨c, hc, hαc'⟩ := this
      obtain ⟨l, c', hc', hl, hml⟩ := orderedMonomial_eq_mul α hc hαc'
      refine Submodule.mem_sup_right (Submodule.subset_span ⟨word ℂ (LL n) l, c', ?_, hc', hml⟩)
      have := word_mem_degreeFiltration ℂ (LL n) l
      rwa [show l.length = D by omega] at this
  -- the `P3` part has vanishing coefficients
  set c3 := coef.filter P3
  set P : MvPolynomial (Fin n × Fin n) ℂ := ∑ α ∈ c3.support, monomial α (c3 α) with hPdef
  have hcoeffP : ∀ α, P.coeff α = c3 α := by
    intro α
    rw [hPdef, coeff_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · exact (Finsupp.notMem_support_iff.1 h).symm
  have hsym3 : (symB n).symbol (D + 1) (Finsupp.linearCombination ℂ m c3) = P := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    have hP : P3 α := by
      have h1 := Finsupp.mem_support_iff.1 hα
      rw [Finsupp.filter_apply] at h1
      by_contra h; simp [h] at h1
    rw [map_smul, hsym α (le_of_eq hP.1), ite_eq_left hP.1, smul_monomial, smul_eq_mul, mul_one]
  have hRvanish : ∀ y, eval (yfun y) ((symB n).symbol (D + 1)
      (Finsupp.linearCombination ℂ m (coef.filter fun α => ¬ P3 α))) = 0 := by
    intro y
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_sum]
    refine Finset.sum_eq_zero fun α hα => ?_
    have hα' := Finsupp.mem_support_iff.1 hα
    rw [Finsupp.filter_apply] at hα'
    have hnP : ¬ P3 α := by intro h; simp [h] at hα'
    have hαc : α ∈ coef.support := by
      rw [Finsupp.mem_support_iff]; intro h0; simp [h0] at hα'
    rw [map_smul, hsym α (hdeg α hαc), smul_eval]
    split_ifs with hd
    · have : ∃ c : Fin n × Fin n, c.2 < c.1 ∧ α c ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hnP ⟨hd, hcon⟩
      obtain ⟨c, hc, hαc'⟩ := this
      rw [eval_yfun_monomial_of_low y hc hαc', mul_zero]
    · simp
  have hsplit : Finsupp.linearCombination ℂ m coef =
      Finsupp.linearCombination ℂ m c3 +
        Finsupp.linearCombination ℂ m (coef.filter fun α => ¬ P3 α) := by
    rw [← map_add, Finsupp.filter_add_filter_not]
  have hP0 : P = 0 := by
    have hsupp : ∀ α ∈ P.support, ∀ c : Fin n × Fin n, c.2 < c.1 → α c = 0 := by
      intro α hα c hc
      have h1 := MvPolynomial.mem_support_iff.1 hα
      rw [hcoeffP, Finsupp.filter_apply] at h1
      by_cases h : P3 α
      · exact h.2 c hc
      · simp [h] at h1
    refine MvPolynomial.funext_set (s := fun _ => Set.range Complex.ofReal)
      (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective) fun x hx => ?_
    have hx' : x = fun c => ((x c).re : ℂ) := by
      funext c
      obtain ⟨r, hr⟩ := hx c (Set.mem_univ c)
      rw [← hr, Complex.ofReal_re]
    rw [map_zero, hx', ← eval_yfun_of_support hsupp, ← hsym3]
    have h1 := h0 fun c => (x c).re
    rw [hsplit, map_add, map_add, hRvanish, add_zero] at h1
    exact h1
  have hc3' : c3 = 0 := by
    ext α
    rw [← hcoeffP, hP0]
    rfl
  rw [hsplit, hc3', map_zero, zero_add]
  exact hR

/-! ## Symbols evaluated at real matrices -/

/-- Evaluation of a polynomial on `𝔤𝔩_n(ℂ)` at the linear form `x ↦ tr(x S)`. -/
def evMat (S : Matrix (Fin n) (Fin n) ℝ) :
    MvPolynomial (Coord (fun _ : Unit => n)) ℂ →ₐ[ℂ] ℂ :=
  aeval fun c => (S c.2.2 c.2.1 : ℂ)

theorem evMat_ξ_tmul (S : Matrix (Fin n) (Fin n) ℝ) (z : ℂ) (X : Matrix (Fin n) (Fin n) ℝ) :
    evMat S ((realSymbol n).ξ (z ⊗ₜ X)) = z * ((X * S).trace : ℝ) := by
  rw [realSymbol_ξ_tmul, map_sum, Fintype.sum_sigma]
  simp only [Fintype.univ_unit, Finset.sum_singleton, map_smul, evMat, aeval_X, smul_eq_mul]
  rw [← Finset.univ_product_univ, Finset.sum_product, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

/-- `Ad(k)` on `ℂ ⊗ 𝔤𝔩_n(ℝ)`. -/
theorem conjLie_tmul (k : Matrix.unitaryGroup (Fin n) ℝ) (z : ℂ) (X : Matrix (Fin n) (Fin n) ℝ) :
    conjLie (orthUnit k) (z ⊗ₜ X) =
      z ⊗ₜ ((k : Matrix (Fin n) (Fin n) ℝ) * X * (star k : Matrix (Fin n) (Fin n) ℝ)) := by
  rw [conjLie_apply, orthUnit_val, orthUnit_inv_val, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem evMat_ξ_conj (S : Matrix (Fin n) (Fin n) ℝ) (k : Matrix.unitaryGroup (Fin n) ℝ)
    (x : LL n) :
    evMat S ((realSymbol n).ξ (conjLie (orthUnit k) x)) =
      evMat ((star k : Matrix (Fin n) (Fin n) ℝ) * S * (k : Matrix (Fin n) (Fin n) ℝ))
        ((realSymbol n).ξ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z X =>
    rw [conjLie_tmul, evMat_ξ_tmul, evMat_ξ_tmul]
    congr 2
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy, map_add]

/-- **Equivariance of symbols.** `σ_N(Ad(k) u)` evaluated at `S` is `σ_N(u)` evaluated at
`kᵀ S k`. -/
theorem evMat_symbol_conj (S : Matrix (Fin n) (Fin n) ℝ) (k : Matrix.unitaryGroup (Fin n) ℝ)
    {N : ℕ} {u : UU n} (hu : u ∈ degreeFiltration ℂ (LL n) N) :
    evMat S ((realSymbol n).symbol N (envMap (conjLie (orthUnit k)) u)) =
      evMat ((star k : Matrix (Fin n) (Fin n) ℝ) * S * (k : Matrix (Fin n) (Fin n) ℝ))
        ((realSymbol n).symbol N u) := by
  have hu' := degreeFiltration_le_wordSpan ℂ (LL n) N hu
  clear hu
  induction hu' using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨l, hl, rfl⟩ := hw
    rw [map_word ℂ (LL n) (envMap (conjLie (orthUnit k))) (conjLie (orthUnit k)).toLinearMap
      (fun x => envMap_ι _ x) l]
    rcases hl.lt_or_eq with hlt | heq
    · rw [(realSymbol n).symbol_word_of_length_lt _ (by simpa using hlt),
        (realSymbol n).symbol_word_of_length_lt _ hlt, map_zero, map_zero]
    · rw [(realSymbol n).symbol_word_of_length_eq _ (by simpa using heq),
        (realSymbol n).symbol_word_of_length_eq _ heq, map_list_prod, map_list_prod,
        List.map_map, List.map_map, List.map_map]
      refine congrArg List.prod (List.map_congr_left fun x _ => ?_)
      simp only [Function.comp_apply, LieHom.coe_toLinearMap]
      exact evMat_ξ_conj S k x
  | zero => simp
  | add w w' _ _ h h' => rw [map_add, map_add, map_add, h, h', map_add, map_add]
  | smul c w _ h => rw [map_smul, map_smul, map_smul, h, map_smul, map_smul]

/-- The diagonal restriction evaluated at a real point is evaluation at the diagonal matrix. -/
theorem eval_diagRes (t : Fin n → ℝ) (P : MvPolynomial (Coord (fun _ : Unit => n)) ℂ) :
    eval (fun p => (t p : ℂ)) (diagRes n P) = evMat (Matrix.diagonal t) P := by
  have h : (aeval fun p => (t p : ℂ)).comp (diagRes n) = evMat (Matrix.diagonal t) := by
    ext c
    obtain ⟨u, p, q⟩ := c
    by_cases hpq : p = q
    · subst hpq; simp [diagRes, evMat]
    · simp [diagRes, evMat, hpq, Matrix.diagonal_apply_ne _ (Ne.symm hpq)]
  exact congrArg (fun f => f P) h

/-- The symmetric matrix with upper triangular entries `y`. -/
def symMat (y : Fin n × Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun p q => if q < p then y (q, p) else y (p, q)

theorem symMat_transpose (y : Fin n × Fin n → ℝ) : (symMat y)ᵀ = symMat y := by
  ext p q
  simp only [Matrix.transpose_apply, symMat, Matrix.of_apply]
  rcases lt_trichotomy p q with h | h | h
  · simp [h, not_lt.mpr h.le]
  · subst h; simp
  · simp [h, not_lt.mpr h.le]

theorem eval_yfun_symB (y : Fin n × Fin n → ℝ) (N : ℕ) (u : UU n) :
    eval (yfun y) ((symB n).symbol N u) = evMat (symMat y) ((realSymbol n).symbol N u) := by
  rw [symB_symbol]
  have h : (aeval (yfun y)).comp (psiB n) = evMat (symMat y) := by
    ext c
    obtain ⟨u, p, q⟩ := c
    by_cases hqp : q < p
    · simp [psiB, evMat, symMat, yfun, hqp, not_lt.mpr hqp.le]
    · rcases (not_lt.mp hqp).lt_or_eq with hpq | hpq
      · simp [psiB, evMat, symMat, yfun, hqp, hpq]
      · subst hpq; simp [psiB, evMat, symMat, yfun]
  exact congrArg (fun f : MvPolynomial (Coord (fun _ : Unit => n)) ℂ →ₐ[ℂ] ℂ =>
    f ((realSymbol n).symbol N u)) h

/-- **Spectral theorem.** Every real symmetric matrix is `kᵀ diag(t) k` with `k ∈ O(n)`. -/
theorem exists_orth_diag {S : Matrix (Fin n) (Fin n) ℝ} (hS : Sᵀ = S) :
    ∃ (k : Matrix.unitaryGroup (Fin n) ℝ) (t : Fin n → ℝ),
      S = (star k : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal t * (k : Matrix (Fin n) (Fin n) ℝ) := by
  have hH : S.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hS]
  refine ⟨star hH.eigenvectorUnitary, hH.eigenvalues, ?_⟩
  conv_lhs => rw [hH.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply]

/-! ## Equivariance of the derivative of a `K`-type -/

theorem hasDerivAt_mul_entries {d : ℕ} {M : ℝ → Matrix (Fin d) (Fin d) ℂ}
    {M' : Matrix (Fin d) (Fin d) ℂ} (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) 0)
    (A B : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    HasDerivAt (fun t => (A * M t * B) i j) ((A * M' * B) i j) 0 := by
  simp only [Matrix.mul_apply]
  apply HasDerivAt.fun_sum
  intro l _
  apply HasDerivAt.mul_const
  apply HasDerivAt.fun_sum
  intro m _
  exact (hM m l).const_mul _

/-- `τ(k) D(Y) = D(k Y kᵀ) τ(k)` for antisymmetric `Y`. -/
theorem typeDerivative_conj {d : ℕ} {τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ}
    {D : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ} (hD : IsTypeDerivative τ D)
    (k : Matrix.unitaryGroup (Fin n) ℝ) (Y : Matrix (Fin n) (Fin n) ℝ) (hY : Yᵀ = -Y) :
    τ k * D Y =
      D ((k : Matrix (Fin n) (Fin n) ℝ) * Y * (star k : Matrix (Fin n) (Fin n) ℝ)) * τ k := by
  set γ0 := RealJacquetFiniteGeneration.skewCurve Y hY
  have h0 : γ0 0 = 1 := by
    apply Subtype.ext
    simp [γ0, RealJacquetFiniteGeneration.skewCurve]
  have hent0 : ∀ i j, HasDerivAt (fun t => (γ0 t : Matrix (Fin n) (Fin n) ℝ) i j) (Y i j) 0 :=
    fun i j => RealJacquetFiniteGeneration.skew_hasDerivAt_entry
      (RealJacquetFiniteGeneration.skew_hasDerivAt_exp_smul_zero Y) i j
  let γ : ℝ → Matrix.unitaryGroup (Fin n) ℝ := fun t => k * γ0 t * star k
  have hγ0 : γ 0 = 1 := by simp [γ, h0, Unitary.mul_star_self]
  have hentγ : ∀ i j, HasDerivAt (fun t => (γ t : Matrix (Fin n) (Fin n) ℝ) i j)
      (((k : Matrix (Fin n) (Fin n) ℝ) * Y * (star k : Matrix (Fin n) (Fin n) ℝ)) i j) 0 := by
    have hcurve : HasDerivAt (fun t => (k : Matrix (Fin n) (Fin n) ℝ) *
        (γ0 t : Matrix (Fin n) (Fin n) ℝ) * (star k : Matrix (Fin n) (Fin n) ℝ))
        ((k : Matrix (Fin n) (Fin n) ℝ) * Y * (star k : Matrix (Fin n) (Fin n) ℝ)) 0 :=
      ((RealJacquetFiniteGeneration.skew_hasDerivAt_exp_smul_zero Y).const_mul _).mul_const _
    intro i j
    have h := RealJacquetFiniteGeneration.skew_hasDerivAt_entry hcurve i j
    simpa [γ, Unitary.coe_star] using h
  have h1 := hD γ _ hγ0 hentγ
  have hτγ : ∀ t, τ (γ t) = τ k * τ (γ0 t) * τ (star k) := fun t => by simp [γ, map_mul]
  have h2 : ∀ i j, HasDerivAt (fun t => τ (γ t) i j) ((τ k * D Y * τ (star k)) i j) 0 := by
    intro i j
    simp only [hτγ]
    exact hasDerivAt_mul_entries (hD γ0 Y h0 hent0) _ _ i j
  have heq : D ((k : Matrix (Fin n) (Fin n) ℝ) * Y * (star k : Matrix (Fin n) (Fin n) ℝ)) =
      τ k * D Y * τ (star k) := by
    ext i j
    exact (h1 i j).unique (h2 i j)
  rw [heq, Matrix.mul_assoc (τ k * D Y), ← map_mul, Unitary.star_mul_self, map_one, Matrix.mul_one]

/-! ## The relations `u Y ⊗ x - u ⊗ D(Y) x` and the descent -/

section Descent

variable {d : ℕ} {τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ}
  {D : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ}

variable (D) in
/-- The relations `u Y ⊗ x - u ⊗ D(Y) x`, `Y` antisymmetric, as `d`-tuples over `U(𝔤)`. -/
def Kspan : Submodule ℂ (Fin d → UU n) :=
  Submodule.span ℂ {w | ∃ (u : UU n) (Y : Matrix (Fin n) (Fin n) ℝ) (x : Fin d → ℂ), Yᵀ = -Y ∧
    w = fun j => x j • (u * UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ Y)) - (D Y *ᵥ x) j • u}

theorem apply_eq_sum_single {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : (Fin d → ℂ) →ₗ[ℂ] M) (y : Fin d → ℂ) : T y = ∑ j, y j • T (Pi.single j 1) := by
  conv_lhs => rw [← Finset.univ_sum_single y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, ← Pi.single_smul, smul_eq_mul, mul_one]

/-- `Φ_T(w) = ∑ⱼ P(w j) T(e_j)`. -/
def PhiT {M : Type*} [AddCommGroup M] [Module ℂ M] (P : UU n →ₐ[ℂ] Module.End ℂ M)
    (T : (Fin d → ℂ) →ₗ[ℂ] M) : (Fin d → UU n) →ₗ[ℂ] M where
  toFun w := ∑ j, P (w j) (T (Pi.single j 1))
  map_add' w w' := by simp [Finset.sum_add_distrib]
  map_smul' c w := by simp [Finset.smul_sum]

/-- `Φ_T` kills the relations for a `K`-intertwiner `T` into a `(𝔤𝔩_n(ℝ), O(n))`-module. -/
theorem PhiT_Kspan {M : Type*} [AddCommGroup M] [Module ℂ M]
    {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) M}
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ M} (hgk : IsRealGKModule n ρ π)
    (hD : IsTypeDerivative τ D) {T : (Fin d → ℂ) →ₗ[ℂ] M} (hT : T ∈ gkIntertwiners ρ d τ)
    {w : Fin d → UU n} (hw : w ∈ Kspan D) : PhiT (envelopingAction π) T w = 0 := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨u, Y, x, hY, rfl⟩ := hw
    have h1 : ∑ j, x j • envelopingAction π (u * UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ Y))
        (T (Pi.single j 1)) = envelopingAction π u (π ((1 : ℂ) ⊗ₜ Y) (T x)) := by
      rw [apply_eq_sum_single T x, map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [envelopingAction, map_smul]
    have h2 : ∑ j, (D Y *ᵥ x) j • envelopingAction π u (T (Pi.single j 1)) =
        envelopingAction π u (T (D Y *ᵥ x)) := by
      rw [apply_eq_sum_single T (D Y *ᵥ x), map_sum]
      simp [map_smul]
    simp only [PhiT, LinearMap.coe_mk, AddHom.coe_mk, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, Finset.sum_sub_distrib]
    rw [h1, h2, apply_skew_intertwiner hgk hD hT Y hY x, sub_self]
  | zero => simp
  | add w w' _ _ h h' => rw [map_add, h, h', add_zero]
  | smul c w _ h => rw [map_smul, h, smul_zero]

variable (τ) in
/-- `QQ(w) = ∑ⱼ Q(w j, e_j)`. -/
def QQ (w : Fin d → UU n) : Fin d → MvPolynomial (Fin n) ℂ := ∑ j, Q τ (w j) (Pi.single j 1)

/-- The polynomial combination `∑ᵢ xᵢ (bᵢⱼ)ⱼ` of the rows of `b`. -/
def psiVec (b : Matrix (Fin d) (Fin d) (UU n)) (x : Fin d → ℂ) : Fin d → UU n :=
  fun j => ∑ i, x i • b i j

variable (τ) in
/-- The action `w ↦ (Ad(k) ⊗ τ(k)) w` of `O(n)` on `d`-tuples. -/
def gAct (k : Matrix.unitaryGroup (Fin n) ℝ) (w : Fin d → UU n) : Fin d → UU n :=
  fun j => ∑ l, τ k j l • envMap (conjLie (orthUnit k)) (w l)

section QQ

variable (hτ : Continuous τ) (hD : IsTypeDerivative τ D)

include hτ hD in
theorem Q_sub (u u' : UU n) (v : Fin d → ℂ) : Q τ (u - u') v = Q τ u v - Q τ u' v := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ u', Q_add hτ hD, Q_smul hτ hD]
  funext i
  simp [sub_eq_add_neg]

include hτ hD in
theorem QQ_add (w w' : Fin d → UU n) : QQ τ (w + w') = QQ τ w + QQ τ w' := by
  simp only [QQ, Pi.add_apply, Q_add hτ hD, Finset.sum_add_distrib]

include hτ hD in
theorem QQ_smul (c : ℂ) (w : Fin d → UU n) : QQ τ (c • w) = fun m => C c * QQ τ w m := by
  funext m
  simp only [QQ, Pi.smul_apply, Q_smul hτ hD, Finset.sum_apply, Finset.mul_sum]

include hτ hD in
theorem QQ_sub (w w' : Fin d → UU n) : QQ τ (w - w') = QQ τ w - QQ τ w' := by
  simp only [QQ, Pi.sub_apply, Q_sub hτ hD, Finset.sum_sub_distrib]

include hτ hD in
theorem QQ_zero : QQ τ (0 : Fin d → UU n) = 0 := by
  have h := QQ_smul hτ hD 0 (0 : Fin d → UU n)
  simp only [zero_smul, map_zero, zero_mul] at h
  rw [h]
  rfl

include hτ hD in
/-- `QQ` kills the relations. -/
theorem QQ_Kspan {w : Fin d → UU n} (hw : w ∈ Kspan D) : QQ τ w = 0 := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨u, Y, x, hY, rfl⟩ := hw
    have h1 : ∀ j, Q τ (x j • (u * UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ Y)))
        (Pi.single j 1) = Q τ (u * UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ Y))
          (Pi.single j (x j)) := by
      intro j
      rw [Q_smul hτ hD, show (Pi.single j (x j) : Fin d → ℂ) = x j • Pi.single j 1 by
        rw [← Pi.single_smul, smul_eq_mul, mul_one], Q_smul_right hτ hD]
    have h2 : ∀ j, Q τ ((D Y *ᵥ x) j • u) (Pi.single j 1) = Q τ u (Pi.single j ((D Y *ᵥ x) j)) := by
      intro j
      rw [Q_smul hτ hD, show (Pi.single j ((D Y *ᵥ x) j) : Fin d → ℂ) = (D Y *ᵥ x) j • Pi.single j 1 by
        rw [← Pi.single_smul, smul_eq_mul, mul_one], Q_smul_right hτ hD]
    simp only [QQ, Q_sub hτ hD, Finset.sum_sub_distrib, h1, h2]
    rw [← Q_sum_right hτ hD, ← Q_sum_right hτ hD, Finset.univ_sum_single, Finset.univ_sum_single,
      Q_mul_skew hτ hD u Y hY x, sub_self]
  | zero => exact QQ_zero hτ hD
  | add w w' _ _ h h' => rw [QQ_add hτ hD, h, h', add_zero]
  | smul c w _ h => rw [QQ_smul hτ hD, h]; funext m; simp

include hτ hD in
theorem Q_one (v : Fin d → ℂ) : Q τ 1 v = fun i => C (v i) := by
  refine Q_eq hτ hD fun a e T hT => ?_
  have : evalVec a (fun i => C (v i)) = v := by funext i; simp [evalVec]
  rw [this, lam_one]

include hτ hD in
theorem QQ_const (r : Fin d → ℂ) : QQ τ (fun j => algebraMap ℂ (UU n) (r j)) = fun m => C (r m) := by
  funext m
  simp only [QQ, Finset.sum_apply]
  have : ∀ j, Q τ (algebraMap ℂ (UU n) (r j)) (Pi.single j 1) =
      fun i => C (r j) * C ((Pi.single j (1 : ℂ) : Fin d → ℂ) i) := by
    intro j
    rw [Algebra.algebraMap_eq_smul_one, Q_smul hτ hD, Q_one hτ hD]
  simp only [this]
  rw [Finset.sum_eq_single m]
  · simp
  · intro j _ hjm; simp [Pi.single_eq_of_ne' hjm]
  · simp

include hτ hD in
/-- The top-degree part of `QQ(w)` is the diagonal restriction of the symbol. -/
theorem QQ_degree {N : ℕ} {w : Fin d → UU n} (hw : ∀ j, w j ∈ degreeFiltration ℂ (LL n) N)
    (m : Fin d) : homogeneousComponent N (QQ τ w m) = diagRes n ((realSymbol n).symbol N (w m)) := by
  simp only [QQ, Finset.sum_apply, map_sum]
  rw [Finset.sum_eq_single m]
  · rw [(Q_degree hτ hD (hw m) (Pi.single m 1)).2 m]
    simp
  · intro j _ hjm
    rw [(Q_degree hτ hD (hw j) (Pi.single j 1)).2 m]
    simp [Pi.single_eq_of_ne' hjm]
  · simp

include hτ hD in
/-- `QQ` of a combination of rows is the corresponding combination of columns of `ĉ(b)`. -/
theorem QQ_psiVec (b : Matrix (Fin d) (Fin d) (UU n)) (x : Fin d → ℂ) (m : Fin d) :
    QQ τ (psiVec b x) m = ∑ i, C (x i) * chat τ b m i := by
  simp only [QQ, psiVec, Finset.sum_apply, chat, Matrix.of_apply]
  have : ∀ j, Q τ (∑ i, x i • b i j) (Pi.single j 1) =
      ∑ i, fun l => C (x i) * Q τ (b i j) (Pi.single j 1) l := by
    intro j
    induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      have := Q_smul hτ hD 0 (0 : UU n) (Pi.single j 1)
      simp only [zero_smul, map_zero, zero_mul] at this
      rw [this]; rfl
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, Q_add hτ hD, ih, Q_smul hτ hD]
  simp only [this, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

end QQ

theorem psiVec_single (b : Matrix (Fin d) (Fin d) (UU n)) (i : Fin d) :
    psiVec b (Pi.single i 1) = fun j => b i j := by
  funext j
  simp only [psiVec]
  rw [Finset.sum_eq_single i]
  · simp
  · intro i' _ hi'; simp [Pi.single_eq_of_ne hi']
  · simp

/-- `K`-invariance of `b`: `ψ_b(τ(k) x) = (Ad(k) ⊗ τ(k)) ψ_b(x)`. -/
theorem psiVec_conj {b : Matrix (Fin d) (Fin d) (UU n)} (hb : InB τ b)
    (k : Matrix.unitaryGroup (Fin n) ℝ) (x : Fin d → ℂ) :
    psiVec b (τ k *ᵥ x) = gAct τ k (psiVec b x) := by
  funext j
  have hent : ∀ m, ∑ l, τ k j l • envMap (conjLie (orthUnit k)) (b m l) =
      ∑ i, τ k i m • b i j := by
    intro m
    have h := congrFun (congrFun (hb k) m) j
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply] at h
    rw [show ∑ i, τ k i m • b i j = ∑ i, algebraMap ℂ (UU n) (τ k i m) * b i j from
      Finset.sum_congr rfl fun i _ => Algebra.smul_def _ _, h]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Algebra.smul_def, Algebra.commutes]
  have lhs : psiVec b (τ k *ᵥ x) j = ∑ m, x m • ∑ i, τ k i m • b i j := by
    simp only [psiVec, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  have rhs : gAct τ k (psiVec b x) j =
      ∑ m, x m • ∑ l, τ k j l • envMap (conjLie (orthUnit k)) (b m l) := by
    simp only [gAct, psiVec, map_sum, map_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
  rw [lhs, rhs]
  simp only [hent]

/-- `gAct` preserves the relations. -/
theorem gAct_Kspan (hD : IsTypeDerivative τ D) (k : Matrix.unitaryGroup (Fin n) ℝ)
    {w : Fin d → UU n} (hw : w ∈ Kspan D) : gAct τ k w ∈ Kspan D := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨u, Y, x, hY, rfl⟩ := hw
    set Y' := (k : Matrix (Fin n) (Fin n) ℝ) * Y * (star k : Matrix (Fin n) (Fin n) ℝ)
    have hY' : Y'ᵀ = -Y' := by
      simp only [Y', Matrix.transpose_mul, hY, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose,
        Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    refine Submodule.subset_span ⟨envMap (conjLie (orthUnit k)) u, Y', τ k *ᵥ x, hY', ?_⟩
    funext j
    have hι : envMap (conjLie (orthUnit k)) (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ Y)) =
        UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ Y') := by
      rw [envMap_ι, conjLie_tmul]
    have hDx : D Y' *ᵥ (τ k *ᵥ x) = τ k *ᵥ (D Y *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, typeDerivative_conj hD k Y hY]
    rw [hDx]
    simp only [gAct, map_sub, map_smul, map_mul, hι, smul_sub, Finset.sum_sub_distrib,
      Matrix.mulVec, dotProduct, Finset.sum_smul, smul_smul, map_sum, Finset.smul_sum,
      Finset.mul_sum]
  | zero =>
    have : gAct τ k (0 : Fin d → UU n) = 0 := by funext j; simp [gAct]
    rw [this]; exact Submodule.zero_mem _
  | add w w' _ _ h h' =>
    have : gAct τ k (w + w') = gAct τ k w + gAct τ k w' := by
      funext j; simp [gAct, Finset.sum_add_distrib]
    rw [this]; exact Submodule.add_mem _ h h'
  | smul c w _ h =>
    have : gAct τ k (c • w) = c • gAct τ k w := by
      funext j; simp [gAct, Finset.smul_sum, smul_comm c]
    rw [this]; exact Submodule.smul_mem _ c h

theorem gAct_sub (k : Matrix.unitaryGroup (Fin n) ℝ) (w w' : Fin d → UU n) :
    gAct τ k (w - w') = gAct τ k w - gAct τ k w' := by
  funext j; simp [gAct, smul_sub, Finset.sum_sub_distrib]

theorem gAct_mem_degreeFiltration (k : Matrix.unitaryGroup (Fin n) ℝ) {N : ℕ}
    {w : Fin d → UU n} (hw : ∀ j, w j ∈ degreeFiltration ℂ (LL n) N) (j : Fin d) :
    gAct τ k w j ∈ degreeFiltration ℂ (LL n) N := by
  refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ ?_
  exact algHom_mem_degreeFiltration ℂ (LL n) (LL n) _ (fun x => by
    rw [envMap_ι]; exact generator_mem_degreeOne ℂ (LL n) _) (hw l)

end Descent

/-! ## Injectivity -/

section Injectivity

variable {d : ℕ} {τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ}
  {D : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ}

variable (D) in
/-- The relations plus the `d`-tuples in `U_N`. -/
def WN (N : ℕ) : Submodule ℂ (Fin d → UU n) :=
  Kspan D ⊔ Submodule.pi Set.univ (fun _ : Fin d => degreeFiltration ℂ (LL n) N)

theorem single_mem_WN {N : ℕ} {u : UU n}
    (hu : u ∈ degreeFiltration ℂ (LL n) N ⊔ Submodule.span ℂ
      {w | ∃ (v : UU n) (c : Fin n × Fin n), v ∈ degreeFiltration ℂ (LL n) N ∧ c.2 < c.1 ∧
        w = v * UniversalEnvelopingAlgebra.ι ℂ (bB n c)}) (l : Fin d) :
    (Pi.single l u : Fin d → UU n) ∈ WN D N := by
  classical
  have hpi : ∀ v ∈ degreeFiltration ℂ (LL n) N, (Pi.single l v : Fin d → UU n) ∈
      Submodule.pi Set.univ (fun _ : Fin d => degreeFiltration ℂ (LL n) N) := by
    intro v hv j _
    by_cases hj : j = l
    · subst hj; simpa using hv
    · simp [Pi.single_eq_of_ne hj]
  suffices h : degreeFiltration ℂ (LL n) N ⊔ Submodule.span ℂ
      {w | ∃ (v : UU n) (c : Fin n × Fin n), v ∈ degreeFiltration ℂ (LL n) N ∧ c.2 < c.1 ∧
        w = v * UniversalEnvelopingAlgebra.ι ℂ (bB n c)} ≤
      (WN D N).comap (LinearMap.single ℂ (fun _ : Fin d => UU n) l) from h hu
  refine sup_le (fun v hv => Submodule.mem_sup_right (hpi v hv)) (Submodule.span_le.2 ?_)
  rintro _ ⟨v, c, hv, hc, rfl⟩
  set Y : Matrix (Fin n) (Fin n) ℝ := Matrix.single c.1 c.2 1 - Matrix.single c.2 c.1 1
  have hbY : bB n c = (1 : ℂ) ⊗ₜ Y := by rw [bB_apply, ite_eq_left hc]
  have hY : Yᵀ = -Y := by
    simp [Y, Matrix.transpose_sub, Matrix.transpose_single]
  have hgen : (fun j => (Pi.single l (1 : ℂ) : Fin d → ℂ) j • (v * UniversalEnvelopingAlgebra.ι ℂ
      ((1 : ℂ) ⊗ₜ Y)) - (D Y *ᵥ Pi.single l 1) j • v) ∈ Kspan D :=
    Submodule.subset_span ⟨v, Y, Pi.single l 1, hY, rfl⟩
  have hrest : (fun j => (D Y *ᵥ Pi.single l (1 : ℂ)) j • v) ∈
      Submodule.pi Set.univ (fun _ : Fin d => degreeFiltration ℂ (LL n) N) :=
    fun j _ => Submodule.smul_mem _ _ hv
  have heq : (Pi.single l (v * UniversalEnvelopingAlgebra.ι ℂ (bB n c)) : Fin d → UU n) =
      (fun j => (Pi.single l (1 : ℂ) : Fin d → ℂ) j • (v * UniversalEnvelopingAlgebra.ι ℂ
        ((1 : ℂ) ⊗ₜ Y)) - (D Y *ᵥ Pi.single l 1) j • v) +
      (fun j => (D Y *ᵥ Pi.single l (1 : ℂ)) j • v) := by
    funext j
    by_cases hj : j = l
    · subst hj; simp [hbY]
    · simp [Pi.single_eq_of_ne hj]
  change (Pi.single l (v * UniversalEnvelopingAlgebra.ι ℂ (bB n c)) : Fin d → UU n) ∈ WN D N
  rw [heq]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hgen) (Submodule.mem_sup_right hrest)

variable (hτ : Continuous τ) (hD : IsTypeDerivative τ D)

include hτ hD in
/-- **The descent.** For `K`-invariant `b` with `ĉ(b) = 0`, every combination of the rows of
`b` is a combination of the relations `u Y ⊗ x - u ⊗ D(Y) x`. -/
theorem psiVec_mem_Kspan {b : Matrix (Fin d) (Fin d) (UU n)} (hb : InB τ b)
    (h0 : chat τ b = 0) (x : Fin d → ℂ) : psiVec b x ∈ Kspan D := by
  classical
  have hQQ0 : ∀ y, QQ τ (psiVec b y) = 0 := by
    intro y; funext m; rw [QQ_psiVec hτ hD, h0]; simp
  have hlin : ∀ y, psiVec b y = ∑ i, y i • psiVec b (Pi.single i 1) := by
    intro y; funext j
    simp [psiVec_single, psiVec, Finset.sum_apply]
  have step : ∀ N, (∀ y, psiVec b y ∈ WN D (N + 1)) → ∀ y, psiVec b y ∈ WN D N := by
    intro N hN
    choose κ hκ w hw hκw using fun i => Submodule.mem_sup.1 (hN (Pi.single i 1))
    set wx : (Fin d → ℂ) → (Fin d → UU n) := fun y => ∑ i, y i • w i with hwxdef
    have hwx : ∀ y j, wx y j ∈ degreeFiltration ℂ (LL n) (N + 1) := by
      intro y j
      simp only [hwxdef, Finset.sum_apply, Pi.smul_apply]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        ((Submodule.mem_pi.1 (hw i)) j (Set.mem_univ j))
    have hdiff : ∀ y, psiVec b y - wx y ∈ Kspan D := by
      intro y
      have : psiVec b y - wx y = ∑ i, y i • κ i := by
        rw [hlin y, hwxdef, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hκw i, ← smul_sub, add_sub_cancel_right]
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hκ i)
    have hvan : ∀ y l (S : Matrix (Fin n) (Fin n) ℝ), Sᵀ = S →
        evMat S ((realSymbol n).symbol (N + 1) (wx y l)) = 0 := by
      intro y l S hS
      obtain ⟨k, t, rfl⟩ := exists_orth_diag hS
      have hg : QQ τ (gAct τ k (wx y)) = 0 := by
        have h1 : gAct τ k (wx y) = psiVec b (τ k *ᵥ y) - gAct τ k (psiVec b y - wx y) := by
          rw [psiVec_conj hb, gAct_sub]; abel
        rw [h1, QQ_sub hτ hD, hQQ0, QQ_Kspan hτ hD (gAct_Kspan hD k (hdiff y)), sub_self]
      set v : Fin d → ℂ := fun l => evMat ((star k : Matrix (Fin n) (Fin n) ℝ) *
        Matrix.diagonal t * (k : Matrix (Fin n) (Fin n) ℝ)) ((realSymbol n).symbol (N + 1) (wx y l))
      have hτv : τ k *ᵥ v = 0 := by
        funext m
        have h1 := QQ_degree hτ hD (gAct_mem_degreeFiltration (τ := τ) k (hwx y)) m
        rw [hg, Pi.zero_apply, map_zero] at h1
        have h2 := congrArg (eval fun p => (t p : ℂ)) h1
        rw [map_zero, eval_diagRes] at h2
        simp only [gAct, map_sum, map_smul, smul_eq_mul] at h2
        simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, v]
        refine Eq.trans ?_ h2.symm
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [evMat_symbol_conj _ k (hwx y l)]
      have hv0 : v = 0 := by
        have h := congrArg (fun z => τ (star k) *ᵥ z) hτv
        simp only [Matrix.mulVec_mulVec, ← map_mul, Unitary.star_mul_self, map_one,
          Matrix.one_mulVec, Matrix.mulVec_zero] at h
        exact h
      exact congrFun hv0 l
    intro y
    have hwxN : wx y ∈ WN D N := by
      rw [← Finset.univ_sum_single (wx y)]
      refine Submodule.sum_mem _ fun l _ => single_mem_WN ?_ l
      refine mem_of_symbol_vanish (hwx y l) fun y' => ?_
      rw [eval_yfun_symB]
      exact hvan y l (symMat y') (symMat_transpose y')
    have : psiVec b y = (psiVec b y - wx y) + wx y := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hdiff y)) hwxN
  have top : ∃ N, ∀ y, psiVec b y ∈ WN D N := by
    choose f hf using fun ij : Fin d × Fin d => exists_mem_degreeFiltration ℂ (LL n) (b ij.1 ij.2)
    refine ⟨Finset.univ.sup f, fun y => Submodule.mem_sup_right ?_⟩
    intro j _
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    exact degreeFiltration_mono ℂ (LL n) (Finset.le_sup (Finset.mem_univ (i, j))) (hf (i, j))
  have base : ∀ y, psiVec b y ∈ WN D 0 → psiVec b y ∈ Kspan D := by
    intro y hy
    obtain ⟨κ, hκ, c, hc, hκc⟩ := Submodule.mem_sup.1 hy
    have hc' : ∀ j, ∃ r : ℂ, algebraMap ℂ (UU n) r = c j := fun j => by
      have := (Submodule.mem_pi.1 hc) j (Set.mem_univ j)
      rw [degreeFiltration_zero] at this
      exact Submodule.mem_one.1 this
    choose r hr using hc'
    have hcr : c = fun j => algebraMap ℂ (UU n) (r j) := funext fun j => (hr j).symm
    have hQ := hQQ0 y
    rw [← hκc, QQ_add hτ hD, QQ_Kspan hτ hD hκ, zero_add, hcr, QQ_const hτ hD] at hQ
    have hr0 : ∀ j, r j = 0 := fun j => by simpa using congrFun hQ j
    have hc0 : c = 0 := by rw [hcr]; funext j; simp [hr0 j]
    rw [← hκc, hc0, add_zero]
    exact hκ
  obtain ⟨N, hN⟩ := top
  have key : ∀ N, (∀ y, psiVec b y ∈ WN D N) → ∀ y, psiVec b y ∈ WN D 0 := by
    intro N
    induction N with
    | zero => exact id
    | succ N ih => exact fun h => ih (step N h)
  exact base x (key N hN x)

include hτ hD in
/-- **Injectivity of the principal-series projection.** If `ĉ(b) = 0` for `K`-invariant `b`,
then `b` acts by zero on the `K`-intertwiners from `τ` into every `(𝔤𝔩_n(ℝ), O(n))`-module. -/
theorem act_eq_zero_of_chat_eq_zero {b : Matrix (Fin d) (Fin d) (UU n)} (hb : InB τ b)
    (h0 : chat τ b = 0) {M : Type*} [AddCommGroup M] [Module ℂ M]
    {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) M}
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ M} (hgk : IsRealGKModule n ρ π)
    {T : (Fin d → ℂ) →ₗ[ℂ] M} (hT : T ∈ gkIntertwiners ρ d τ) :
    act (envelopingAction π) b T = 0 := by
  refine LinearMap.pi_ext fun i c => ?_
  rw [act_single, LinearMap.zero_apply]
  have hrow := psiVec_mem_Kspan hτ hD hb h0 (Pi.single i 1)
  rw [psiVec_single] at hrow
  have := PhiT_Kspan hgk hD hT hrow
  simp only [PhiT, LinearMap.coe_mk, AddHom.coe_mk] at this
  rw [this, smul_zero]

end Injectivity

end RealSubquotient

end Langlands.Archimedean
