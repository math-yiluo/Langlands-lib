import Langlands.Theta.WeilIndex.OneDimensional
import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# The Weil index and the invariants of a quadratic space

GKT §3.3.1: the determinant and the Hasse invariant of a quadratic space, **Propositions 3.29** and
**3.30** (p. 88); Appendix B.2: **Definition B.28** and **Proposition B.29** (p. 617), with the
symmetric case of **Proposition B.27** (`det(V₁ ⊕ V₂) = det V₁ det V₂`, p. 617).

* `diagonalWeights q`: a diagonalization `q ≅ ⟨a₁, …, aₙ⟩` chosen once and for all (Mathlib's
  `equivalent_weightedSumSquares_units_of_nondegenerate'` gives one when `2 ≠ 0` and `q` is
  non-degenerate); `quadraticDet q = ∏ aᵢ`, the determinant, well defined in `Fˣ / Fˣ²`
  (`exists_prod_eq_quadraticDet_mul_sq`, from the discriminant of Mathlib's matrix of `q`). Any
  field with `2 ≠ 0`.
* Over a nonarchimedean local field with `2 ≠ 0`: `diagonalHasseInvariant a = ∏_{i<j} (aᵢ, aⱼ)_F`
  and `hasseInvariant q` (Definition B.28). Proposition 3.29 is first proved for a given
  diagonalization (`weilIndex_eq_of_isometryEquiv_weightedSumSquares`, from Proposition 3.19 (b)
  by induction); since the Weil index depends only on the isometry class (Corollary 3.14) and
  `γ(a, ψ)` only on `a` modulo squares (Proposition 3.19 (a)), the Hasse invariant does not depend
  on the diagonalization (Proposition B.29 (a), `diagonalHasseInvariant_eq_hasseInvariant`): the
  book calls this "well-known"; here it follows from 3.29. Then B.29 (b), (c) and 3.30.
-/

noncomputable section

namespace Langlands.Theta

open HarmonicAnalysis LocalClassField QuadraticMap

/-! ### Diagonalizations and the determinant -/

section Field

variable {F : Type} [Field F]

/-- `⟨a₁, …, aₙ⟩(x) = ∑ aᵢ xᵢ²`. -/
theorem weightedSumSquares_units_apply {ι : Type} [Fintype ι] (a : ι → Fˣ) (x : ι → F) :
    weightedSumSquares F a x = ∑ i, (a i : F) * x i ^ 2 := by
  rw [weightedSumSquares_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Units.smul_def, smul_eq_mul, pow_two]

/-- The matrix of `⟨a₁, …, aₙ⟩` is the diagonal matrix of the `aᵢ`. -/
theorem toMatrix'_weightedSumSquares [Invertible (2 : F)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : ι → Fˣ) :
    QuadraticForm.toMatrix' (weightedSumSquares F a) = Matrix.diagonal fun i => (a i : F) := by
  ext i j
  rw [QuadraticForm.toMatrix', LinearMap.toMatrix₂'_apply]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, QuadraticMap.associated_eq_self_apply,
      weightedSumSquares_units_apply,
      Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
    simp
  · rw [Matrix.diagonal_apply_ne _ hij, QuadraticMap.associated_apply,
      weightedSumSquares_units_apply, weightedSumSquares_units_apply,
      weightedSumSquares_units_apply, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      Finset.sum_eq_zero, smul_zero]
    intro k _
    have h0 : (Pi.single i (1 : F) : ι → F) k * (Pi.single j (1 : F) : ι → F) k = 0 := by
      by_cases hk : k = i
      · subst hk; simp [hij]
      · simp [Pi.single_apply, hk]
    simp only [Pi.add_apply]
    linear_combination (2 * (a k : F)) * h0

/-- The polar form of `⟨a₁, …, aₙ⟩` is non-degenerate (`aᵢ ≠ 0`, `2 ≠ 0`). -/
theorem separatingLeft_polarBilin_weightedSumSquares [NeZero (2 : F)] {ι : Type} [Fintype ι]
    [DecidableEq ι] (a : ι → Fˣ) : (polarBilin (weightedSumSquares F a)).SeparatingLeft := by
  intro x hx
  funext i
  have h := hx (Pi.single i (1 : F))
  rw [polarBilin_apply_apply, polar, weightedSumSquares_units_apply,
    weightedSumSquares_units_apply, weightedSumSquares_units_apply, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib] at h
  have h1 : ∀ k, (a k : F) * (x + (Pi.single i (1 : F) : ι → F)) k ^ 2 - (a k : F) * x k ^ 2 -
      (a k : F) * (Pi.single i (1 : F) : ι → F) k ^ 2 =
        2 * (a k : F) * x k * (Pi.single i (1 : F) : ι → F) k := by
    intro k; simp only [Pi.add_apply]; ring
  simp_rw [h1] at h
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)] at h
  simpa [two_ne_zero, (a i).ne_zero] using h

/-- **The determinant is well defined in `Fˣ / Fˣ²`** for diagonal forms: if `⟨a₁, …, aₙ⟩` and
`⟨b₁, …, bₙ⟩` are isometric, `∏ aᵢ = ∏ bᵢ u²` (Mathlib's `QuadraticForm.discr'_comp`). -/
theorem exists_prod_eq_prod_mul_sq [NeZero (2 : F)] {ι : Type} [Fintype ι] [DecidableEq ι]
    {a b : ι → Fˣ} (e : (weightedSumSquares F a).IsometryEquiv (weightedSumSquares F b)) :
    ∃ u : Fˣ, ∏ i, a i = (∏ i, b i) * u ^ 2 := by
  have : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have hQ : (weightedSumSquares F a : QuadraticForm F (ι → F)) =
      (weightedSumSquares F b).comp (e.toLinearEquiv : (ι → F) →ₗ[F] ι → F) := by
    ext x
    rw [QuadraticMap.comp_apply]
    exact (e.map_app x).symm
  have hd := QuadraticForm.discr'_comp (Q := (weightedSumSquares F b : QuadraticForm F (ι → F)))
    (e.toLinearEquiv : (ι → F) →ₗ[F] ι → F)
  rw [← hQ] at hd
  simp only [QuadraticForm.discr', toMatrix'_weightedSumSquares, Matrix.det_diagonal,
    LinearMap.det_toMatrix'] at hd
  obtain ⟨u, hu⟩ := e.toLinearEquiv.isUnit_det'
  refine ⟨u, Units.ext ?_⟩
  push_cast
  rw [hd, hu]
  ring

variable {V : Type} [AddCommGroup V] [Module F V]

open Classical in
/-- **A diagonalization of `q`**, chosen once and for all: weights `a₁, …, aₙ ∈ Fˣ`
(`n = dim V`) with `q ≅ ⟨a₁, …, aₙ⟩` if there are such (for instance if `2 ≠ 0` and `q` is
non-degenerate, `equivalent_diagonalWeights`), and `1` otherwise. -/
def diagonalWeights (q : QuadraticForm F V) : Fin (Module.finrank F V) → Fˣ :=
  if h : ∃ w : Fin (Module.finrank F V) → Fˣ, q.Equivalent (weightedSumSquares F w) then h.choose
  else 1

/-- **The determinant** `det(q) = ∏ aᵢ` of a quadratic space (GKT §3.3.1, p. 88; Definition B.23),
for the chosen diagonalization `diagonalWeights q`: a representative of the class in `Fˣ / Fˣ²`
(`exists_prod_eq_quadraticDet_mul_sq`). -/
def quadraticDet (q : QuadraticForm F V) : Fˣ :=
  ∏ i, diagonalWeights q i

theorem equivalent_diagonalWeights_of_exists (q : QuadraticForm F V)
    (h : ∃ w : Fin (Module.finrank F V) → Fˣ, q.Equivalent (weightedSumSquares F w)) :
    q.Equivalent (weightedSumSquares F (diagonalWeights q)) := by
  rw [diagonalWeights]
  split_ifs with h'
  · exact h'.choose_spec
  · exact absurd h h'

/-- If `2 ≠ 0` and `q` is non-degenerate, `q ≅ ⟨a₁, …, aₙ⟩` for `a = diagonalWeights q`. -/
theorem equivalent_diagonalWeights [NeZero (2 : F)] [FiniteDimensional F V] (q : QuadraticForm F V)
    (hq : (polarBilin q).SeparatingLeft) :
    q.Equivalent (weightedSumSquares F (diagonalWeights q)) := by
  have : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  exact equivalent_diagonalWeights_of_exists q
    (QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate' q
      ((separatingLeft_associated_iff q).2 hq))

/-- A diagonalization has `dim V` weights. -/
theorem finrank_eq_of_isometryEquiv (q : QuadraticForm F V) {n : ℕ} {a : Fin n → Fˣ}
    (e : q.IsometryEquiv (weightedSumSquares F a)) : Module.finrank F V = n := by
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]

/-- If `q` has a diagonalization, `diagonalWeights q` is one. -/
theorem equivalent_diagonalWeights_of_isometryEquiv (q : QuadraticForm F V) {n : ℕ}
    {a : Fin n → Fˣ} (e : q.IsometryEquiv (weightedSumSquares F a)) :
    q.Equivalent (weightedSumSquares F (diagonalWeights q)) := by
  have hn := finrank_eq_of_isometryEquiv q e
  subst hn
  exact equivalent_diagonalWeights_of_exists q ⟨a, ⟨e⟩⟩

/-- **The determinant is well defined in `Fˣ / Fˣ²`** (GKT Proposition B.24 for quadratic spaces):
for every diagonalization `q ≅ ⟨a₁, …, aₙ⟩`, `∏ aᵢ = det(q) u²` for some `u ∈ Fˣ`. -/
theorem exists_prod_eq_quadraticDet_mul_sq [NeZero (2 : F)] (q : QuadraticForm F V) {n : ℕ}
    {a : Fin n → Fˣ} (e : q.IsometryEquiv (weightedSumSquares F a)) :
    ∃ u : Fˣ, ∏ i, a i = quadraticDet q * u ^ 2 := by
  have hn := finrank_eq_of_isometryEquiv q e
  subst hn
  obtain ⟨e₀⟩ := equivalent_diagonalWeights_of_isometryEquiv q e
  exact exists_prod_eq_prod_mul_sq (e.symm.trans e₀)

/-- Isometric non-degenerate quadratic spaces have the same determinant in `Fˣ / Fˣ²`. -/
theorem exists_quadraticDet_eq_mul_sq_of_isometryEquiv [NeZero (2 : F)] {V' : Type}
    [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] {q : QuadraticForm F V}
    {q' : QuadraticForm F V'} (e : q.IsometryEquiv q') (hq' : (polarBilin q').SeparatingLeft) :
    ∃ u : Fˣ, quadraticDet q' = quadraticDet q * u ^ 2 := by
  obtain ⟨e'⟩ := equivalent_diagonalWeights q' hq'
  exact exists_prod_eq_quadraticDet_mul_sq q (e.trans e')

namespace WeilIndex.Internal

/-- `(x, y) ↦ (x₁, …, x_m, y₁, …, y_k)` as a linear equivalence. -/
def appendLinearEquiv (m k : ℕ) : ((Fin m → F) × (Fin k → F)) ≃ₗ[F] (Fin (m + k) → F) where
  __ := Fin.appendEquiv m k
  map_add' x y := by
    funext i
    induction i using Fin.addCases with
    | left i => simp [Fin.appendEquiv]
    | right i => simp [Fin.appendEquiv]
  map_smul' c x := by
    funext i
    induction i using Fin.addCases with
    | left i => simp [Fin.appendEquiv]
    | right i => simp [Fin.appendEquiv]

/-- `⟨a⟩ ⊕ ⟨b⟩ ≅ ⟨a, b⟩`. -/
def appendIsometryEquiv {m k : ℕ} (a : Fin m → Fˣ) (b : Fin k → Fˣ) :
    ((weightedSumSquares F a).prod (weightedSumSquares F b)).IsometryEquiv
      (weightedSumSquares F (Fin.append a b)) where
  __ := appendLinearEquiv m k
  map_app' x := by
    change weightedSumSquares F (Fin.append a b) (Fin.append x.1 x.2) = _
    rw [QuadraticMap.prod_apply, weightedSumSquares_units_apply, weightedSumSquares_units_apply,
      weightedSumSquares_units_apply, Fin.sum_univ_add]
    simp

end WeilIndex.Internal

open WeilIndex.Internal

variable {V' : Type} [AddCommGroup V'] [Module F V']

/-- **GKT Proposition B.27** for quadratic spaces: `det(V₁ ⊕ V₂) = det(V₁) det(V₂)` in
`Fˣ / Fˣ²`. -/
theorem exists_quadraticDet_prod [NeZero (2 : F)] [FiniteDimensional F V] [FiniteDimensional F V']
    (q : QuadraticForm F V) (q' : QuadraticForm F V') (hq : (polarBilin q).SeparatingLeft)
    (hq' : (polarBilin q').SeparatingLeft) :
    ∃ u : Fˣ, quadraticDet q * quadraticDet q' = quadraticDet (q.prod q') * u ^ 2 := by
  obtain ⟨e⟩ := equivalent_diagonalWeights q hq
  obtain ⟨e'⟩ := equivalent_diagonalWeights q' hq'
  obtain ⟨u, hu⟩ := exists_prod_eq_quadraticDet_mul_sq (q.prod q')
    ((e.prod e').trans (appendIsometryEquiv _ _))
  refine ⟨u, ?_⟩
  rw [← hu, Fin.prod_univ_add]
  simp [quadraticDet]

end Field

/-! ### The Hasse invariant and the Weil index -/

section LocalField

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [NeZero (2 : F)]

attribute [local instance] WeilIndex.Internal.secondCountableTopology_self
  WeilIndex.Internal.locallyCompactSpace_self WeilIndex.Internal.compactOpenExhaustion_self

/-- **The Hasse invariant of a diagonal form** `⟨a₁, …, aₙ⟩`: `∏_{i<j} (aᵢ, aⱼ)_F`
(GKT Definition B.28, §3.3.1). -/
def diagonalHasseInvariant {n : ℕ} (a : Fin n → Fˣ) : ℤˣ :=
  ∏ j, ∏ i, if i < j then hilbertSymbol F (a i) (a j) else 1

/-- **The Hasse invariant** `h(q) = ∏_{i<j} (aᵢ, aⱼ)_F` of a quadratic space (GKT Definition B.28),
for the chosen diagonalization; by Proposition B.29 (a) (`diagonalHasseInvariant_eq_hasseInvariant`)
every diagonalization gives it. -/
def hasseInvariant {V : Type} [AddCommGroup V] [Module F V] (q : QuadraticForm F V) : ℤˣ :=
  diagonalHasseInvariant (diagonalWeights q)

theorem diagonalHasseInvariant_castSucc {n : ℕ} (a : Fin (n + 1) → Fˣ) :
    diagonalHasseInvariant a = diagonalHasseInvariant (fun i => a (Fin.castSucc i)) *
      ∏ i : Fin n, hilbertSymbol F (a (Fin.castSucc i)) (a (Fin.last n)) := by
  simp only [diagonalHasseInvariant]
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    rw [Fin.prod_univ_castSucc]
    simp [Fin.castSucc_lt_castSucc_iff, lt_asymm (Fin.castSucc_lt_last j)]
  · rw [Fin.prod_univ_castSucc]
    simp [Fin.castSucc_lt_last]

/-- `h(⟨a, b⟩) = h(⟨a⟩) h(⟨b⟩) (∏ aᵢ, ∏ bⱼ)_F`. -/
theorem diagonalHasseInvariant_append {m k : ℕ} (a : Fin m → Fˣ) (b : Fin k → Fˣ) :
    diagonalHasseInvariant (Fin.append a b) = diagonalHasseInvariant a *
      diagonalHasseInvariant b * hilbertSymbol F (∏ i, a i) (∏ j, b j) := by
  have h1 : ∀ (i : Fin k) (j : Fin m), ¬ Fin.natAdd m i < Fin.castAdd k j := by
    intro i j; simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]; omega
  have h2 : ∀ (i : Fin m) (j : Fin k), Fin.castAdd k i < Fin.natAdd m j := by
    intro i j; simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]; omega
  have h3 : ∀ (i j : Fin m), Fin.castAdd k i < Fin.castAdd k j ↔ i < j := by
    intro i j; simp only [Fin.lt_def, Fin.val_castAdd]
  simp only [diagonalHasseInvariant]
  rw [Fin.prod_univ_add]
  simp_rw [Fin.prod_univ_add (f := fun i => if i < _ then _ else _)]
  simp only [h1, h2, h3, Fin.natAdd_lt_natAdd_iff, Fin.append_left, Fin.append_right, ite_true,
    ite_false, Finset.prod_const_one, mul_one]
  rw [Finset.prod_mul_distrib, map_prod]
  simp_rw [hilbertSymbol_prod_left]
  ac_rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [NeZero (2 : F)] in
/-- `((s : ℤ) : ℂ)² = 1` for `s ∈ ℤˣ`. -/
theorem WeilIndex.Internal.units_int_cast_mul_self (s : ℤˣ) :
    ((s : ℤ) : ℂ) * ((s : ℤ) : ℂ) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

variable (ψ : UnitaryAdditiveCharacter F)

open WeilIndex.Internal in
/-- **GKT Proposition 3.29**, the step from `n` to `n + 1` by Proposition 3.19 (b):
`∏ γ(aᵢ, ψ) = γ(∏ aᵢ, ψ) ∏_{i<j} (aᵢ, aⱼ)_F`. -/
theorem prod_normalizedWeilIndex : ∀ {n : ℕ} (a : Fin n → Fˣ),
    ∏ i, normalizedWeilIndex (a i) ψ =
      normalizedWeilIndex (∏ i, a i) ψ * ((diagonalHasseInvariant a : ℤ) : ℂ)
  | 0, a => by simp [diagonalHasseInvariant, normalizedWeilIndex_one]
  | n + 1, a => by
    rw [Fin.prod_univ_castSucc, prod_normalizedWeilIndex (fun i => a (Fin.castSucc i)),
      Fin.prod_univ_castSucc (f := a), normalizedWeilIndex_mul, diagonalHasseInvariant_castSucc,
      ← hilbertSymbol_prod_left]
    have hs := units_int_cast_mul_self
      (hilbertSymbol F (∏ i : Fin n, a (Fin.castSucc i)) (a (Fin.last n)))
    push_cast
    linear_combination (-(normalizedWeilIndex (∏ i : Fin n, a (Fin.castSucc i)) ψ *
      normalizedWeilIndex (a (Fin.last n)) ψ *
        ((diagonalHasseInvariant fun i => a (Fin.castSucc i) : ℤ) : ℂ))) * hs

/-- **GKT Proposition 3.29** for a diagonal form:
`γ(ψ ∘ ⟨a₁, …, aₙ⟩) = γ(∏ aᵢ, ψ) γ(ψ)ⁿ ∏_{i<j} (aᵢ, aⱼ)_F`. -/
theorem weilIndex_weightedSumSquares {n : ℕ} (a : Fin n → Fˣ) :
    weilIndex (fun x : Fin n → F => ψ.complex (weightedSumSquares F a x)) =
      normalizedWeilIndex (∏ i, a i) ψ * weilIndexOne ψ ^ n *
        ((diagonalHasseInvariant a : ℤ) : ℂ) := by
  simp_rw [weightedSumSquares_units_apply]
  rw [weilIndex_diagonal]
  have h : ∀ i, weilIndexOne (ψ.scale (a i)) = normalizedWeilIndex (a i) ψ * weilIndexOne ψ :=
    fun i => by rw [normalizedWeilIndex, div_mul_cancel₀ _ (weilIndexOne_ne_zero ψ)]
  simp_rw [h]
  rw [Finset.prod_mul_distrib, prod_normalizedWeilIndex, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  ring

variable {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [TopologicalSpace V]
  [IsModuleTopology F V]

/-- **GKT Proposition 3.29** for a given diagonalization `q ≅ ⟨a₁, …, aₙ⟩`:
`γ(ψ ∘ q) = γ(∏ aᵢ, ψ) γ(ψ)ⁿ ∏_{i<j} (aᵢ, aⱼ)_F`. -/
theorem weilIndex_eq_of_isometryEquiv_weightedSumSquares (q : QuadraticForm F V) {n : ℕ}
    (a : Fin n → Fˣ) (e : q.IsometryEquiv (weightedSumSquares F a)) :
    weilIndex (fun x => ψ.complex (q x)) =
      normalizedWeilIndex (∏ i, a i) ψ * weilIndexOne ψ ^ n *
        ((diagonalHasseInvariant a : ℤ) : ℂ) := by
  rw [weilIndex_quadraticForm_isometryEquiv ψ e (separatingLeft_polarBilin_weightedSumSquares a),
    weilIndex_weightedSumSquares]

/-- **GKT Proposition 3.29**: `γ(ψ ∘ q) = γ(det(q), ψ) γ(ψ)ⁿ h(q)` for a non-degenerate quadratic
space of dimension `n`. -/
theorem weilIndex_eq_quadraticDet_hasseInvariant (q : QuadraticForm F V)
    (hq : (polarBilin q).SeparatingLeft) :
    weilIndex (fun x => ψ.complex (q x)) =
      normalizedWeilIndex (quadraticDet q) ψ * weilIndexOne ψ ^ Module.finrank F V *
        ((hasseInvariant q : ℤ) : ℂ) := by
  obtain ⟨e⟩ := equivalent_diagonalWeights q hq
  exact weilIndex_eq_of_isometryEquiv_weightedSumSquares ψ q _ e

/-- **GKT Proposition 3.30**: `γ(ψ_a ∘ q) = (det(q), a)_F γ(a, ψ)ⁿ γ(ψ ∘ q)`. -/
theorem weilIndex_scale_quadraticForm (q : QuadraticForm F V)
    (hq : (polarBilin q).SeparatingLeft) (a : Fˣ) :
    weilIndex (fun x => (ψ.scale a).complex (q x)) =
      ((hilbertSymbol F (quadraticDet q) a : ℤ) : ℂ) *
        normalizedWeilIndex a ψ ^ Module.finrank F V * weilIndex (fun x => ψ.complex (q x)) := by
  rw [weilIndex_eq_quadraticDet_hasseInvariant (ψ.scale a) q hq,
    weilIndex_eq_quadraticDet_hasseInvariant ψ q hq, normalizedWeilIndex_scale]
  have h : weilIndexOne (ψ.scale a) = normalizedWeilIndex a ψ * weilIndexOne ψ := by
    rw [normalizedWeilIndex, div_mul_cancel₀ _ (weilIndexOne_ne_zero ψ)]
  rw [h]
  ring

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [NeZero (2 : F)] [FiniteDimensional F V]
  [IsModuleTopology F V] in
/-- GKT Proposition 3.30, the "trivial" equality: `γ(ψ_a ∘ q) = γ(ψ ∘ a q)`. -/
theorem weilIndex_scale_eq_smul [IsTopologicalRing F] (q : QuadraticForm F V) (a : Fˣ) :
    weilIndex (fun x => (ψ.scale a).complex (q x)) =
      weilIndex (fun x => ψ.complex (((a : F) • q) x)) :=
  rfl

end LocalField

/-! ### Proposition B.29 -/

section HasseInvariant

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [NeZero (2 : F)] {V : Type} [AddCommGroup V] [Module F V]

attribute [local instance] WeilIndex.Internal.secondCountableTopology_self
  WeilIndex.Internal.locallyCompactSpace_self WeilIndex.Internal.compactOpenExhaustion_self

/-- **GKT Proposition B.29 (a)**: the Hasse invariant does not depend on the diagonalization: for
every `q ≅ ⟨a₁, …, aₙ⟩`, `∏_{i<j} (aᵢ, aⱼ)_F = h(q)`. Proof: Proposition 3.29 for both
diagonalizations of `⟨a₁, …, aₙ⟩`, Corollary 3.14 and Proposition 3.19 (a). -/
theorem diagonalHasseInvariant_eq_hasseInvariant (q : QuadraticForm F V) {n : ℕ} {a : Fin n → Fˣ}
    (e : q.IsometryEquiv (weightedSumSquares F a)) :
    diagonalHasseInvariant a = hasseInvariant q := by
  obtain ⟨ψ⟩ := nonempty_unitaryAdditiveCharacter F
  have hn := finrank_eq_of_isometryEquiv q e
  subst hn
  obtain ⟨e₀⟩ := equivalent_diagonalWeights_of_isometryEquiv q e
  obtain ⟨u, hu⟩ := exists_prod_eq_prod_mul_sq (e₀.symm.trans e)
  have h1 := weilIndex_eq_of_isometryEquiv_weightedSumSquares ψ
    (weightedSumSquares F (diagonalWeights q)) a (e₀.symm.trans e)
  rw [weilIndex_weightedSumSquares, hu, normalizedWeilIndex_mul_sq] at h1
  have hne : normalizedWeilIndex (∏ i, a i) ψ * weilIndexOne ψ ^ Module.finrank F V ≠ 0 := by
    refine mul_ne_zero (fun h => ?_) (pow_ne_zero _ (weilIndexOne_ne_zero ψ))
    have := norm_normalizedWeilIndex ψ (∏ i, a i)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have h2 := mul_left_cancel₀ hne h1
  exact (Units.ext (Int.cast_injective h2)).symm

/-- Isometric non-degenerate quadratic spaces have the same Hasse invariant. -/
theorem hasseInvariant_eq_of_isometryEquiv {V' : Type} [AddCommGroup V'] [Module F V']
    [FiniteDimensional F V'] {q : QuadraticForm F V} {q' : QuadraticForm F V'}
    (e : q.IsometryEquiv q') (hq' : (polarBilin q').SeparatingLeft) :
    hasseInvariant q = hasseInvariant q' := by
  obtain ⟨e'⟩ := equivalent_diagonalWeights q' hq'
  exact (diagonalHasseInvariant_eq_hasseInvariant q (e.trans e')).symm

/-- **GKT Proposition B.29 (b)**: the hyperbolic plane `ℍ ≅ ⟨c, -c⟩` has Hasse invariant `1`. -/
theorem hasseInvariant_eq_one_of_isometryEquiv (q : QuadraticForm F V) (c : Fˣ)
    (e : q.IsometryEquiv (weightedSumSquares F ![c, -c])) : hasseInvariant q = 1 := by
  rw [← diagonalHasseInvariant_eq_hasseInvariant q e]
  simp [diagonalHasseInvariant, Fin.prod_univ_two, hilbertSymbol_neg_self]

open WeilIndex.Internal in
/-- **GKT Proposition B.29 (c)**: `h(V₁ ⊕ V₂) = h(V₁) h(V₂) (det V₁, det V₂)_F`. -/
theorem hasseInvariant_prod [FiniteDimensional F V] {V' : Type} [AddCommGroup V'] [Module F V']
    [FiniteDimensional F V'] (q : QuadraticForm F V) (q' : QuadraticForm F V')
    (hq : (polarBilin q).SeparatingLeft) (hq' : (polarBilin q').SeparatingLeft) :
    hasseInvariant (q.prod q') =
      hasseInvariant q * hasseInvariant q' *
        hilbertSymbol F (quadraticDet q) (quadraticDet q') := by
  obtain ⟨e⟩ := equivalent_diagonalWeights q hq
  obtain ⟨e'⟩ := equivalent_diagonalWeights q' hq'
  rw [← diagonalHasseInvariant_eq_hasseInvariant (q.prod q')
    ((e.prod e').trans (appendIsometryEquiv _ _)), diagonalHasseInvariant_append]
  rfl

end HasseInvariant

end Langlands.Theta
