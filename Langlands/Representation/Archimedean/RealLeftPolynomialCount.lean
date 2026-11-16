import Langlands.Representation.Archimedean.RealSmoothRightAction
import Langlands.Representation.Archimedean.RealLowerUnipotentRestriction
import Langlands.Representation.Archimedean.Kostant.OrderedMonomials

/-!
# Counting `U(𝔤)` modulo a Borel-shifted right ideal and along `Ad(N̄)`

Let `𝔤 = ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)` with basis `x_c = 1 ⊗ E_c`, `c = (i, j)`. For scalars `μ_c`, a position
`c₀` strictly below the diagonal and `k : ℕ`, `J μ c₀ k` is the span of the elements
`(x_c - μ_c) z` (`c` on or above the diagonal) and `x_{c₀}^k z` (`z ∈ U(𝔤)`): a right ideal.

* `finrank_map_mkQ_le`: the image of `U_d` in `U(𝔤) / J` has dimension at most
  `k (d + 1)^(N - 1)`, with `N` the number of positions below the diagonal.
* `finrank_map_adU_le`: the functions `v ↦ [Ad(n̄(v)) u]`, `u ∈ U_d`, span a space of dimension
  at most `((n + 1) d + 1)^N k (d + 1)^(N - 1)`.
-/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Algebra.UniversalEnveloping Langlands.LocalFactor.Archimedean

namespace LeftPolynomialCount

open Kostant

variable {n : ℕ}

/-! ## The basis and the order of the letters -/

variable (n) in
/-- The basis `1 ⊗ E_{ij}` of `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`. -/
def stdBasis : Module.Basis (Fin n × Fin n) ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) :=
  Algebra.TensorProduct.basis ℂ (Matrix.stdBasis ℝ (Fin n) (Fin n))

theorem stdBasis_apply (c : Fin n × Fin n) :
    stdBasis n c = (1 : ℂ) ⊗ₜ[ℝ] Matrix.single c.1 c.2 (1 : ℝ) := by
  obtain ⟨i, j⟩ := c
  rw [stdBasis, Algebra.TensorProduct.basis_apply, Matrix.stdBasis_eq_single]

/-- The generator `x_c = ι(1 ⊗ E_c)` of `U(𝔤)`. -/
abbrev gen (c : Fin n × Fin n) : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) :=
  UniversalEnvelopingAlgebra.ι ℂ (stdBasis n c)

variable (n) in
/-- The positions on or above the diagonal. -/
def upList : List (Fin n × Fin n) :=
  (Finset.univ.filter fun c : Fin n × Fin n => c.1 ≤ c.2).toList

/-- The positions strictly below the diagonal other than `c₀`. -/
def lowList (c₀ : Fin n × Fin n) : List (Fin n × Fin n) :=
  (Finset.univ.filter fun c : Fin n × Fin n => c.2 < c.1 ∧ c ≠ c₀).toList

/-- The order of the letters: upper ones, then `c₀`, then the other lower ones. -/
def orderList (c₀ : Fin n × Fin n) : List (Fin n × Fin n) := upList n ++ c₀ :: lowList c₀

theorem mem_upList {c : Fin n × Fin n} : c ∈ upList n ↔ c.1 ≤ c.2 := by
  simp [upList]

theorem mem_lowList {c₀ c : Fin n × Fin n} : c ∈ lowList c₀ ↔ c.2 < c.1 ∧ c ≠ c₀ := by
  simp [lowList]

theorem orderList_nodup {c₀ : Fin n × Fin n} (hc₀ : c₀.2 < c₀.1) : (orderList c₀).Nodup := by
  unfold orderList
  rw [List.nodup_append]
  refine ⟨Finset.nodup_toList _, List.nodup_cons.2 ⟨fun h => (mem_lowList.1 h).2 rfl,
    Finset.nodup_toList _⟩, fun a ha b hb hab => ?_⟩
  subst hab
  have h1 := mem_upList.1 ha
  rcases List.mem_cons.1 hb with rfl | hb
  · exact absurd hc₀ (not_lt.2 h1)
  · exact absurd (mem_lowList.1 hb).1 (not_lt.2 h1)

theorem mem_orderList (c₀ c : Fin n × Fin n) :
    c ∈ orderList c₀ := by
  unfold orderList
  rw [List.mem_append, List.mem_cons, mem_upList, mem_lowList]
  by_cases h : c.1 ≤ c.2
  · exact Or.inl h
  · by_cases h' : c = c₀
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr ⟨not_le.1 h, h'⟩)

/-! ## The right ideal `J` -/

variable (μ : Fin n × Fin n → ℂ) (c₀ : Fin n × Fin n) (k : ℕ)

/-- The span of `(x_c - μ_c) z` for `c` on or above the diagonal and of `x_{c₀}^k z`. -/
def J : Submodule ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)) :=
  Submodule.span ℂ
    ({y | ∃ c : Fin n × Fin n, c.1 ≤ c.2 ∧ ∃ z, y = (gen c - algebraMap ℂ _ (μ c)) * z} ∪
      {y | ∃ z, y = gen c₀ ^ k * z})

theorem sub_mem_J {c : Fin n × Fin n} (hc : c.1 ≤ c.2)
    (z : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)) :
    gen c * z - μ c • z ∈ J μ c₀ k := by
  have h : gen c * z - μ c • z = (gen c - algebraMap ℂ _ (μ c)) * z := by
    rw [sub_mul, Algebra.smul_def]
  rw [h]
  exact Submodule.subset_span (Or.inl ⟨c, hc, z, rfl⟩)

theorem pow_mul_mem_J (z : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)) :
    gen c₀ ^ k * z ∈ J μ c₀ k :=
  Submodule.subset_span (Or.inr ⟨z, rfl⟩)

/-- Upper letters in front act by their scalars modulo `J`. -/
theorem word_mul_sub_mem_J (l : List (Fin n × Fin n)) (hl : ∀ c ∈ l, c.1 ≤ c.2)
    (z : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)) :
    word ℂ _ (l.map (stdBasis n)) * z - (l.map μ).prod • z ∈ J μ c₀ k := by
  induction l with
  | nil => simp
  | cons c l ih =>
    have hc := hl c List.mem_cons_self
    have ih' := ih fun c' hc' => hl c' (List.mem_cons_of_mem c hc')
    have h : word ℂ _ ((c :: l).map (stdBasis n)) * z - ((c :: l).map μ).prod • z =
        (gen c * (word ℂ _ (l.map (stdBasis n)) * z) -
          μ c • (word ℂ _ (l.map (stdBasis n)) * z)) +
        μ c • (word ℂ _ (l.map (stdBasis n)) * z - (l.map μ).prod • z) := by
      rw [List.map_cons, word_cons, List.map_cons, List.prod_cons, mul_assoc, smul_sub,
        smul_smul]
      abel
    rw [h]
    exact Submodule.add_mem _ (sub_mem_J μ c₀ k hc _) (Submodule.smul_mem _ _ ih')

theorem word_append (l₁ l₂ : List (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)) :
    word ℂ _ (l₁ ++ l₂) = word ℂ _ l₁ * word ℂ _ l₂ := by
  simp only [word, List.map_append, List.prod_append]

theorem word_replicate (m : ℕ) (x : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) :
    word ℂ _ (List.replicate m x) = UniversalEnvelopingAlgebra.ι ℂ x ^ m := by
  simp only [word, List.map_replicate, List.prod_replicate]

/-- A word in the letters `expand l α` is the ordered product of the powers `x_c^(α c)`. -/
theorem word_expand (l : List (Fin n × Fin n)) (α : (Fin n × Fin n) →₀ ℕ) :
    word ℂ _ ((expand l α).map (stdBasis n)) = (l.map fun c => gen c ^ α c).prod := by
  induction l with
  | nil => simp [expand]
  | cons c l ih =>
    have he : expand (c :: l) α = List.replicate (α c) c ++ expand l α := by
      simp [expand]
    rw [he, List.map_append, word_append, ih, List.map_replicate, word_replicate,
      List.map_cons, List.prod_cons]

/-- The ordered monomial for the order `orderList c₀`. -/
theorem orderedMonomial_eq (α : (Fin n × Fin n) →₀ ℕ) :
    orderedMonomial ℂ _ (stdBasis n) (orderList c₀) α =
      word ℂ _ ((expand (upList n) α).map (stdBasis n)) *
        (gen c₀ ^ α c₀ * ((lowList c₀).map fun c => gen c ^ α c).prod) := by
  have he : expand (orderList c₀) α =
      expand (upList n) α ++ (List.replicate (α c₀) c₀ ++ expand (lowList c₀) α) := by
    simp [expand, orderList]
  rw [orderedMonomial, he, List.map_append, word_append, List.map_append, word_append,
    List.map_replicate, word_replicate, word_expand, word_expand]

/-- The spanning family of `U_d` modulo `J`: `[x_{c₀}^j ∏ x_c^(γ c)]` with `j < k`, `c` running
through `lowList c₀` and `γ c ≤ d`. -/
def spanFamily (d : ℕ) :
    Fin k × (Fin (lowList c₀).length → Fin (d + 1)) →
      UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) ⧸ J μ c₀ k :=
  fun p => (J μ c₀ k).mkQ (gen c₀ ^ (p.1 : ℕ) *
    (List.ofFn fun i => gen ((lowList c₀).get i) ^ (p.2 i : ℕ)).prod)

theorem mkQ_orderedMonomial_mem {d : ℕ} (α : (Fin n × Fin n) →₀ ℕ) (hα : α.degree ≤ d) :
    (J μ c₀ k).mkQ (orderedMonomial ℂ _ (stdBasis n) (orderList c₀) α) ∈
      Submodule.span ℂ (Set.range (spanFamily μ c₀ k d)) := by
  set y := gen c₀ ^ α c₀ * ((lowList c₀).map fun c => gen c ^ α c).prod with hy
  have hup : ∀ c ∈ expand (upList n) α, c.1 ≤ c.2 := by
    intro c hc
    simp only [expand, List.mem_flatMap, List.mem_replicate] at hc
    obtain ⟨c', hc', _, rfl⟩ := hc
    exact mem_upList.1 hc'
  have h1 := word_mul_sub_mem_J μ c₀ k _ hup y
  have h2 : (J μ c₀ k).mkQ (orderedMonomial ℂ _ (stdBasis n) (orderList c₀) α) =
      ((expand (upList n) α).map μ).prod • (J μ c₀ k).mkQ y := by
    rw [orderedMonomial_eq, ← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact h1
  rw [h2]
  refine Submodule.smul_mem _ _ ?_
  by_cases hk : k ≤ α c₀
  · have : y ∈ J μ c₀ k := by
      rw [hy, ← Nat.add_sub_cancel' hk, pow_add, mul_assoc]
      exact pow_mul_mem_J μ c₀ k _
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 this]
    exact Submodule.zero_mem _
  · have hle : ∀ c, α c < d + 1 := fun c => Nat.lt_succ_of_le ((Finsupp.le_degree c α).trans hα)
    refine Submodule.subset_span ⟨(⟨α c₀, not_le.1 hk⟩, fun i => ⟨α ((lowList c₀).get i),
      hle _⟩), ?_⟩
    simp only [spanFamily, hy]
    congr 3
    conv_rhs => rw [← List.ofFn_get (lowList c₀), List.map_ofFn]
    rfl

/-- **The count modulo `J`.** The image of `U_d` in `U(𝔤) / J` lies in the span of
`spanFamily`, which has `k (d + 1)^|lowList c₀|` elements. -/
theorem map_mkQ_le_span {c₀ : Fin n × Fin n} (hc₀ : c₀.2 < c₀.1) (d : ℕ) :
    (degreeFiltration ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) d).map (J μ c₀ k).mkQ ≤
      Submodule.span ℂ (Set.range (spanFamily μ c₀ k d)) := by
  refine (Submodule.map_mono (degreeFiltration_le_orderedSpan ℂ _ (stdBasis n)
    (orderList_nodup hc₀) (mem_orderList c₀) d)).trans ?_
  rw [orderedSpan, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨α, hα, rfl⟩, rfl⟩
  exact mkQ_orderedMonomial_mem μ c₀ k α hα

/-! ## Polynomial functions of the coordinates of `N̄` -/

open RealLowerUnipotent SmoothRightAction

/-- The monomial `v ↦ ∏_c v_c^(β c)`. -/
def mono (β : LowIdx n → ℕ) : (LowIdx n → ℝ) → ℝ := fun v => ∏ c, v c ^ β c

variable (n) in
/-- The real polynomial functions of degree at most `D` in the coordinates `v`. -/
def polyR (D : ℕ) : Submodule ℝ ((LowIdx n → ℝ) → ℝ) :=
  Submodule.span ℝ {φ | ∃ β : LowIdx n → ℕ, ∑ c, β c ≤ D ∧ φ = mono β}

theorem mono_mem_polyR {D : ℕ} {β : LowIdx n → ℕ} (hβ : ∑ c, β c ≤ D) : mono β ∈ polyR n D :=
  Submodule.subset_span ⟨β, hβ, rfl⟩

theorem const_mem_polyR (r : ℝ) (D : ℕ) : (fun _ => r : (LowIdx n → ℝ) → ℝ) ∈ polyR n D := by
  have h : (fun _ => r : (LowIdx n → ℝ) → ℝ) = r • mono 0 := by
    funext v
    simp [mono]
  rw [h]
  exact Submodule.smul_mem _ _ (mono_mem_polyR (by simp))

theorem coord_mem_polyR (c : LowIdx n) : (fun v : LowIdx n → ℝ => v c) ∈ polyR n 1 := by
  have h : (fun v : LowIdx n → ℝ => v c) = mono (Pi.single c 1) := by
    funext v
    simp only [mono]
    rw [Fintype.prod_eq_single c (fun c' hc' => by rw [Pi.single_eq_of_ne hc', pow_zero])]
    simp
  rw [h]
  exact mono_mem_polyR (by simp)

theorem mono_mul (β β' : LowIdx n → ℕ) : mono β * mono β' = mono (β + β') := by
  funext v
  simp only [mono, Pi.mul_apply, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

theorem mul_mem_polyR {D D' : ℕ} {φ ψ : (LowIdx n → ℝ) → ℝ} (hφ : φ ∈ polyR n D)
    (hψ : ψ ∈ polyR n D') : φ * ψ ∈ polyR n (D + D') := by
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨β, hβ, rfl⟩ := hφ
    induction hψ using Submodule.span_induction with
    | mem ψ hψ =>
      obtain ⟨β', hβ', rfl⟩ := hψ
      rw [mono_mul]
      exact mono_mem_polyR (by simp only [Pi.add_apply, Finset.sum_add_distrib]; omega)
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ r ha
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r ha

theorem prod_mem_polyR {ι : Type*} (s : Finset ι) (f : ι → (LowIdx n → ℝ) → ℝ)
    (hf : ∀ i ∈ s, f i ∈ polyR n 1) : (fun v => ∏ i ∈ s, f i v) ∈ polyR n s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const_mem_polyR (n := n) 1 0
  | @insert a s ha ih =>
    have h : (fun v => ∏ i ∈ insert a s, f i v) = f a * fun v => ∏ i ∈ s, f i v := by
      funext v
      rw [Finset.prod_insert ha]
      rfl
    rw [h, Finset.card_insert_of_notMem ha, add_comm]
    exact mul_mem_polyR (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem det_mem_polyR (M : (LowIdx n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, (fun v => M v i j) ∈ polyR n 1) : (fun v => (M v).det) ∈ polyR n n := by
  have h : (fun v => (M v).det) = ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) • (fun v => ∏ i, M v (σ i) i) := by
    funext v
    rw [Matrix.det_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Pi.smul_apply, Units.smul_def, zsmul_eq_mul, smul_eq_mul]
  rw [h]
  refine Submodule.sum_mem _ fun σ _ => Submodule.smul_mem _ _ ?_
  have := prod_mem_polyR (n := n) Finset.univ (fun i v => M v (σ i) i) fun i _ => hM (σ i) i
  rwa [Finset.card_univ, Fintype.card_fin] at this

theorem nbarMat_mem_polyR (i j : Fin n) : (fun v => nbarMat v i j) ∈ polyR n 1 := by
  by_cases h : j < i
  · have : (fun v => nbarMat v i j) = fun v => v ⟨(i, j), h⟩ := by
      funext v
      simp [nbarMat, h]
    rw [this]
    exact coord_mem_polyR _
  · have : (fun v => nbarMat v i j) = fun _ => if i = j then (1 : ℝ) else 0 := by
      funext v
      simp [nbarMat, h]
    rw [this]
    exact const_mem_polyR _ _

theorem adjugate_nbarMat_mem_polyR (i j : Fin n) :
    (fun v => (nbarMat v).adjugate i j) ∈ polyR n n := by
  have h : (fun v => (nbarMat v).adjugate i j) =
      fun v => ((nbarMat v).updateRow j (Pi.single i 1)).det := by
    funext v
    rw [Matrix.adjugate_apply]
  rw [h]
  refine det_mem_polyR _ fun a b => ?_
  by_cases hab : a = j
  · subst hab
    have : (fun v => ((nbarMat v).updateRow a (Pi.single i 1)) a b) =
        fun _ => (Pi.single i (1 : ℝ) : Fin n → ℝ) b := by
      funext v
      simp
    rw [this]
    exact const_mem_polyR _ _
  · have : (fun v => ((nbarMat v).updateRow j (Pi.single i 1)) a b) =
        fun v => nbarMat v a b := by
      funext v
      rw [Matrix.updateRow_ne hab]
    rw [this]
    exact nbarMat_mem_polyR a b

theorem conj_mem_polyR (X : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (fun v => (nbarMat v * X * (nbarMat v).adjugate) i j) ∈ polyR n (1 + n) := by
  have h : (fun v => (nbarMat v * X * (nbarMat v).adjugate) i j) =
      ∑ l, (fun v => (nbarMat v * X) i l) * fun v => (nbarMat v).adjugate l j := by
    funext v
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply]
  rw [h]
  refine Submodule.sum_mem _ fun l _ => mul_mem_polyR ?_ (adjugate_nbarMat_mem_polyR l j)
  have h2 : (fun v => (nbarMat v * X) i l) = ∑ m, X m l • fun v => nbarMat v i m := by
    funext v
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [h2]
  exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (nbarMat_mem_polyR i m)

/-! ## Polynomial functions with values in `U(𝔤)` -/

variable (n) in
/-- The functions `v ↦ ∑ m_β(v) w_β` with `|β| ≤ D` and `w_β ∈ U_d`. -/
def polyU (D d : ℕ) : Submodule ℂ ((LowIdx n → ℝ) →
    UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)) :=
  Submodule.span ℂ {F | ∃ β : LowIdx n → ℕ, ∑ c, β c ≤ D ∧
    ∃ w ∈ degreeFiltration ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) d,
      F = fun v => ((mono β v : ℝ) : ℂ) • w}

theorem polyU_mono {D D' d d' : ℕ} (hD : D ≤ D') (hd : d ≤ d') : polyU n D d ≤ polyU n D' d' :=
  Submodule.span_mono fun _ ⟨β, hβ, w, hw, he⟩ =>
    ⟨β, hβ.trans hD, w, degreeFiltration_mono ℂ _ hd hw, he⟩

theorem smul_mem_polyU {D d : ℕ} {φ : (LowIdx n → ℝ) → ℝ} (hφ : φ ∈ polyR n D)
    {w : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)}
    (hw : w ∈ degreeFiltration ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) d) :
    (fun v => ((φ v : ℝ) : ℂ) • w) ∈ polyU n D d := by
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨β, hβ, rfl⟩ := hφ
    exact Submodule.subset_span ⟨β, hβ, w, hw, rfl⟩
  | zero =>
    convert Submodule.zero_mem (polyU n D d) using 1
    funext v
    simp
  | add a b _ _ ha hb =>
    convert Submodule.add_mem _ ha hb using 1
    funext v
    simp [add_smul]
  | smul r a _ ha =>
    convert Submodule.smul_mem _ (r : ℂ) ha using 1
    funext v
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, smul_smul]

theorem mul_mem_polyU {D D' d d' : ℕ}
    {F F' : (LowIdx n → ℝ) → UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)}
    (hF : F ∈ polyU n D d) (hF' : F' ∈ polyU n D' d') :
    (fun v => F v * F' v) ∈ polyU n (D + D') (d + d') := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨β, hβ, w, hw, rfl⟩ := hF
    induction hF' using Submodule.span_induction with
    | mem F' hF' =>
      obtain ⟨β', hβ', w', hw', rfl⟩ := hF'
      have hsum : ∑ c, (β + β') c ≤ D + D' := by
        simp only [Pi.add_apply, Finset.sum_add_distrib]
        omega
      refine Submodule.subset_span ⟨β + β', hsum, w * w', mul_mem_degreeFiltration ℂ _ hw hw', ?_⟩
      funext v
      rw [smul_mul_smul_comm, ← Complex.ofReal_mul, ← mono_mul]
      rfl
    | zero =>
      convert Submodule.zero_mem (polyU n (D + D') (d + d')) using 1
      funext v
      simp
    | add a b _ _ ha hb =>
      convert Submodule.add_mem _ ha hb using 1
      funext v
      simp [mul_add]
    | smul r a _ ha =>
      convert Submodule.smul_mem _ r ha using 1
      funext v
      simp
  | zero =>
    convert Submodule.zero_mem (polyU n (D + D') (d + d')) using 1
    funext v
    simp
  | add a b _ _ ha hb =>
    convert Submodule.add_mem _ ha hb using 1
    funext v
    simp [add_mul]
  | smul r a _ ha =>
    convert Submodule.smul_mem _ r ha using 1
    funext v
    simp

theorem adU_ι_mem_polyU (x : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) :
    (fun v => adU (nbar v) (UniversalEnvelopingAlgebra.ι ℂ x)) ∈ polyU n (1 + n) 1 := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    convert Submodule.add_mem _ hx hy using 1
    funext v
    simp [map_add]
  | tmul z X =>
    have hgen : ∀ i j : Fin n, UniversalEnvelopingAlgebra.ι ℂ
        (z ⊗ₜ[ℝ] (Matrix.single i j (1 : ℝ) : Matrix (Fin n) (Fin n) ℝ) :
          ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) ∈
        degreeFiltration ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) 1 := by
      intro i j
      rw [degreeFiltration_one]
      exact generator_mem_degreeOne ℂ _ _
    have h : (fun v => adU (nbar v) (UniversalEnvelopingAlgebra.ι ℂ (z ⊗ₜ X))) =
        ∑ i, ∑ j, fun v => (((nbarMat v * X * (nbarMat v).adjugate) i j : ℝ) : ℂ) •
          UniversalEnvelopingAlgebra.ι ℂ
            (z ⊗ₜ[ℝ] (Matrix.single i j (1 : ℝ) : Matrix (Fin n) (Fin n) ℝ) :
              ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) := by
      funext v
      rw [adU_ι, adLie_apply, adAlg_tmul, conjAlgHom_apply, nbar_val, nbar_inv_val]
      conv_lhs => rw [Matrix.matrix_eq_sum_single (nbarMat v * X * (nbarMat v).adjugate)]
      simp only [TensorProduct.tmul_sum, map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [show Matrix.single i j ((nbarMat v * X * (nbarMat v).adjugate) i j) =
          ((nbarMat v * X * (nbarMat v).adjugate) i j) • Matrix.single i j (1 : ℝ) by
        rw [Matrix.smul_single, smul_eq_mul, mul_one], TensorProduct.tmul_smul,
        ← algebraMap_smul ℂ, map_smul]
      rfl
    rw [h]
    exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
      smul_mem_polyU (conj_mem_polyR X i j) (hgen i j)

theorem algebraMap_mem_polyU (r : ℂ) (D d : ℕ) :
    (fun _ => algebraMap ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)) r :
      (LowIdx n → ℝ) → _) ∈ polyU n D d := by
  refine Submodule.subset_span ⟨0, by simp, algebraMap ℂ _ r,
    algebraMap_mem_degreeFiltration ℂ _ r d, ?_⟩
  funext v
  simp [mono]

/-- `v ↦ Ad(n̄(v)) u` is polynomial of degree at most `(1 + n) d` for `u ∈ U_d`. -/
theorem adU_mem_polyU (d : ℕ)
    {u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)}
    (hu : u ∈ degreeFiltration ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) d) :
    (fun v => adU (nbar v) u) ∈ polyU n ((1 + n) * d) d := by
  induction d generalizing u with
  | zero =>
    rw [degreeFiltration_zero, Submodule.mem_one] at hu
    obtain ⟨r, rfl⟩ := hu
    convert algebraMap_mem_polyU (n := n) r _ _ using 1
    funext v
    rw [AlgHom.commutes]
  | succ d ih =>
    have hone : ∀ b ∈ degreeOne ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ),
        (fun v => adU (nbar v) b) ∈ polyU n (1 + n) 1 := by
      intro b hb
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hb
      obtain ⟨r, rfl⟩ := Submodule.mem_one.1 hy
      obtain ⟨x, rfl⟩ := hz
      convert Submodule.add_mem _ (algebraMap_mem_polyU (n := n) r (1 + n) 1)
        (adU_ι_mem_polyU x) using 1
      funext v
      rw [map_add, AlgHom.commutes]
      rfl
    have hu' : u ∈ degreeFiltration ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) d *
        degreeOne ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) := by
      rw [degreeFiltration, ← pow_succ]
      exact hu
    clear hu
    induction hu' using Submodule.mul_induction_on' with
    | mem_mul_mem a ha b hb =>
      have h := mul_mem_polyU (ih ha) (hone b hb)
      rw [show (1 + n) * d + (1 + n) = (1 + n) * (d + 1) by ring] at h
      convert h using 1
      funext v
      rw [map_mul]
    | add x _ y _ hx hy =>
      convert Submodule.add_mem _ hx hy using 1
      funext v
      rw [map_add]
      rfl

/-! ## The combined count -/

variable {c₀}

/-- `u ↦ (v ↦ [Ad(n̄(v)) u])`. -/
def adMap (μ : Fin n × Fin n → ℂ) (c₀ : Fin n × Fin n) (k : ℕ) :
    UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ[ℂ]
      ((LowIdx n → ℝ) → UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) ⧸
        J μ c₀ k) :=
  LinearMap.pi fun v => (J μ c₀ k).mkQ ∘ₗ (adU (nbar v)).toLinearMap

theorem adMap_apply (u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ))
    (v : LowIdx n → ℝ) : adMap μ c₀ k u v = (J μ c₀ k).mkQ (adU (nbar v) u) :=
  rfl

/-- The family `v ↦ m_β(v) [x_{c₀}^j ∏ x_c^(γ c)]`. -/
def fullFamily (D d : ℕ) :
    (LowIdx n → Fin (D + 1)) × (Fin k × (Fin (lowList c₀).length → Fin (d + 1))) →
      ((LowIdx n → ℝ) → UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) ⧸
        J μ c₀ k) :=
  fun p v => ((mono (fun c => (p.1 c : ℕ)) v : ℝ) : ℂ) • spanFamily μ c₀ k d p.2

theorem mkQ_polyU_mem (hc₀ : c₀.2 < c₀.1) {D d : ℕ}
    {F : (LowIdx n → ℝ) → UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)}
    (hF : F ∈ polyU n D d) :
    (fun v => (J μ c₀ k).mkQ (F v)) ∈ Submodule.span ℂ (Set.range (fullFamily μ k D d)) := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨β, hβ, w, hw, rfl⟩ := hF
    have hw' := map_mkQ_le_span μ k hc₀ d (Submodule.mem_map_of_mem hw)
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hw'
    have hβle : ∀ c, β c < D + 1 := fun c => Nat.lt_succ_of_le
      ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)).trans hβ)
    have h : (fun v => (J μ c₀ k).mkQ (((mono β v : ℝ) : ℂ) • w)) =
        ∑ p, a p • fullFamily μ k D d (fun c => ⟨β c, hβle c⟩, p) := by
      funext v
      rw [map_smul, ← ha, Finset.sum_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [fullFamily, Pi.smul_apply, smul_smul, mul_comm]
    rw [h]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  | zero =>
    convert Submodule.zero_mem _ using 1
    funext v
    simp
  | add a b _ _ ha hb =>
    convert Submodule.add_mem _ ha hb using 1
    funext v
    simp
  | smul r a _ ha =>
    convert Submodule.smul_mem _ r ha using 1
    funext v
    simp

/-- **The count along `Ad(N̄)`.** The functions `v ↦ [Ad(n̄(v)) u]`, `u ∈ U_d`, span a space
of dimension at most `((1 + n) d + 1)^N · k (d + 1)^|lowList c₀|`, `N` the number of positions
below the diagonal. -/
theorem finrank_map_adMap_le (hc₀ : c₀.2 < c₀.1) (d : ℕ) :
    Module.finrank ℂ ((degreeFiltration ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) d).map
      (adMap μ c₀ k)) ≤
      ((1 + n) * d + 1) ^ Fintype.card (LowIdx n) * (k * (d + 1) ^ (lowList c₀).length) := by
  have hle : (degreeFiltration ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) d).map (adMap μ c₀ k) ≤
      Submodule.span ℂ (Set.range (fullFamily (c₀ := c₀) μ k ((1 + n) * d) d)) := by
    rintro _ ⟨u, hu, rfl⟩
    exact mkQ_polyU_mem μ k hc₀ (adU_mem_polyU d hu)
  have : Module.Finite ℂ (Submodule.span ℂ
      (Set.range (fullFamily (c₀ := c₀) μ k ((1 + n) * d) d))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  refine (Submodule.finrank_mono hle).trans ((finrank_range_le_card _).trans ?_)
  simp [Fintype.card_prod, Fintype.card_fin]

/-! ## Cardinalities -/

/-- The positions below the diagonal, sorted by row. -/
def lowIdxEquiv : LowIdx n ≃ Σ i : Fin n, Fin i where
  toFun c := ⟨c.1.1, ⟨c.1.2, c.2⟩⟩
  invFun p := ⟨(p.1, ⟨p.2, p.2.2.trans p.1.2⟩), p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- There are `n (n - 1) / 2` positions below the diagonal. -/
theorem card_lowIdx_mul_two : Fintype.card (LowIdx n) * 2 = n * (n - 1) := by
  rw [Fintype.card_congr lowIdxEquiv, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id_mul_two]

theorem length_lowList_add_one {c₀ : Fin n × Fin n} (hc₀ : c₀.2 < c₀.1) :
    (lowList c₀).length + 1 = Fintype.card (LowIdx n) := by
  rw [lowList, Finset.length_toList, Fintype.card_subtype]
  have h : (Finset.univ.filter fun c : Fin n × Fin n => c.2 < c.1 ∧ c ≠ c₀) =
      (Finset.univ.filter fun c : Fin n × Fin n => c.2 < c.1).erase c₀ := by
    ext c
    simp [and_comm]
  rw [h, Finset.card_erase_of_mem (by simpa using hc₀)]
  have : 0 < (Finset.univ.filter fun c : Fin n × Fin n => c.2 < c.1).card :=
    Finset.card_pos.2 ⟨c₀, by simpa using hc₀⟩
  omega

end LeftPolynomialCount

end Langlands.Archimedean
