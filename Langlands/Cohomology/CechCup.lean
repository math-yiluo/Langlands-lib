import Langlands.Cohomology.CechCochains
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Products of ordered Čech cochains of a presheaf of rings

For a presheaf `R` of commutative rings on a topological space and a family `U` of opens, the
ordered Čech cochains of the underlying abelian presheaf carry the Alexander–Whitney products.
This file records the two products needed for products of degree-one classes: the product
`cup₀ h b` of a `0`-cochain with a `q`-cochain and the product `cup₁ z b` of a `1`-cochain with
a `q`-cochain, their Leibniz rules, and the product `prod n z` of `n` one-cochains,
`(prod n z) τ = ∏ₖ z k (τ k, τ (k + 1))`. The product of cocycles is a cocycle, and it changes by
a coboundary when the factors change by coboundaries.
-/

universe w v u

open CategoryTheory Opposite TopologicalSpace

namespace Langlands.Cohomology.Cech

section Face

variable {T : TopCat.{u}} {P : TopCat.Presheaf AddCommGrpCat.{v} T} {ι : Type w}
  {U : ι → Opens T}

/-- The value of a family of sections on the face `τ ∘ θ` of `τ`, restricted to `inter U τ`. -/
def face {m n : ℕ} (x : ∀ σ : Fin m → ι, P.obj (op (inter U σ))) (τ : Fin n → ι)
    (θ : Fin m → Fin n) : P.obj (op (inter U τ)) :=
  res (inter_le_comp τ θ) (x (τ ∘ θ))

lemma res_face {m n l : ℕ} (x : ∀ σ : Fin m → ι, P.obj (op (inter U σ))) (τ : Fin n → ι)
    (θ₁ : Fin l → Fin n) (θ₂ : Fin m → Fin l) :
    res (inter_le_comp τ θ₁) (face x (τ ∘ θ₁) θ₂) = face x τ (θ₁ ∘ θ₂) := by
  rw [face, res_res]
  rfl

lemma face_congr {m n : ℕ} (x : ∀ σ : Fin m → ι, P.obj (op (inter U σ))) (τ : Fin n → ι)
    {θ θ' : Fin m → Fin n} (h : θ = θ') : face x τ θ = face x τ θ' := by
  subst h
  rfl

lemma face_id {n : ℕ} (x : ∀ σ : Fin n → ι, P.obj (op (inter U σ))) (τ : Fin n → ι) :
    face x τ id = x τ :=
  res_self _ _

lemma face_add {m n : ℕ} (x y : ∀ σ : Fin m → ι, P.obj (op (inter U σ))) (τ : Fin n → ι)
    (θ : Fin m → Fin n) : face (x + y) τ θ = face x τ θ + face y τ θ :=
  map_add _ _ _

lemma face_sub {m n : ℕ} (x y : ∀ σ : Fin m → ι, P.obj (op (inter U σ))) (τ : Fin n → ι)
    (θ : Fin m → Fin n) : face (x - y) τ θ = face x τ θ - face y τ θ :=
  map_sub _ _ _

lemma face_neg {m n : ℕ} (x : ∀ σ : Fin m → ι, P.obj (op (inter U σ))) (τ : Fin n → ι)
    (θ : Fin m → Fin n) : face (-x) τ θ = -face x τ θ :=
  map_neg _ _

lemma face_zero {m n : ℕ} (τ : Fin n → ι) (θ : Fin m → Fin n) :
    face (0 : ∀ σ : Fin m → ι, P.obj (op (inter U σ))) τ θ = 0 :=
  map_zero _

lemma face_zsmul {m n : ℕ} (c : ℤ) (x : ∀ σ : Fin m → ι, P.obj (op (inter U σ)))
    (τ : Fin n → ι) (θ : Fin m → Fin n) : face (c • x) τ θ = c • face x τ θ :=
  map_zsmul _ _ _

lemma face_sum {m n : ℕ} {α : Type*} (s : Finset α)
    (x : α → ∀ σ : Fin m → ι, P.obj (op (inter U σ))) (τ : Fin n → ι) (θ : Fin m → Fin n) :
    face (∑ a ∈ s, x a) τ θ = ∑ a ∈ s, face (x a) τ θ := by
  rw [face, Finset.sum_apply, map_sum]
  rfl

/-- The Čech differential in terms of faces. -/
lemma d_apply_face (p : ℕ) (z : C P U p) (τ : Fin (p + 2) → ι) :
    d P U p z τ = ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • face z τ k.succAbove :=
  d_apply P U p z τ

lemma face_d (p : ℕ) (z : C P U p) {n : ℕ} (τ : Fin n → ι) (θ : Fin (p + 2) → Fin n) :
    face (d P U p z) τ θ = ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • face z τ (θ ∘ k.succAbove) := by
  rw [face, d_apply_face, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, res_face]

/-- A `1`-cocycle vanishes on constant pairs `(i, i)`. -/
lemma cocycle_apply_const {z : C P U 1} (hz : d P U 1 z = 0) (i : ι) : z (fun _ => i) = 0 := by
  have h₃₂ : inter U (fun _ : Fin 3 => i) ≤ inter U (fun _ : Fin 2 => i) :=
    le_iInf fun _ => iInf_le (fun _ : Fin 3 => U i) 0
  have h₂₃ : inter U (fun _ : Fin 2 => i) ≤ inter U (fun _ : Fin 3 => i) :=
    le_iInf fun _ => iInf_le (fun _ : Fin 2 => U i) 0
  have key : ∀ k : Fin 3, res (inter_le_comp (fun _ : Fin 3 => i) k.succAbove)
      (z ((fun _ : Fin 3 => i) ∘ k.succAbove)) = res h₃₂ (z (fun _ => i)) := fun k => rfl
  have h := congrFun hz (fun _ => i)
  rw [d_apply] at h
  simp only [key] at h
  simp [Fin.sum_univ_three] at h
  have h' := congrArg (res h₂₃) h
  rwa [res_res, res_self, map_zero] at h'

lemma inter_two (a b : ι) : inter U ![a, b] = U a ⊓ U b := by
  apply le_antisymm
  · exact le_inf (inter_le_apply ![a, b] 0) (inter_le_apply ![a, b] 1)
  · refine le_iInf fun i => ?_
    fin_cases i
    · exact inf_le_left
    · exact inf_le_right

/-- The cocycle identity `z (x, y) + z (y, w) = z (x, w)` of a `1`-cocycle, on any open contained
in the three pairwise intersections. -/
lemma cocycle_add {z : C P U 1} (hz : d P U 1 z = 0) (x y w : ι) {O : Opens T}
    (h₁ : O ≤ inter U ![x, y]) (h₂ : O ≤ inter U ![y, w]) (h₃ : O ≤ inter U ![x, w]) :
    res h₁ (z ![x, y]) + res h₂ (z ![y, w]) = res h₃ (z ![x, w]) := by
  have hO : O ≤ inter U ![x, y, w] := by
    refine le_iInf fun i => ?_
    fin_cases i
    · exact h₁.trans (inter_le_apply ![x, y] 0)
    · exact h₁.trans (inter_le_apply ![x, y] 1)
    · exact h₂.trans (inter_le_apply ![y, w] 1)
  have h := congrArg (res hO) (congrFun hz ![x, y, w])
  rw [d_apply, map_sum, Fin.sum_univ_three] at h
  simp only [map_neg, res_res, Pi.zero_apply, map_zero, Fin.val_zero, Fin.val_one,
    Fin.val_two, pow_zero, pow_one, neg_one_sq, one_smul, neg_smul] at h
  rw [res_congr P U (σ := ![x, y, w] ∘ Fin.succAbove 0) (σ' := ![y, w])
      (by funext i; fin_cases i <;> rfl) z _ h₂,
    res_congr P U (σ := ![x, y, w] ∘ Fin.succAbove 1) (σ' := ![x, w])
      (by funext i; fin_cases i <;> rfl) z _ h₃,
    res_congr P U (σ := ![x, y, w] ∘ Fin.succAbove 2) (σ' := ![x, y])
      (by funext i; fin_cases i <;> rfl) z _ h₁] at h
  rw [← sub_eq_zero, ← h]
  abel

end Face

section Ring

variable {T : TopCat.{u}} (R : TopCat.Presheaf CommRingCat.{v} T) {ι : Type w}
  (U : ι → Opens T)

/-- The presheaf of abelian groups underlying a presheaf of commutative rings. -/
abbrev ab : TopCat.Presheaf AddCommGrpCat.{v} T :=
  R ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat

instance (V : Opens T) : CommRing ((ab R).obj (op V)) :=
  inferInstanceAs (CommRing (R.obj (op V)))

variable {R}

lemma res_mul {V W : Opens T} (h : V ≤ W) (x y : (ab R).obj (op W)) :
    res (P := ab R) h (x * y) = res h x * res h y :=
  map_mul (R.map (homOfLE h).op).hom x y

lemma res_one {V W : Opens T} (h : V ≤ W) : res (P := ab R) h 1 = 1 :=
  map_one (R.map (homOfLE h).op).hom

lemma res_prod {V W : Opens T} (h : V ≤ W) {α : Type*} (s : Finset α)
    (x : α → (ab R).obj (op W)) : res (P := ab R) h (∏ a ∈ s, x a) = ∏ a ∈ s, res h (x a) :=
  map_prod (R.map (homOfLE h).op).hom x s

variable {U}

lemma face_mul {m₁ m₂ n l : ℕ} (x : ∀ σ : Fin m₁ → ι, (ab R).obj (op (inter U σ)))
    (y : ∀ σ : Fin m₂ → ι, (ab R).obj (op (inter U σ))) (θ₁ : Fin m₁ → Fin l)
    (θ₂ : Fin m₂ → Fin l) (τ : Fin n → ι) (θ : Fin l → Fin n) :
    face (fun σ => face x σ θ₁ * face y σ θ₂) τ θ = face x τ (θ ∘ θ₁) * face y τ (θ ∘ θ₂) := by
  rw [face, res_mul, res_face, res_face]

lemma face_prod {m n l : ℕ} {α : Type*} (s : Finset α)
    (x : α → ∀ σ : Fin m → ι, (ab R).obj (op (inter U σ))) (θs : α → Fin m → Fin l)
    (τ : Fin n → ι) (θ : Fin l → Fin n) :
    face (fun σ => ∏ a ∈ s, face (x a) σ (θs a)) τ θ = ∏ a ∈ s, face (x a) τ (θ ∘ θs a) := by
  rw [face, res_prod]
  exact Finset.prod_congr rfl fun a _ => res_face _ _ _ _

lemma face_one {m n : ℕ} (τ : Fin n → ι) (θ : Fin m → Fin n) :
    face (fun σ : Fin m → ι => (1 : (ab R).obj (op (inter U σ)))) τ θ = 1 :=
  res_one _

/-- The edge `(k, k + 1)` of the standard `n`-simplex. -/
def edge {n : ℕ} (k : Fin n) : Fin 2 → Fin (n + 1) := ![k.castSucc, k.succ]

@[simp] lemma edge_zero {n : ℕ} (k : Fin n) : edge k 0 = k.castSucc := rfl

@[simp] lemma edge_one {n : ℕ} (k : Fin n) : edge k 1 = k.succ := rfl

lemma succ_succAbove_comp_succ {n : ℕ} (i : Fin (n + 1)) :
    i.succ.succAbove ∘ Fin.succ = Fin.succ ∘ i.succAbove := by
  funext a
  exact Fin.succ_succAbove_succ i a

lemma succ_succ_succAbove_comp_edge_zero {n : ℕ} (i : Fin (n + 1)) :
    i.succ.succ.succAbove ∘ edge (0 : Fin (n + 1)) = edge (0 : Fin (n + 2)) := by
  funext a
  fin_cases a
  · exact Fin.succ_succAbove_zero _
  · show i.succ.succ.succAbove (Fin.succ 0) = Fin.succ 0
    rw [Fin.succ_succAbove_succ, Fin.succ_succAbove_zero]

variable (R U)

/-- The unit `0`-cochain. -/
def one : C (ab R) U 0 := fun _ => 1

/-- The product of a `0`-cochain and a `q`-cochain. -/
def cup₀ {q : ℕ} (h : C (ab R) U 0) (b : C (ab R) U q) : C (ab R) U q :=
  fun τ => face h τ (fun _ => 0) * b τ

/-- The Alexander–Whitney product of a `1`-cochain and a `q`-cochain. -/
def cup₁ {q : ℕ} (z : C (ab R) U 1) (b : C (ab R) U q) : C (ab R) U (q + 1) :=
  fun τ => face z τ (edge 0) * face b τ Fin.succ

/-- The product of `n` one-cochains, `(prod n z) τ = ∏ₖ z k (τ k, τ (k + 1))`. -/
def prod (n : ℕ) (z : Fin n → C (ab R) U 1) : C (ab R) U n :=
  fun τ => ∏ k : Fin n, face (z k) τ (edge k)

variable {R U}

lemma cup₀_apply {q : ℕ} (h : C (ab R) U 0) (b : C (ab R) U q) (τ : Fin (q + 1) → ι) :
    cup₀ R U h b τ = face h τ (fun _ => 0) * b τ := rfl

lemma cup₁_apply {q : ℕ} (z : C (ab R) U 1) (b : C (ab R) U q) (τ : Fin (q + 2) → ι) :
    cup₁ R U z b τ = face z τ (edge 0) * face b τ Fin.succ := rfl

lemma prod_apply (n : ℕ) (z : Fin n → C (ab R) U 1) (τ : Fin (n + 1) → ι) :
    prod R U n z τ = ∏ k : Fin n, face (z k) τ (edge k) := rfl

lemma prod_zero (z : Fin 0 → C (ab R) U 1) : prod R U 0 z = one R U := by
  funext τ
  simp [prod, one]

lemma prod_one (z : Fin 1 → C (ab R) U 1) : prod R U 1 z = z 0 := by
  funext τ
  rw [prod_apply, Fin.prod_univ_one]
  refine (face_congr _ _ (θ' := id) ?_).trans (face_id _ _)
  funext a
  fin_cases a <;> rfl

lemma prod_succ (n : ℕ) (z : Fin (n + 1) → C (ab R) U 1) :
    prod R U (n + 1) z = cup₁ R U (z 0) (prod R U n (Fin.tail z)) := by
  funext τ
  rw [prod_apply, Fin.prod_univ_succ, cup₁_apply]
  show _ = _ * face (fun σ => ∏ k : Fin n, face (Fin.tail z k) σ (edge k)) τ Fin.succ
  rw [face_prod]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  refine face_congr _ _ ?_
  funext a
  refine Fin.cases ?_ (fun a => ?_) a
  · rfl
  · rw [Fin.fin_one_eq_zero a]
    rfl

lemma cup₁_add_left {q : ℕ} (z z' : C (ab R) U 1) (b : C (ab R) U q) :
    cup₁ R U (z + z') b = cup₁ R U z b + cup₁ R U z' b := by
  funext τ
  simp only [cup₁_apply, face_add, add_mul, Pi.add_apply]

lemma cup₁_sub_left {q : ℕ} (z z' : C (ab R) U 1) (b : C (ab R) U q) :
    cup₁ R U (z - z') b = cup₁ R U z b - cup₁ R U z' b := by
  funext τ
  simp only [cup₁_apply, face_sub, sub_mul, Pi.sub_apply]

lemma cup₁_add_right {q : ℕ} (z : C (ab R) U 1) (b b' : C (ab R) U q) :
    cup₁ R U z (b + b') = cup₁ R U z b + cup₁ R U z b' := by
  funext τ
  simp only [cup₁_apply, face_add, mul_add, Pi.add_apply]

lemma cup₁_sub_right {q : ℕ} (z : C (ab R) U 1) (b b' : C (ab R) U q) :
    cup₁ R U z (b - b') = cup₁ R U z b - cup₁ R U z b' := by
  funext τ
  simp only [cup₁_apply, face_sub, mul_sub, Pi.sub_apply]

lemma cup₁_neg_right {q : ℕ} (z : C (ab R) U 1) (b : C (ab R) U q) :
    cup₁ R U z (-b) = -cup₁ R U z b := by
  funext τ
  simp only [cup₁_apply, face_neg, mul_neg, Pi.neg_apply]

lemma cup₁_zero_right {q : ℕ} (z : C (ab R) U 1) : cup₁ R U z (0 : C (ab R) U q) = 0 := by
  funext τ
  simp only [cup₁_apply, face_zero, mul_zero, Pi.zero_apply]

lemma cup₀_zero_right {q : ℕ} (h : C (ab R) U 0) : cup₀ R U h (0 : C (ab R) U q) = 0 := by
  funext τ
  simp only [cup₀_apply, Pi.zero_apply, mul_zero]

lemma cup₀_sub_left {q : ℕ} (h h' : C (ab R) U 0) (b : C (ab R) U q) :
    cup₀ R U (h - h') b = cup₀ R U h b - cup₀ R U h' b := by
  funext τ
  simp only [cup₀_apply, face_sub, sub_mul, Pi.sub_apply]

private lemma zsmul_mul_eq {A : Type*} [CommRing A] (c : ℤ) (x y : A) :
    c • x * y = c • (x * y) := by
  rw [zsmul_eq_mul, zsmul_eq_mul, mul_assoc]

private lemma mul_zsmul_eq {A : Type*} [CommRing A] (c : ℤ) (x y : A) :
    x * c • y = c • (x * y) := by
  rw [zsmul_eq_mul, zsmul_eq_mul, mul_left_comm]

lemma face_one' {n : ℕ} (τ : Fin n → ι) (θ : Fin 1 → Fin n) :
    face (one R U) τ θ = 1 :=
  res_one _

lemma d_one : d (ab R) U 0 (one R U) = 0 := by
  funext τ
  rw [d_apply_face, Fin.sum_univ_two, face_one', face_one']
  simp

lemma face_cup₀ {q n : ℕ} (h : C (ab R) U 0) (b : C (ab R) U q) (τ : Fin n → ι)
    (θ : Fin (q + 1) → Fin n) :
    face (cup₀ R U h b) τ θ = face h τ (fun _ => θ 0) * face b τ θ := by
  rw [face, cup₀_apply, res_mul, res_face]
  rfl

lemma face_cup₁ {q n : ℕ} (z : C (ab R) U 1) (b : C (ab R) U q) (τ : Fin n → ι)
    (θ : Fin (q + 2) → Fin n) :
    face (cup₁ R U z b) τ θ = face z τ (θ ∘ edge 0) * face b τ (θ ∘ Fin.succ) := by
  rw [face, cup₁_apply, res_mul, res_face, res_face]

/-- The Leibniz rule for the product with a `0`-cochain. -/
lemma d_cup₀ (q : ℕ) (h : C (ab R) U 0) (b : C (ab R) U q) :
    d (ab R) U q (cup₀ R U h b) =
      cup₁ R U (d (ab R) U 0 h) b + cup₀ R U h (d (ab R) U q b) := by
  funext τ
  have e₀ : (edge (0 : Fin (q + 1)) ∘ (0 : Fin 2).succAbove) = fun _ : Fin 1 => 1 := by
    funext a
    rw [Fin.fin_one_eq_zero a]
    rfl
  have e₁ : (edge (0 : Fin (q + 1)) ∘ (1 : Fin 2).succAbove) = fun _ : Fin 1 => 0 := by
    funext a
    rw [Fin.fin_one_eq_zero a]
    rfl
  rw [Pi.add_apply, cup₁_apply, cup₀_apply, d_apply_face, d_apply_face, face_d,
    Fin.sum_univ_two, e₀, e₁]
  simp only [face_cup₀]
  conv_lhs => rw [Fin.sum_univ_succ]
  conv_rhs => rw [Fin.sum_univ_succ]
  simp only [Fin.succAbove_zero, Fin.succ_succAbove_zero, Fin.succ_zero_eq_one, Fin.val_zero,
    Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, Finset.mul_sum, mul_add, add_mul,
    neg_mul, mul_zsmul_eq]
  abel

/-- The Leibniz rule for the product with a `1`-cocycle. -/
lemma d_cup₁_of_cocycle {q : ℕ} {z : C (ab R) U 1} (hz : d (ab R) U 1 z = 0)
    (b : C (ab R) U q) :
    d (ab R) U (q + 1) (cup₁ R U z b) = -cup₁ R U z (d (ab R) U q b) := by
  funext τ
  have hc := congrArg (fun x => face x τ ![0, 1, 2]) hz
  simp only [face_d, face_zero] at hc
  rw [Fin.sum_univ_three, face_congr z τ (θ := ![0, 1, 2] ∘ Fin.succAbove 0)
      (θ' := Fin.succ ∘ edge (0 : Fin (q + 1))) (by funext a; fin_cases a <;> rfl),
    face_congr z τ (θ := ![0, 1, 2] ∘ Fin.succAbove 1)
      (θ' := Fin.succAbove (Fin.succ 0) ∘ edge (0 : Fin (q + 1)))
      (by funext a; fin_cases a <;> rfl),
    face_congr z τ (θ := ![0, 1, 2] ∘ Fin.succAbove 2)
      (θ' := edge (0 : Fin (q + 2))) (by funext a; fin_cases a <;> rfl)] at hc
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, neg_one_sq, one_smul,
    neg_smul] at hc
  rw [d_apply_face, Fin.sum_univ_succ, Fin.sum_univ_succ, Pi.neg_apply, cup₁_apply, face_d]
  conv_rhs => rw [Fin.sum_univ_succ]
  simp only [face_cup₁, Fin.succAbove_zero, succ_succAbove_comp_succ, Fin.val_zero,
    Fin.val_succ, zero_add, pow_zero, pow_succ, mul_neg, mul_one, neg_neg, one_smul, neg_smul,
    mul_add, Finset.mul_sum, mul_zsmul_eq, Finset.sum_neg_distrib]
  have e : ∀ x : Fin (q + 1), face z τ (x.succ.succ.succAbove ∘ edge 0) = face z τ (edge 0) :=
    fun x => face_congr _ _ (succ_succ_succAbove_comp_edge_zero x)
  simp only [e]
  linear_combination face b τ (Fin.succ ∘ Fin.succ) * hc

lemma prod_cocycle (n : ℕ) (z : Fin n → C (ab R) U 1) (hz : ∀ k, d (ab R) U 1 (z k) = 0) :
    d (ab R) U n (prod R U n z) = 0 := by
  induction n with
  | zero => rw [prod_zero, d_one]
  | succ n ih =>
    rw [prod_succ, d_cup₁_of_cocycle (hz 0), ih (Fin.tail z) (fun k => hz k.succ),
      cup₁_zero_right, neg_zero]

/-- Changing each factor by a coboundary changes the product of cocycles by a coboundary. -/
lemma prod_sub_eq_d (n : ℕ) (z z' : Fin (n + 1) → C (ab R) U 1)
    (hz : ∀ k, d (ab R) U 1 (z k) = 0) (hz' : ∀ k, d (ab R) U 1 (z' k) = 0)
    (h : Fin (n + 1) → C (ab R) U 0) (hh : ∀ k, z' k - z k = d (ab R) U 0 (h k)) :
    ∃ c : C (ab R) U n, prod R U (n + 1) z' - prod R U (n + 1) z = d (ab R) U n c := by
  induction n with
  | zero =>
    refine ⟨cup₀ R U (h 0) (one R U), ?_⟩
    rw [d_cup₀, d_one, cup₀_zero_right, add_zero, ← hh 0, cup₁_sub_left, prod_succ 0 z',
      prod_succ 0 z, prod_zero, prod_zero]
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih (Fin.tail z) (Fin.tail z') (fun k => hz k.succ) (fun k => hz' k.succ)
      (Fin.tail h) (fun k => hh k.succ)
    refine ⟨cup₀ R U (h 0) (prod R U (n + 1) (Fin.tail z')) - cup₁ R U (z 0) c, ?_⟩
    rw [map_sub, d_cup₀, prod_cocycle (n + 1) (Fin.tail z') (fun k => hz' k.succ),
      cup₀_zero_right, add_zero, d_cup₁_of_cocycle (hz 0), ← hc, ← hh 0,
      prod_succ (n + 1) z', prod_succ (n + 1) z, cup₁_sub_left, cup₁_sub_right]
    abel

end Ring

end Langlands.Cohomology.Cech
