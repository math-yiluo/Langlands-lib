import Langlands.GroupScheme.SplitExistence.ShortRoots

/-!
# The short-root module and its raising and lowering operators

Let `P` be a reduced root datum with a finite index type and a base `b`, and let
`gen : Fin r → X` be a family of weights. The *short-root module* is the free `ℤ`-module on

* vectors `u_t` of weight `0`, one for each simple root `t`;
* vectors `v_γ` of weight `α_γ`, one for each short root `γ` (`IsShortRoot`);
* vectors `x_ν` of weight `ν`, one for each `ν` in the union of the minimal-norm weight sets of
  the cosets `gen w + ℤΦ` (`minimalWeights`).

For a simple root `i`, the raising operator `raiseMat i` sends `u_t` to `|⟨α_t, α_i^∨⟩| v_{α_i}`
if `α_i` is short (and to `0` otherwise), `v_{-α_i}` to `u_i`, `v_γ` to `v_{γ + α_i}` when
`⟨α_γ, α_i^∨⟩ = -1`, and `x_ν` to `x_{ν + α_i}` when `⟨ν, α_i^∨⟩ = -1`; all other basis vectors
go to `0`. The lowering operator `lowerMat i` is the mirror image. Both are matrices with at most
one nonzero entry in each column (`colMat`), which makes products easy to compute.

The main result `raiseMat_mul_lowerMat_comm` says that the raising operator of a simple root
commutes with the lowering operator of a different simple root.
-/

noncomputable section

universe u

open Matrix RootPairing

namespace Langlands.GroupScheme.SplitExistence

/-! ### Matrices with at most one nonzero entry in each column -/

section ColMat

variable {B : Type*} [DecidableEq B]

/-- The matrix sending the basis vector `c` to `κ c` times the basis vector `f c`. -/
def colMat (f : B → B) (κ : B → ℤ) : Matrix B B ℤ :=
  of fun r c => if f c = r then κ c else 0

theorem colMat_apply (f : B → B) (κ : B → ℤ) (r c : B) :
    colMat f κ r c = if f c = r then κ c else 0 := rfl

theorem colMat_mul [Fintype B] (f g : B → B) (κ μ : B → ℤ) :
    colMat f κ * colMat g μ = colMat (f ∘ g) (fun c => κ (g c) * μ c) := by
  ext r c
  simp only [mul_apply, colMat_apply, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, Function.comp_apply, ite_mul, zero_mul]

theorem colMat_congr {f f' : B → B} {κ κ' : B → ℤ}
    (h : ∀ c, κ c = κ' c ∧ (κ c ≠ 0 → f c = f' c)) : colMat f κ = colMat f' κ' := by
  ext r c
  rw [colMat_apply, colMat_apply]
  obtain ⟨h1, h2⟩ := h c
  by_cases hc : κ c = 0
  · rw [← h1, hc]
    simp
  · rw [h2 hc, h1]

theorem submatrix_eq_colMat {B' : Type*} [DecidableEq B'] (σ : B ≃ B') {A : Matrix B' B' ℤ}
    {f : B → B} {κ : B → ℤ} (h : ∀ c x, A x (σ c) = if σ (f c) = x then κ c else 0) :
    A.submatrix σ σ = colMat f κ := by
  ext r c
  rw [submatrix_apply, h, colMat_apply]
  simp only [σ.apply_eq_iff_eq]

theorem colMat_map_ne_zero {f : B → B} {κ : B → ℤ} {c : B} (hc : κ c = 1) (p : ℕ)
    [Fact p.Prime] : (colMat f κ).map (Int.castRingHom (ZMod p)) ≠ 0 := by
  intro h
  have := congrFun (congrFun h (f c)) c
  simp [colMat_apply, hc] at this

end ColMat

/-! ### Facts about roots and reflections -/

section Roots

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y}

theorem root_reflectionPerm_eq (i k : J) :
    P.root (P.reflectionPerm i k) = P.root k - P.pairing k i • P.root i := by
  rw [root_reflectionPerm, reflection_apply_root]

theorem eq_zero_of_smul_root_eq_zero {i : J} {z : ℤ} (h : z • P.root i = 0) : z = 0 := by
  have := congrArg (fun x => P.toLinearMap x (P.coroot i)) h
  simp only [map_zsmul, LinearMap.smul_apply, root_coroot_eq_pairing, pairing_same,
    smul_eq_mul, map_zero, LinearMap.zero_apply] at this
  omega

theorem root_reflectionPerm_eq_self_iff (i k : J) :
    P.root (P.reflectionPerm i k) = P.root k ↔ P.pairing k i = 0 := by
  rw [root_reflectionPerm_eq, sub_eq_self]
  exact ⟨eq_zero_of_smul_root_eq_zero, fun h => by rw [h, zero_smul]⟩

theorem root_ne_neg_self (i : J) : P.root i ≠ -P.root i := by
  intro h
  have h2 : (2 : ℤ) • P.root i = 0 := by
    rw [two_smul]
    nth_rw 1 [h]
    exact neg_add_cancel _
  exact absurd (eq_zero_of_smul_root_eq_zero h2) (by norm_num)

theorem toLinearMap_reflection_coroot (i j : J) (x : X) :
    P.toLinearMap (P.reflection j x) (P.coroot i) =
      P.toLinearMap x (P.coroot i) - P.toLinearMap x (P.coroot j) * P.pairing j i := by
  show _ = P.toLinearMap x (P.coroot i) - P.coroot' j x * P.pairing j i
  rw [reflection_apply, map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply,
    root_coroot_eq_pairing, smul_eq_mul]

theorem IsShortRoot.neg_one_le_pairing {j : J} (hj : IsShortRoot P j) {k : J}
    (hk : P.root j ≠ -P.root k) : -1 ≤ P.pairing j k := by
  by_cases h : P.root k = P.root j
  · rw [P.root.injective h, pairing_same]
    norm_num
  · have h' : P.root k ≠ -P.root j := fun h' => hk (by rw [h', neg_neg])
    exact (abs_le.1 (hj k h h')).1

theorem IsShortRoot.pairing_le_one {j : J} (hj : IsShortRoot P j) {k : J}
    (hk : P.root j ≠ P.root k) : P.pairing j k ≤ 1 := by
  by_cases h : P.root k = -P.root j
  · have hk' : k = P.reflectionPerm j j :=
      P.root.injective (by rw [h, root_reflectionPerm_self])
    rw [hk', pairing_reflectionPerm_self_right, pairing_same]
    norm_num
  · exact (abs_le.1 (hj k (Ne.symm hk) h)).2

variable [Finite J] [P.IsReduced] (b : P.Base)

omit [P.IsReduced] in
theorem pairing_le_zero_of_mem_support {i j : J} (hi : i ∈ b.support) (hj : j ∈ b.support)
    (hij : i ≠ j) : P.pairing i j ≤ 0 := by
  rw [← pairingIn_int]
  exact b.pairingIn_le_zero_of_ne hij hi hj

/-- The possible pairings of two distinct simple roots. -/
theorem pairing_cases_of_mem_support {i j : J} (hi : i ∈ b.support) (hj : j ∈ b.support)
    (hij : i ≠ j) :
    (P.pairing i j = 0 ∧ P.pairing j i = 0) ∨ (P.pairing i j = -1 ∧ P.pairing j i = -1) ∨
      (P.pairing i j = -1 ∧ P.pairing j i ≤ -2) ∨ (P.pairing i j ≤ -2 ∧ P.pairing j i = -1) := by
  have h1 := pairing_le_zero_of_mem_support b hi hj hij
  have h2 := pairing_le_zero_of_mem_support b hj hi (Ne.symm hij)
  have hmem := pairing_pairing_mem (P := P) (i := i) (j := j)
    (fun h => hij (P.root.injective h)) (b.root_ne_neg_of_ne hi hj hij)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  omega

end Roots

/-! ### The index set of the short-root module -/

section Module

variable {J X Y : Type u} [Fintype J] [AddCommGroup X] [AddCommGroup Y] (P : RootDatum J X Y)
  (b : P.Base) {r : ℕ} (gen : Fin r → X)

open Classical

/-- The short roots. -/
abbrev ShortIdx : Type u := {j : J // IsShortRoot P j}

/-- The union of the minimal-norm weight sets of the cosets `gen w + ℤΦ`. -/
abbrev MinIdx : Type u := {ν : X // ∃ w, ν ∈ minimalWeights P (gen w)}

/-- The basis of the short-root module: the simple roots (weight `0`), the short roots and the
minimal-norm weights. -/
abbrev Idx : Type u := (↥b.support ⊕ ShortIdx P) ⊕ MinIdx P gen

instance : Finite (MinIdx P gen) :=
  Set.Finite.to_subtype (s := {ν : X | ∃ w, ν ∈ minimalWeights P (gen w)})
    ((Set.finite_iUnion fun w => minimalWeights_finite (P := P) (gen w)).subset
      fun _ hν => Set.mem_iUnion.2 hν)

instance : Fintype (MinIdx P gen) := Fintype.ofFinite _

instance : Fintype (ShortIdx P) := Subtype.fintype _

instance : DecidableEq (Idx P b gen) := Classical.decEq _

/-- The weight of a basis vector of the short-root module. -/
def idxWt : Idx P b gen → X :=
  Sum.elim (Sum.elim 0 fun γ => P.root γ) fun ν => ν.1

variable {P b gen}

/-- The reflection of a short root. -/
def shRefl (i : J) (γ : ShortIdx P) : ShortIdx P :=
  ⟨P.reflectionPerm i γ, γ.2.reflectionPerm i⟩

omit [Fintype J] in
theorem coe_shRefl (i : J) (γ : ShortIdx P) : (shRefl i γ : J) = P.reflectionPerm i γ := rfl

omit [Fintype J] in
theorem coe_shRefl_self (i : J) (h : IsShortRoot P i) :
    (shRefl (P := P) i ⟨i, h⟩ : J) = P.reflectionPerm i i := rfl

theorem minIdx_reflection_mem (i : J) (ν : MinIdx P gen) :
    ∃ w, P.reflection i ν.1 ∈ minimalWeights P (gen w) := by
  obtain ⟨w, hw⟩ := ν.2
  exact ⟨w, reflection_mem_minimalWeights hw i⟩

/-- The reflection of a minimal-norm weight. -/
def minRefl (i : J) (ν : MinIdx P gen) : MinIdx P gen :=
  ⟨P.reflection i ν.1, minIdx_reflection_mem i ν⟩

theorem coe_minRefl (i : J) (ν : MinIdx P gen) : (minRefl i ν).1 = P.reflection i ν.1 := rfl

theorem minIdx_pairing (ν : MinIdx P gen) (j : J) :
    -1 ≤ P.toLinearMap ν.1 (P.coroot j) ∧ P.toLinearMap ν.1 (P.coroot j) ≤ 1 := by
  obtain ⟨w, hw⟩ := ν.2
  exact ⟨neg_one_le_pairing hw j, pairing_le_one hw j⟩

/-! ### The raising and lowering operators -/

variable (P b gen)

/-- The target of a basis vector under the raising operator of the simple root `i`. -/
def raiseTgt (i : b.support) : Idx P b gen → Idx P b gen
  | .inl (.inl t) => if h : IsShortRoot P i then .inl (.inr ⟨i, h⟩) else .inl (.inl t)
  | .inl (.inr γ) => if P.root γ = -P.root i then .inl (.inl i) else .inl (.inr (shRefl i γ))
  | .inr ν => .inr (minRefl i ν)

/-- The coefficient of a basis vector under the raising operator of the simple root `i`. -/
def raiseCoeff (i : b.support) : Idx P b gen → ℤ
  | .inl (.inl t) => if IsShortRoot P i then |P.pairing t i| else 0
  | .inl (.inr γ) => if P.root γ = -P.root i then 1 else if P.pairing γ i = -1 then 1 else 0
  | .inr ν => if P.toLinearMap ν.1 (P.coroot i) = -1 then 1 else 0

/-- The target of a basis vector under the lowering operator of the simple root `i`. -/
def lowerTgt (i : b.support) : Idx P b gen → Idx P b gen
  | .inl (.inl t) => if h : IsShortRoot P i then .inl (.inr (shRefl i ⟨i, h⟩)) else .inl (.inl t)
  | .inl (.inr γ) => if P.root γ = P.root i then .inl (.inl i) else .inl (.inr (shRefl i γ))
  | .inr ν => .inr (minRefl i ν)

/-- The coefficient of a basis vector under the lowering operator of the simple root `i`. -/
def lowerCoeff (i : b.support) : Idx P b gen → ℤ
  | .inl (.inl t) => if IsShortRoot P i then |P.pairing t i| else 0
  | .inl (.inr γ) => if P.root γ = P.root i then 1 else if P.pairing γ i = 1 then 1 else 0
  | .inr ν => if P.toLinearMap ν.1 (P.coroot i) = 1 then 1 else 0

/-- The raising operator of the simple root `i` on the short-root module. -/
def raiseMat (i : b.support) : Matrix (Idx P b gen) (Idx P b gen) ℤ :=
  colMat (raiseTgt P b gen i) (raiseCoeff P b gen i)

/-- The lowering operator of the simple root `i` on the short-root module. -/
def lowerMat (i : b.support) : Matrix (Idx P b gen) (Idx P b gen) ℤ :=
  colMat (lowerTgt P b gen i) (lowerCoeff P b gen i)

variable {P b gen}

section Eval

variable (i : b.support)

theorem raiseTgt_inl_inl (t : b.support) :
    raiseTgt P b gen i (.inl (.inl t)) =
      if h : IsShortRoot P i then .inl (.inr ⟨i, h⟩) else .inl (.inl t) := rfl

theorem raiseCoeff_inl_inl (t : b.support) :
    raiseCoeff P b gen i (.inl (.inl t)) = if IsShortRoot P i then |P.pairing t i| else 0 := rfl

theorem lowerTgt_inl_inl (t : b.support) :
    lowerTgt P b gen i (.inl (.inl t)) =
      if h : IsShortRoot P i then .inl (.inr (shRefl i ⟨i, h⟩)) else .inl (.inl t) := rfl

theorem lowerCoeff_inl_inl (t : b.support) :
    lowerCoeff P b gen i (.inl (.inl t)) = if IsShortRoot P i then |P.pairing t i| else 0 := rfl

variable {i}

theorem raiseTgt_of_eq {γ : ShortIdx P} (h : P.root γ = -P.root i) :
    raiseTgt P b gen i (.inl (.inr γ)) = .inl (.inl i) := by
  simp [raiseTgt, h]

theorem raiseCoeff_of_eq {γ : ShortIdx P} (h : P.root γ = -P.root i) :
    raiseCoeff P b gen i (.inl (.inr γ)) = 1 := by
  simp [raiseCoeff, h]

theorem raiseTgt_of_ne {γ : ShortIdx P} (h : P.root γ ≠ -P.root i) :
    raiseTgt P b gen i (.inl (.inr γ)) = .inl (.inr (shRefl i γ)) := by
  simp [raiseTgt, h]

theorem raiseCoeff_of_ne {γ : ShortIdx P} (h : P.root γ ≠ -P.root i) :
    raiseCoeff P b gen i (.inl (.inr γ)) = if P.pairing γ i = -1 then 1 else 0 := by
  simp [raiseCoeff, h]

theorem lowerTgt_of_eq {γ : ShortIdx P} (h : P.root γ = P.root i) :
    lowerTgt P b gen i (.inl (.inr γ)) = .inl (.inl i) := by
  simp [lowerTgt, h]

theorem lowerCoeff_of_eq {γ : ShortIdx P} (h : P.root γ = P.root i) :
    lowerCoeff P b gen i (.inl (.inr γ)) = 1 := by
  simp [lowerCoeff, h]

theorem lowerTgt_of_ne {γ : ShortIdx P} (h : P.root γ ≠ P.root i) :
    lowerTgt P b gen i (.inl (.inr γ)) = .inl (.inr (shRefl i γ)) := by
  simp [lowerTgt, h]

theorem lowerCoeff_of_ne {γ : ShortIdx P} (h : P.root γ ≠ P.root i) :
    lowerCoeff P b gen i (.inl (.inr γ)) = if P.pairing γ i = 1 then 1 else 0 := by
  simp [lowerCoeff, h]

theorem raiseTgt_inr (ν : MinIdx P gen) : raiseTgt P b gen i (.inr ν) = .inr (minRefl i ν) := rfl

theorem raiseCoeff_inr (ν : MinIdx P gen) :
    raiseCoeff P b gen i (.inr ν) = if P.toLinearMap ν.1 (P.coroot i) = -1 then 1 else 0 := rfl

theorem lowerTgt_inr (ν : MinIdx P gen) : lowerTgt P b gen i (.inr ν) = .inr (minRefl i ν) := rfl

theorem lowerCoeff_inr (ν : MinIdx P gen) :
    lowerCoeff P b gen i (.inr ν) = if P.toLinearMap ν.1 (P.coroot i) = 1 then 1 else 0 := rfl

end Eval

/-! ### Commutation of raising and lowering operators of distinct simple roots -/

/-- The integer identity behind the commutation on a weight `x` with `a = ⟨x, α_i^∨⟩ ≥ -1`,
`c = ⟨x, α_j^∨⟩ ≤ 1`, and pairings `p = ⟨α_i, α_j^∨⟩`, `q = ⟨α_j, α_i^∨⟩` of distinct simple
roots. -/
theorem comm_arith {a c p q : ℤ} (ha : -1 ≤ a) (hc : c ≤ 1) (hp : p ≤ 0) (hq : q ≤ 0)
    (hpq : p = 0 ↔ q = 0) :
    ((c = 1 ∧ a - c * q = -1) ↔ (a = -1 ∧ c - a * p = 1)) ∧
      (c = 1 ∧ a - c * q = -1 → a = -1 ∧ c = 1 ∧ p = 0 ∧ q = 0) := by
  have key : c = 1 ∧ a - c * q = -1 → a = -1 ∧ c = 1 ∧ p = 0 ∧ q = 0 := by
    rintro ⟨rfl, h⟩
    rw [one_mul] at h
    have hq0 : q = 0 := by omega
    exact ⟨by omega, rfl, hpq.2 hq0, hq0⟩
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, key⟩
  · obtain ⟨ha', hc', hp', hq'⟩ := key h
    subst ha' hc' hp'
    norm_num
  · obtain ⟨rfl, h⟩ := h
    have hp0 : p = 0 := by
      have : c + p = 1 := by linarith
      omega
    have hc1 : c = 1 := by
      rw [hp0] at h
      linarith
    subst hc1 hp0
    rw [hpq.1 rfl]
    norm_num

theorem ite_one_zero_mul_ite_one_zero {p q : Prop} [Decidable p] [Decidable q] :
    ((if p then 1 else 0 : ℤ) * if q then 1 else 0) = if q ∧ p then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

variable [P.IsReduced]

/-- The raising operator of a simple root commutes with the lowering operator of a different
simple root. -/
theorem raiseMat_mul_lowerMat_comm {i j : b.support} (hij : i ≠ j) :
    raiseMat P b gen i * lowerMat P b gen j = lowerMat P b gen j * raiseMat P b gen i := by
  have hij' : (i : J) ≠ j := fun h => hij (Subtype.ext h)
  have hpij := pairing_le_zero_of_mem_support b i.2 j.2 hij'
  have hpji := pairing_le_zero_of_mem_support b j.2 i.2 hij'.symm
  have hcases := pairing_cases_of_mem_support b i.2 j.2 hij'
  have hpq : P.pairing i j = 0 ↔ P.pairing j i = 0 := by omega
  have hrij : P.root i ≠ P.root j := fun h => hij' (P.root.injective h)
  have hrij' : P.root i ≠ -P.root j := b.root_ne_neg_of_ne i.2 j.2 hij'
  have hrji' : P.root j ≠ -P.root i := b.root_ne_neg_of_ne j.2 i.2 hij'.symm
  rw [raiseMat, lowerMat, colMat_mul, colMat_mul]
  refine colMat_congr fun c => ?_
  simp only [Function.comp_apply]
  rcases c with (t | γ) | ν
  · -- the vectors `u_t`: both composites vanish
    have h1 : raiseCoeff P b gen i (lowerTgt P b gen j (.inl (.inl t))) *
        lowerCoeff P b gen j (.inl (.inl t)) = 0 := by
      by_cases hjs : IsShortRoot P j
      · have hne : P.root (shRefl (P := P) j ⟨j, hjs⟩ : J) ≠ -P.root i := by
          rw [coe_shRefl_self, root_reflectionPerm_self, ne_eq, neg_inj]
          exact Ne.symm hrij
        have hp : ¬ P.pairing (shRefl (P := P) j ⟨j, hjs⟩ : J) i = -1 := by
          rw [coe_shRefl_self, pairing_reflectionPerm_self_left]
          omega
        rw [lowerTgt_inl_inl, dite_eq_left hjs, raiseCoeff_of_ne hne, ite_eq_right hp, zero_mul]
      · rw [lowerCoeff_inl_inl, ite_eq_right hjs, mul_zero]
    have h2 : lowerCoeff P b gen j (raiseTgt P b gen i (.inl (.inl t))) *
        raiseCoeff P b gen i (.inl (.inl t)) = 0 := by
      by_cases his : IsShortRoot P i
      · have h0 : lowerCoeff P b gen j (.inl (.inr ⟨i, his⟩)) = 0 := by
          rw [lowerCoeff_of_ne (γ := (⟨(i : J), his⟩ : ShortIdx P)) hrij]
          exact ite_eq_right (show ¬ P.pairing i j = 1 by omega)
        rw [raiseTgt_inl_inl, dite_eq_left his, h0, zero_mul]
      · rw [raiseCoeff_inl_inl, ite_eq_right his, mul_zero]
    exact ⟨by rw [h1, h2], fun h => absurd h1 h⟩
  · by_cases ha : P.root γ = P.root j
    · -- `γ = α_j`
      have hγ : (γ : J) = j := P.root.injective ha
      have hjs : IsShortRoot P j := hγ ▸ γ.2
      have hγi : P.root γ ≠ -P.root i := by rw [ha]; exact hrji'
      rw [lowerTgt_of_eq ha, lowerCoeff_of_eq ha, raiseTgt_of_ne hγi, raiseCoeff_of_ne hγi,
        raiseCoeff_inl_inl, raiseTgt_inl_inl, mul_one, hγ]
      have hδ : P.root (shRefl (P := P) i γ : J) = P.root j - P.pairing j i • P.root i := by
        rw [coe_shRefl, root_reflectionPerm_eq, hγ]
      rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2]
        simp
      · -- `⟨α_i, α_j^∨⟩ = ⟨α_j, α_i^∨⟩ = -1`: both composites send `v_{α_j}` to `v_{α_i}`
        have hδne : P.root (shRefl (P := P) i γ : J) ≠ P.root j := by
          rw [ne_eq, ← ha, coe_shRefl, root_reflectionPerm_eq_self_iff, hγ, h2]
          norm_num
        have hδj : P.pairing (shRefl (P := P) i γ : J) j = 1 := by
          rw [coe_shRefl, pairing_reflectionPerm_left, hγ, pairing_same, h1, h2]
          norm_num
        have hroot : P.root (P.reflectionPerm j (shRefl (P := P) i γ : J)) = P.root i := by
          rw [root_reflectionPerm_eq, hδj, hδ, h2]
          module
        have his : IsShortRoot P i :=
          ((shRefl (P := P) i γ).2.reflectionPerm j).of_root_eq (Or.inl hroot.symm)
        rw [ite_eq_left his, dite_eq_left his, h2, lowerCoeff_of_ne hδne, ite_eq_left hδj]
        refine ⟨by norm_num, fun _ => ?_⟩
        rw [lowerTgt_of_ne hδne]
        exact congrArg (fun x => Sum.inl (Sum.inr x)) (Subtype.ext (P.root.injective hroot.symm))
      · -- `|⟨α_j, α_i^∨⟩| ≥ 2` contradicts the shortness of `α_j`
        have := abs_le.1 (hjs i hrij hrij')
        omega
      · -- `α_i` is not short, and `⟨s_i α_j, α_j^∨⟩ ≠ 1`
        have his : ¬ IsShortRoot P i := fun his =>
          absurd (abs_le.1 (his j (Ne.symm hrij) hrji')).1 (by omega)
        have hδne : P.root (shRefl (P := P) i γ : J) ≠ P.root j := by
          rw [ne_eq, ← ha, coe_shRefl, root_reflectionPerm_eq_self_iff, hγ, h2]
          norm_num
        have hδj : ¬ P.pairing (shRefl (P := P) i γ : J) j = 1 := by
          rw [coe_shRefl, pairing_reflectionPerm_left, hγ, pairing_same, h2]
          omega
        rw [ite_eq_right his, lowerCoeff_of_ne hδne, ite_eq_right hδj, zero_mul]
        exact ⟨rfl, fun h => absurd rfl h⟩
    by_cases hb : P.root γ = -P.root i
    · -- `γ = -α_i`
      have hγ : (γ : J) = P.reflectionPerm i i :=
        P.root.injective (by rw [hb, root_reflectionPerm_self])
      have his : IsShortRoot P i := γ.2.of_root_eq (Or.inr (by rw [hb, neg_neg]))
      have hγj : P.root γ ≠ P.root j := by
        rw [hb]
        exact fun h => hrji' h.symm
      have hγj' : P.pairing γ j = -P.pairing i j := by
        rw [hγ, pairing_reflectionPerm_self_left]
      rw [lowerTgt_of_ne hγj, lowerCoeff_of_ne hγj, raiseTgt_of_eq hb, raiseCoeff_of_eq hb,
        lowerCoeff_inl_inl, lowerTgt_inl_inl, mul_one, hγj']
      have hδ : P.root (shRefl (P := P) j γ : J) = -P.root i + P.pairing i j • P.root j := by
        rw [coe_shRefl, root_reflectionPerm_eq, hγj', hb]
        module
      have hδi : P.pairing (shRefl (P := P) j γ : J) i = -2 + P.pairing i j * P.pairing j i := by
        rw [coe_shRefl, pairing_reflectionPerm_left, hγj', hγ, pairing_reflectionPerm_self_left,
          pairing_same]
        ring
      rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1]
        simp
      · have hδne : P.root (shRefl (P := P) j γ : J) ≠ -P.root i := by
          rw [ne_eq, ← hb, coe_shRefl, root_reflectionPerm_eq_self_iff, hγj', h1]
          norm_num
        have hδi' : P.pairing (shRefl (P := P) j γ : J) i = -1 := by
          rw [hδi, h1, h2]
          norm_num
        have hroot : P.root (P.reflectionPerm i (shRefl (P := P) j γ : J)) = -P.root j := by
          rw [root_reflectionPerm_eq, hδi', hδ, h1]
          module
        have hjs : IsShortRoot P j :=
          ((shRefl (P := P) j γ).2.reflectionPerm i).of_root_eq (Or.inr (by rw [hroot, neg_neg]))
        rw [raiseCoeff_of_ne hδne, ite_eq_left hδi', ite_eq_left hjs, dite_eq_left hjs, h1]
        refine ⟨by norm_num, fun _ => ?_⟩
        rw [raiseTgt_of_ne hδne]
        refine congrArg (fun x => Sum.inl (Sum.inr x)) (Subtype.ext (P.root.injective ?_))
        show P.root (P.reflectionPerm i (shRefl (P := P) j γ : J)) = P.root (P.reflectionPerm j j)
        rw [hroot, root_reflectionPerm_self]
      · have hjs : ¬ IsShortRoot P j := fun hjs =>
          absurd (abs_le.1 (hjs i hrij hrij')).1 (by omega)
        have hδne : P.root (shRefl (P := P) j γ : J) ≠ -P.root i := by
          rw [ne_eq, ← hb, coe_shRefl, root_reflectionPerm_eq_self_iff, hγj', h1]
          norm_num
        have hδi' : ¬ P.pairing (shRefl (P := P) j γ : J) i = -1 := by
          rw [hδi, h1]
          omega
        rw [ite_eq_right hjs, raiseCoeff_of_ne hδne, ite_eq_right hδi', zero_mul]
        exact ⟨rfl, fun h => absurd rfl h⟩
      · have := abs_le.1 (his j (Ne.symm hrij) hrji')
        omega
    · -- the generic case
      have ha1 : -1 ≤ P.pairing γ i := γ.2.neg_one_le_pairing hb
      have hc1 : P.pairing γ j ≤ 1 := γ.2.pairing_le_one ha
      have harith := comm_arith ha1 hc1 hpij hpji hpq
      have hδ1 : P.pairing (shRefl (P := P) j γ : J) i =
          P.pairing γ i - P.pairing γ j * P.pairing j i := by
        rw [coe_shRefl, pairing_reflectionPerm_left]
      have hδ2 : P.pairing (shRefl (P := P) i γ : J) j =
          P.pairing γ j - P.pairing γ i * P.pairing i j := by
        rw [coe_shRefl, pairing_reflectionPerm_left]
      have hδne : P.pairing γ j = 1 → P.root (shRefl (P := P) j γ : J) ≠ -P.root i := by
        intro hc h
        have hγ' : P.root γ = P.root j - P.root i := by
          have h' : P.root (shRefl (P := P) j γ : J) = P.root γ - P.root j := by
            rw [coe_shRefl, root_reflectionPerm_eq, hc, one_smul]
          rw [h] at h'
          rw [← sub_eq_zero]
          rw [← sub_eq_zero] at h'
          rw [← neg_eq_zero, ← h']
          abel
        have : P.pairing γ j = 2 - P.pairing i j := by
          rw [← root_coroot_eq_pairing, hγ', map_sub, LinearMap.sub_apply,
            root_coroot_eq_pairing, root_coroot_eq_pairing, pairing_same]
        omega
      have hεne : P.pairing γ i = -1 → P.root (shRefl (P := P) i γ : J) ≠ P.root j := by
        intro ha' h
        have hγ' : P.root γ = P.root j - P.root i := by
          rw [← h, coe_shRefl, root_reflectionPerm_eq, ha']
          module
        have : P.pairing γ i = P.pairing j i - 2 := by
          rw [← root_coroot_eq_pairing, hγ', map_sub, LinearMap.sub_apply,
            root_coroot_eq_pairing, root_coroot_eq_pairing, pairing_same]
        omega
      rw [lowerTgt_of_ne ha, lowerCoeff_of_ne ha, raiseTgt_of_ne hb, raiseCoeff_of_ne hb]
      have hL : raiseCoeff P b gen i (.inl (.inr (shRefl (P := P) j γ))) *
          (if P.pairing γ j = 1 then 1 else 0) =
          if P.pairing γ j = 1 ∧ P.pairing γ i - P.pairing γ j * P.pairing j i = -1 then 1
            else 0 := by
        by_cases hc : P.pairing γ j = 1
        · rw [raiseCoeff_of_ne (hδne hc), hδ1, ite_one_zero_mul_ite_one_zero]
        · rw [ite_eq_right hc, mul_zero, ite_eq_right (fun h => hc h.1)]
      have hR : lowerCoeff P b gen j (.inl (.inr (shRefl (P := P) i γ))) *
          (if P.pairing γ i = -1 then 1 else 0) =
          if P.pairing γ i = -1 ∧ P.pairing γ j - P.pairing γ i * P.pairing i j = 1 then 1
            else 0 := by
        by_cases ha' : P.pairing γ i = -1
        · rw [lowerCoeff_of_ne (hεne ha'), hδ2, ite_one_zero_mul_ite_one_zero]
        · rw [ite_eq_right ha', mul_zero, ite_eq_right (fun h => ha' h.1)]
      rw [hL, hR]
      refine ⟨if_congr harith.1 rfl rfl, fun h => ?_⟩
      have h' : P.pairing γ j = 1 ∧ P.pairing γ i - P.pairing γ j * P.pairing j i = -1 := by
        by_contra hn
        exact h (ite_eq_right hn)
      obtain ⟨ha', hc', hp0, hq0⟩ := harith.2 h'
      rw [raiseTgt_of_ne (hδne hc'), lowerTgt_of_ne (hεne ha')]
      refine congrArg (fun x => Sum.inl (Sum.inr x)) (Subtype.ext (P.root.injective ?_))
      simp only [coe_shRefl, root_reflectionPerm_eq, pairing_reflectionPerm_left, ha', hc', hp0,
        hq0]
      module
  · -- the minimal-norm weights
    simp only [raiseTgt_inr, lowerTgt_inr, raiseCoeff_inr, lowerCoeff_inr, coe_minRefl,
      toLinearMap_reflection_coroot]
    have harith := comm_arith (minIdx_pairing ν i).1 (minIdx_pairing ν j).2 hpij hpji hpq
    rw [ite_one_zero_mul_ite_one_zero, ite_one_zero_mul_ite_one_zero]
    refine ⟨if_congr harith.1 rfl rfl, fun h => ?_⟩
    have h' : P.toLinearMap ν.1 (P.coroot j) = 1 ∧
        P.toLinearMap ν.1 (P.coroot i) - P.toLinearMap ν.1 (P.coroot j) * P.pairing j i = -1 := by
      by_contra hn
      exact h (ite_eq_right hn)
    obtain ⟨ha', hc', hp0, hq0⟩ := harith.2 h'
    refine congrArg Sum.inr (Subtype.ext ?_)
    have e1 : ∀ (k : J) (y : X), P.reflection k y = y - P.toLinearMap y (P.coroot k) • P.root k :=
      fun _ _ => rfl
    simp only [coe_minRefl, e1, map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply,
      root_coroot_eq_pairing, smul_eq_mul, ha', hc', hp0, hq0]
    module

end Module

end Langlands.GroupScheme.SplitExistence
