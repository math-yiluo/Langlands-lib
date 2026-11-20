import Langlands.BushnellKutzko.LevelAttainingStratum

/-! # Products in a coset and a determinant bound on compact sets

Two algebraic inputs to the lower bound for the conductor of a supercuspidal representation in
terms of its normalized level.

* **Products.** If `b ∈ 𝔓^j(𝓛)` and `x₁, …, x_k ∈ b + 𝔓^{j+1}(𝓛)`, then
  `x₁ ⋯ x_k ∈ b^k + 𝔓^{kj+1}(𝓛)` (`LatticeChain.list_prod_sub_pow_mem`). Hence, if no power
  `b^k` lies in `𝔓^{kj+1}(𝓛)`, no such product lies in `𝔓^{kj+1}(𝓛)`
  (`LatticeChain.list_prod_not_mem`).
* **Determinants.** If `X ∈ 𝔓^a(𝓛)` has nonzero determinant, then
  `N a ≤ e(𝓛) ord(det X)`, where `N` is the dimension
  (`LatticeChain.card_mul_le_period_mul_ordOf_det`). The proof applies integrality of
  determinants on `𝔄(𝓛) = 𝔓^0(𝓛)` to `ϖ^{-a} X^e ∈ 𝔓^0(𝓛)`.
* **Compact sets.** For a compact set `C` of invertible matrices there is `B` such that, for all
  `g ∈ C`, all `a ∈ F^×` and all `j ∈ ℤ`, if `a g ∉ 𝔓^j(𝓛)` then
  `e(𝓛) ord(det(a g)) < N j + B` (`LatticeChain.exists_period_mul_ordOf_det_lt`).
* **Growth.** Consequently, if for every `n` some `a g` with `g ∈ C` lies outside
  `𝔓^{nj+1}(𝓛)` and has `ord(det(a g)) = n μ`, then `e(𝓛) μ ≤ N j`
  (`LatticeChain.period_mul_le_of_forall_exists`).
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe u

/-! ### Products of elements of a coset -/

section Product

variable {F : Type u} [Field F] [ValuativeRel F]
variable {ι : Type*}

namespace LatticeChain

variable (𝓛 : LatticeChain 𝒪[F] F (ι → F))

/-- If `b ∈ 𝔓^j(𝓛)` and every factor of the list `l` lies in `b + 𝔓^{j+1}(𝓛)`, then the
product of the `k` factors lies in `b^k + 𝔓^{kj+1}(𝓛)`. -/
theorem list_prod_sub_pow_mem {j : ℤ} {b : Module.End F (ι → F)}
    (hb : b ∈ 𝓛.endFiltration j) (l : List (Module.End F (ι → F)))
    (hl : ∀ x ∈ l, x - b ∈ 𝓛.endFiltration (j + 1)) :
    l.prod - b ^ l.length ∈ 𝓛.endFiltration (l.length * j + 1) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx : x - b ∈ 𝓛.endFiltration (j + 1) := hl x (by simp)
    have ih' := ih (fun y hy => hl y (by simp [hy]))
    have hlb : l.prod ∈ 𝓛.endFiltration (l.length * j) := by
      have h1 := 𝓛.pow_mem_endFiltration_natMul hb l.length
      have h2 := 𝓛.endFiltration_antitone
        (show (l.length : ℤ) * j ≤ l.length * j + 1 by omega) ih'
      simpa using add_mem h2 h1
    have e : (x :: l).prod - b ^ (x :: l).length =
        (x - b) * l.prod + b * (l.prod - b ^ l.length) := by
      simp only [List.prod_cons, List.length_cons, pow_succ']
      rw [sub_mul, mul_sub]
      abel
    rw [e]
    refine add_mem ?_ ?_
    · have := 𝓛.mul_mem_endFiltration hx hlb
      convert this using 2
      simp only [List.length_cons]
      push_cast
      ring
    · have := 𝓛.mul_mem_endFiltration hb ih'
      convert this using 2
      simp only [List.length_cons]
      push_cast
      ring

/-- If `b ∈ 𝔓^j(𝓛)`, no power `b^k` lies in `𝔓^{kj+1}(𝓛)`, and every factor of the list `l`
lies in `b + 𝔓^{j+1}(𝓛)`, then the product of the `k` factors is not in `𝔓^{kj+1}(𝓛)`. -/
theorem list_prod_not_mem {j : ℤ} {b : Module.End F (ι → F)} (hb : b ∈ 𝓛.endFiltration j)
    (hpow : ∀ k : ℕ, b ^ k ∉ 𝓛.endFiltration (k * j + 1))
    (l : List (Module.End F (ι → F))) (hl : ∀ x ∈ l, x - b ∈ 𝓛.endFiltration (j + 1)) :
    l.prod ∉ 𝓛.endFiltration (l.length * j + 1) := by
  intro h
  apply hpow l.length
  simpa using sub_mem h (𝓛.list_prod_sub_pow_mem hb l hl)

end LatticeChain

end Product

/-! ### Determinants -/

section Determinant

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)

theorem ordOf_pow {c : F} (hc : c ≠ 0) (k : ℕ) : ordOf hϖ (c ^ k) = k * ordOf hϖ c := by
  induction k with
  | zero => simpa using ordOf_zpow hϖ 0
  | succ k ih =>
    rw [pow_succ, ordOf_mul hϖ (pow_ne_zero _ hc) hc, ih]
    push_cast
    ring

variable {ι : Type*}

namespace LatticeChain

variable (𝓛 : LatticeChain 𝒪[F] F (ι → F))

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Multiplication by an integral scalar preserves `𝔓^j(𝓛)`. -/
theorem integer_smul_mem_endFiltration {c : F} (hc : c ∈ 𝒪[F]) {j : ℤ}
    {Y : Module.End F (ι → F)} (hY : Y ∈ 𝓛.endFiltration j) : c • Y ∈ 𝓛.endFiltration j := by
  intro i v hv
  rw [LinearMap.smul_apply,
    show c • Y v = (⟨c, hc⟩ : 𝒪[F]) • Y v from algebraMap_smul F (⟨c, hc⟩ : 𝒪[F]) (Y v)]
  exact Submodule.smul_mem _ _ (hY i v hv)

include hϖ in
/-- Multiplication by a nonzero scalar `c` maps `𝔓^j(𝓛)` into `𝔓^{j + e ord(c)}(𝓛)`. -/
theorem smul_mem_endFiltration_ordOf {c : F} (hc : c ≠ 0) {j : ℤ} {Y : Module.End F (ι → F)}
    (hY : Y ∈ 𝓛.endFiltration j) : c • Y ∈ 𝓛.endFiltration (j + 𝓛.period * ordOf hϖ c) := by
  intro i v hv
  rw [LinearMap.smul_apply, 𝓛.smul_mem_iff hϖ hc]
  convert hY i v hv using 2
  ring

variable [Fintype ι]

omit [Fintype ι] in
/-- An element of `𝔄(𝓛) = 𝔓^0(𝓛)` has integral determinant. -/
theorem det_mem_integer_of_mem_endFiltration_zero {Y : Module.End F (ι → F)}
    (hY : Y ∈ 𝓛.endFiltration 0) : LinearMap.det Y ∈ 𝒪[F] := by
  classical
  let b := Module.finBasis 𝒪[F] (𝓛.lattice 0)
  let bF := b.extendOfIsLattice F
  have hbF : ∀ k, bF k ∈ 𝓛.lattice 0 := fun k => by
    simp only [bF, Module.Basis.extendOfIsLattice_apply]
    exact (b k).2
  have hent : ∀ k l, LinearMap.toMatrix bF bF Y k l ∈ 𝒪[F] := by
    intro k l
    rw [LinearMap.toMatrix_apply]
    exact 𝓛.repr_extendOfIsLattice_mem b (by simpa using hY 0 _ (hbF l)) k
  let M : Matrix (Fin (Module.finrank 𝒪[F] (𝓛.lattice 0)))
      (Fin (Module.finrank 𝒪[F] (𝓛.lattice 0))) 𝒪[F] := fun k l => ⟨_, hent k l⟩
  have hM : (𝒪[F].subtype).mapMatrix M = LinearMap.toMatrix bF bF Y := by
    ext k l
    rfl
  rw [← LinearMap.det_toMatrix bF, ← hM, ← RingHom.map_det]
  exact (M.det).2

include hϖ in
/-- **Determinant bound.** If `X ∈ 𝔓^a(𝓛)` and `det X ≠ 0`, then
`N a ≤ e(𝓛) ord(det X)` with `N = dim F^ι`. -/
theorem card_mul_le_period_mul_ordOf_det {a : ℤ} {X : Module.End F (ι → F)}
    (hX : X ∈ 𝓛.endFiltration a) (hdet : LinearMap.det X ≠ 0) :
    (Fintype.card ι : ℤ) * a ≤ 𝓛.period * ordOf hϖ (LinearMap.det X) := by
  have hϖ0 : (ϖ : F) ^ (-a) ≠ 0 := zpow_ne_zero _ (coe_uniformizer_ne_zero hϖ)
  have h1 := 𝓛.pow_mem_endFiltration_natMul hX 𝓛.period
  have h2 : ((ϖ : F) ^ (-a)) • X ^ 𝓛.period ∈ 𝓛.endFiltration 0 := by
    convert 𝓛.smul_mem_endFiltration_ordOf hϖ hϖ0 h1 using 2
    rw [ordOf_zpow]
    ring
  have h3 := 𝓛.det_mem_integer_of_mem_endFiltration_zero h2
  rw [LinearMap.det_smul, map_pow, Module.finrank_fintype_fun_eq_card] at h3
  have h4 := ordOf_nonneg hϖ (mul_ne_zero (pow_ne_zero _ hϖ0) (pow_ne_zero _ hdet)) h3
  rw [ordOf_mul hϖ (pow_ne_zero _ hϖ0) (pow_ne_zero _ hdet), ordOf_pow hϖ hϖ0,
    ordOf_pow hϖ hdet, ordOf_zpow] at h4
  linarith

end LatticeChain

end Determinant

/-! ### Compact sets of matrices -/

section Compact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)

include hϖ in
/-- A compact subset of `F` is bounded: `ϖ^s S ⊆ 𝔬_F` for some `s`. -/
theorem exists_pow_mul_mem_of_isCompact {S : Set F} (hS : IsCompact S) :
    ∃ s : ℕ, ∀ x ∈ S, (ϖ : F) ^ s * x ∈ 𝒪[F] := by
  have hopen : ∀ s : ℕ, IsOpen {x : F | (ϖ : F) ^ s * x ∈ 𝒪[F]} := fun s =>
    (Valuation.isOpen_integer : IsOpen (𝒪[F] : Set F)).preimage
      (continuous_const.mul continuous_id)
  have hcover : S ⊆ ⋃ s : ℕ, {x : F | (ϖ : F) ^ s * x ∈ 𝒪[F]} := by
    intro x _
    rw [Set.mem_iUnion]
    by_cases hx : x = 0
    · exact ⟨0, by simp [hx]⟩
    · refine ⟨(-ordOf hϖ x).toNat, ?_⟩
      have hp : (ϖ : F) ^ (-ordOf hϖ x).toNat ≠ 0 := pow_ne_zero _ (coe_uniformizer_ne_zero hϖ)
      show (ϖ : F) ^ (-ordOf hϖ x).toNat * x ∈ 𝒪[F]
      apply mem_integer_of_ordOf_nonneg hϖ (mul_ne_zero hp hx)
      rw [ordOf_mul hϖ hp hx, ← zpow_natCast, ordOf_zpow]
      omega
  have hmono : ∀ s t : ℕ, s ≤ t → {x : F | (ϖ : F) ^ s * x ∈ 𝒪[F]} ⊆
      {x : F | (ϖ : F) ^ t * x ∈ 𝒪[F]} := by
    intro s t hst x hx
    show (ϖ : F) ^ t * x ∈ 𝒪[F]
    rw [← Nat.sub_add_cancel hst, pow_add, mul_assoc]
    exact mul_mem (pow_mem ϖ.2 _) hx
  have hdir : Directed (· ⊆ ·) (fun s : ℕ => {x : F | (ϖ : F) ^ s * x ∈ 𝒪[F]}) :=
    fun s t => ⟨max s t, hmono _ _ (le_max_left s t), hmono _ _ (le_max_right s t)⟩
  obtain ⟨s, hs⟩ := hS.elim_directed_cover _ hopen hcover hdir
  exact ⟨s, fun x hx => hs hx⟩

variable {ι : Type*} [Fintype ι]

include hϖ in
/-- The entries of the matrices in a compact set are bounded. -/
theorem exists_pow_mul_entry_mem_of_isCompact {C : Set (Matrix ι ι F)} (hC : IsCompact C) :
    ∃ s : ℕ, ∀ M ∈ C, ∀ k l, (ϖ : F) ^ s * M k l ∈ 𝒪[F] := by
  classical
  have h : ∀ k l, ∃ s : ℕ, ∀ M ∈ C, (ϖ : F) ^ s * M k l ∈ 𝒪[F] := by
    intro k l
    obtain ⟨s, hs⟩ := exists_pow_mul_mem_of_isCompact hϖ
      (hC.image (continuous_id.matrix_elem k l))
    exact ⟨s, fun M hM => hs _ ⟨M, hM, rfl⟩⟩
  choose s hs using h
  refine ⟨∑ k, ∑ l, s k l, fun M hM k l => ?_⟩
  have hle : s k l ≤ ∑ k, ∑ l, s k l :=
    (Finset.single_le_sum (f := fun l => s k l) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ l)).trans
      (Finset.single_le_sum (f := fun k => ∑ l, s k l) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ k))
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
  exact mul_mem (pow_mem ϖ.2 _) (hs k l M hM)

namespace LatticeChain

variable (𝓛 : LatticeChain 𝒪[F] F (ι → F))

include hϖ in
/-- Every endomorphism of `F^ι` lies in some `𝔓^t(𝓛)`. -/
theorem exists_mem_endFiltration (x : Module.End F (ι → F)) :
    ∃ t : ℤ, x ∈ 𝓛.endFiltration t := by
  classical
  obtain ⟨r, β, hβ, -⟩ := exists_basis_splits_both hϖ 𝓛 𝓛
  let w : Fin r → Fin r → ℤ := fun k l =>
    |(𝓛.period : ℤ) * ordOf hϖ (entry β x k l) + 𝓛.index hϖ (β k) - 𝓛.index hϖ (β l)|
  refine ⟨-∑ k, ∑ l, w k l, ?_⟩
  rw [← sum_elementaryEnd_entry β x]
  refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun l _ => ?_
  by_cases hkl : entry β x k l = 0
  · rw [hkl, elementaryEnd_zero]
    exact zero_mem _
  · rw [𝓛.elementaryEnd_mem_iff hϖ hβ k l hkl]
    have hle : w k l ≤ ∑ k, ∑ l, w k l :=
      (Finset.single_le_sum (f := fun l => w k l) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ l)).trans
        (Finset.single_le_sum (f := fun k => ∑ l, w k l)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ k))
    have := neg_abs_le
      ((𝓛.period : ℤ) * ordOf hϖ (entry β x k l) + 𝓛.index hϖ (β k) - 𝓛.index hϖ (β l))
    simp only [w] at hle
    linarith

variable [DecidableEq ι]

include hϖ in
/-- Matrices with entries in `ϖ^{-s} 𝔬_F` all lie in one `𝔓^t(𝓛)`. -/
theorem exists_forall_toLin'_mem_endFiltration (s : ℕ) :
    ∃ t : ℤ, ∀ M : Matrix ι ι F, (∀ k l, (ϖ : F) ^ s * M k l ∈ 𝒪[F]) →
      Matrix.toLin' M ∈ 𝓛.endFiltration t := by
  classical
  have h : ∀ k l, ∃ t : ℤ, Matrix.toLin' (Matrix.single k l (1 : F)) ∈ 𝓛.endFiltration t :=
    fun k l => 𝓛.exists_mem_endFiltration hϖ _
  choose t ht using h
  refine ⟨-(∑ k, ∑ l, |t k l|) + 𝓛.period * (-(s : ℤ)), fun M hM => ?_⟩
  have hϖs : (ϖ : F) ^ (-(s : ℤ)) ≠ 0 := zpow_ne_zero _ (coe_uniformizer_ne_zero hϖ)
  rw [Matrix.matrix_eq_sum_single M, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [map_sum]
  refine Submodule.sum_mem _ fun l _ => ?_
  have heq : Matrix.toLin' (Matrix.single k l (M k l)) = (ϖ : F) ^ (-(s : ℤ)) •
      (((ϖ : F) ^ s * M k l) • Matrix.toLin' (Matrix.single k l (1 : F))) := by
    rw [smul_smul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one, ← mul_assoc, zpow_neg,
      zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ (coe_uniformizer_ne_zero hϖ)), one_mul]
  rw [heq]
  have hle : |t k l| ≤ ∑ k, ∑ l, |t k l| :=
    (Finset.single_le_sum (f := fun l => |t k l|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ l)).trans
      (Finset.single_le_sum (f := fun k => ∑ l, |t k l|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ k))
  have h1 : Matrix.toLin' (Matrix.single k l (1 : F)) ∈
      𝓛.endFiltration (-(∑ k, ∑ l, |t k l|)) :=
    𝓛.endFiltration_antitone (by linarith [neg_abs_le (t k l)]) (ht k l)
  have h2 := 𝓛.smul_mem_endFiltration_ordOf hϖ hϖs (𝓛.integer_smul_mem_endFiltration (hM k l) h1)
  rwa [ordOf_zpow] at h2

include hϖ in
/-- All matrices in a compact set lie in one `𝔓^t(𝓛)`. -/
theorem exists_forall_mem_endFiltration_of_isCompact {C : Set (Matrix ι ι F)}
    (hC : IsCompact C) : ∃ t : ℤ, ∀ M ∈ C, Matrix.toLin' M ∈ 𝓛.endFiltration t := by
  obtain ⟨s, hs⟩ := exists_pow_mul_entry_mem_of_isCompact hϖ hC
  obtain ⟨t, ht⟩ := 𝓛.exists_forall_toLin'_mem_endFiltration hϖ s
  exact ⟨t, fun M hM => ht M (hs M hM)⟩

include hϖ in
/-- **Compact sets modulo scalars.** For a compact set `C ⊆ GL(F^ι)` there is `B` such that,
for every `g ∈ C`, every `a ∈ F^×` and every `j ∈ ℤ`, if `a g ∉ 𝔓^j(𝓛)` then
`e(𝓛) ord(det(a g)) < N j + B`, where `N = dim F^ι`. -/
theorem exists_period_mul_ordOf_det_lt {C : Set (Matrix.GeneralLinearGroup ι F)}
    (hC : IsCompact C) :
    ∃ B : ℤ, ∀ g ∈ C, ∀ a : F, a ≠ 0 → ∀ j : ℤ,
      Matrix.toLin' (a • (g : Matrix ι ι F)) ∉ 𝓛.endFiltration j →
        𝓛.period * ordOf hϖ (a • (g : Matrix ι ι F)).det < Fintype.card ι * j + B := by
  obtain ⟨t, ht⟩ := 𝓛.exists_forall_mem_endFiltration_of_isCompact hϖ
    (hC.image Units.continuous_val)
  obtain ⟨t', ht'⟩ := 𝓛.exists_forall_mem_endFiltration_of_isCompact hϖ
    (hC.image Units.continuous_coe_inv)
  refine ⟨1 - Fintype.card ι * (t + t'), fun g hg a ha j hj => ?_⟩
  have hA : Matrix.toLin' (g : Matrix ι ι F) ∈ 𝓛.endFiltration t := ht _ ⟨g, hg, rfl⟩
  have hB : Matrix.toLin' ((g⁻¹ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) ∈
      𝓛.endFiltration t' := ht' _ ⟨g, hg, rfl⟩
  -- the scalar is bounded by `j`
  have ha' : 𝓛.period * ordOf hϖ a ≤ j - t - 1 := by
    by_contra hcon
    apply hj
    rw [map_smul]
    exact 𝓛.endFiltration_antitone (by omega) (𝓛.smul_mem_endFiltration_ordOf hϖ ha hA)
  -- the determinant of `g` is bounded by `t'`
  have hmul : ((g⁻¹ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).det *
      (g : Matrix ι ι F).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  have hdg : (g : Matrix ι ι F).det ≠ 0 := right_ne_zero_of_mul_eq_one hmul
  have hdg' : ((g⁻¹ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).det ≠ 0 :=
    left_ne_zero_of_mul_eq_one hmul
  have hord : ordOf hϖ ((g⁻¹ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).det =
      -ordOf hϖ (g : Matrix ι ι F).det := by
    have h := congrArg (ordOf hϖ) hmul
    rw [ordOf_mul hϖ hdg' hdg] at h
    have h1 : ordOf hϖ (1 : F) = 0 := by simpa using ordOf_zpow hϖ 0
    omega
  have hD := 𝓛.card_mul_le_period_mul_ordOf_det hϖ hB (by rwa [LinearMap.det_toLin'])
  rw [LinearMap.det_toLin', hord] at hD
  -- assemble
  rw [Matrix.det_smul, ordOf_mul hϖ (pow_ne_zero _ ha) hdg, ordOf_pow hϖ ha]
  have hN : (0 : ℤ) ≤ Fintype.card ι := by positivity
  have h5 : (Fintype.card ι : ℤ) * (𝓛.period * ordOf hϖ a) ≤ Fintype.card ι * (j - t - 1) :=
    mul_le_mul_of_nonneg_left ha' hN
  nlinarith

include hϖ in
/-- **Growth bound.** Let `C ⊆ GL(F^ι)` be compact and `j, μ ∈ ℤ`. Suppose that for every
`n ∈ ℕ` there are `g ∈ C` and `a ∈ F^×` with `a g ∉ 𝔓^{nj+1}(𝓛)` and
`ord(det(a g)) = n μ`. Then `e(𝓛) μ ≤ N j`, where `N = dim F^ι`. -/
theorem period_mul_le_of_forall_exists {C : Set (Matrix.GeneralLinearGroup ι F)}
    (hC : IsCompact C) {j μ : ℤ}
    (h : ∀ n : ℕ, ∃ g ∈ C, ∃ a : F, a ≠ 0 ∧
      Matrix.toLin' (a • (g : Matrix ι ι F)) ∉ 𝓛.endFiltration (n * j + 1) ∧
        ordOf hϖ (a • (g : Matrix ι ι F)).det = n * μ) :
    𝓛.period * μ ≤ Fintype.card ι * j := by
  obtain ⟨B, hB⟩ := 𝓛.exists_period_mul_ordOf_det_lt hϖ hC
  by_contra hcon
  have hpos : 1 ≤ 𝓛.period * μ - Fintype.card ι * j := by omega
  obtain ⟨g, hg, a, ha, hn, hdet⟩ := h (Fintype.card ι + B).toNat
  have h1 := hB g hg a ha _ hn
  rw [hdet] at h1
  have h2 : ((Fintype.card ι + B).toNat : ℤ) * (𝓛.period * μ - Fintype.card ι * j) <
      Fintype.card ι + B := by
    nlinarith
  have h3 : Fintype.card ι + B ≤ ((Fintype.card ι + B).toNat : ℤ) := Int.self_le_toNat _
  have h4 : (0 : ℤ) ≤ ((Fintype.card ι + B).toNat : ℤ) := by positivity
  nlinarith

end LatticeChain

end Compact

end Langlands.BushnellKutzko
