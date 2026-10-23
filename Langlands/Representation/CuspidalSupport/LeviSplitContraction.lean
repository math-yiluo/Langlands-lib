import Langlands.Representation.CuspidalSupport.JacquetVanishingSubgroups
import Langlands.Representation.Geometric.RefinementDefinitions
import Langlands.Representation.Whittaker.Iwasawa

/-!
# Splitting one block of a product Levi and contracting its unipotent radical

Auxiliary block shapes, the refinement of a product Levi that splits a single block,
and the contraction of the corresponding unipotent radical by antitone diagonal
torus elements with a deep gap at the split point.
-/

noncomputable section

open Filter Topology

namespace Langlands.CuspidalSupport.LeviAdmissibility

open GeneralLinear Geometric

universe uF

/-! ### Auxiliary block shapes -/

section Shapes

/-- The block shape of rank `m` with a single block. -/
def oneBlock (m : ℕ) (hm : 0 < m) : BlockShape m where
  length := 1
  size := fun _ => m
  positive := fun _ => hm
  sum_eq := by simp

/-- The block shape of rank `m` with blocks of sizes `a + 1` and `m - (a + 1)`. -/
def twoBlock (m a : ℕ) (ha : a + 1 < m) : BlockShape m where
  length := 2
  size := ![a + 1, m - (a + 1)]
  positive := by
    intro i
    fin_cases i <;> simp
    omega
  sum_eq := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega

/-- The standard numbering of the coordinates of a block. -/
theorem index_val {n : ℕ} (B : BlockShape n) (i : Fin B.length) (b : Fin (B.size i)) :
    ((B.index i b : Fin n) : ℕ) = ∑ k : Fin i, B.size (Fin.castLE i.2.le k) + b := by
  simp only [BlockShape.index, BlockShape.indexEquiv, Function.Embedding.coeFn_mk,
    Equiv.trans_apply, finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply]

theorem twoBlock_index_fst {m a : ℕ} (ha : a + 1 < m) (p : Fin m) (hp : p.val ≤ a) :
    (twoBlock m a ha).index ⟨0, by simp [twoBlock]⟩ ⟨p, by simp [twoBlock]; omega⟩ = p :=
  Fin.ext (by simp [index_val])

theorem twoBlock_index_snd {m a : ℕ} (ha : a + 1 < m) (p : Fin m) (hp : a < p.val) :
    (twoBlock m a ha).index ⟨1, by simp [twoBlock]⟩
      ⟨p - (a + 1), by simp [twoBlock]; omega⟩ = p := by
  apply Fin.ext
  rw [index_val]
  simp [twoBlock]
  omega

variable {R : Type*} [CommRing R]

/-- A matrix whose entries agree with the identity outside the upper right block
of the split after the first `a + 1` coordinates. -/
def SplitUnipotent (m a : ℕ) (u : Matrix (Fin m) (Fin m) R) : Prop :=
  ∀ p q : Fin m, ¬ (p.val ≤ a ∧ a < q.val) →
    u p q = (1 : Matrix (Fin m) (Fin m) R) p q

/-- The unipotent radical of the one-block shape is trivial. -/
theorem eq_one_of_mem_oneBlock_unipotent {m : ℕ} (hm : 0 < m)
    {g : GeneralLinear m R} (hg : g ∈ (oneBlock m hm).unipotentSubgroup R) : g = 1 := by
  have hd := (((oneBlock m hm).mem_unipotentSubgroup_iff R g).mp hg).2 ⟨0, Nat.one_pos⟩
  have hidx : ∀ p : Fin m, (oneBlock m hm).index ⟨0, Nat.one_pos⟩ ⟨p, p.2⟩ = p := fun p =>
    Fin.ext (by simp [index_val])
  apply Matrix.GeneralLinearGroup.ext
  intro p q
  have h := hd ⟨p, p.2⟩ ⟨q, q.2⟩
  rw [hidx p, hidx q] at h
  rw [h, Units.val_one, Matrix.one_apply]
  simp [Fin.ext_iff]

/-- The unipotent radical of the two-block shape is split unipotent. -/
theorem splitUnipotent_of_mem_twoBlock {m a : ℕ} (ha : a + 1 < m) {g : GeneralLinear m R}
    (hg : g ∈ (twoBlock m a ha).unipotentSubgroup R) : SplitUnipotent m a g.val := by
  obtain ⟨hpar, hdiag⟩ := ((twoBlock m a ha).mem_unipotentSubgroup_iff R g).mp hg
  rw [BlockShape.mem_parabolic_iff] at hpar
  intro p q hpq
  rcases le_or_gt p.val a with hp | hp <;> rcases le_or_gt q.val a with hq | hq
  · have h := hdiag ⟨0, by simp [twoBlock]⟩ ⟨p, by simp [twoBlock]; omega⟩
      ⟨q, by simp [twoBlock]; omega⟩
    rw [twoBlock_index_fst ha p hp, twoBlock_index_fst ha q hq] at h
    rw [h, Matrix.one_apply]
    simp [Fin.ext_iff]
  · exact absurd ⟨hp, hq⟩ hpq
  · have h := hpar ⟨1, by simp [twoBlock]⟩ ⟨0, by simp [twoBlock]⟩
      ⟨p - (a + 1), by simp [twoBlock]; omega⟩ ⟨q, by simp [twoBlock]; omega⟩
      (by simp [Fin.lt_def])
    rw [twoBlock_index_snd ha p hp, twoBlock_index_fst ha q hq] at h
    rw [h, Matrix.one_apply_ne (by rintro rfl; omega)]
  · have h := hdiag ⟨1, by simp [twoBlock]⟩ ⟨p - (a + 1), by simp [twoBlock]; omega⟩
      ⟨q - (a + 1), by simp [twoBlock]; omega⟩
    rw [twoBlock_index_snd ha p hp, twoBlock_index_snd ha q hq] at h
    rw [h, Matrix.one_apply]
    simp only [Fin.ext_iff]
    split_ifs <;> first | rfl | omega

end Shapes

/-! ### Refinements splitting one block -/

section Split

variable {n : ℕ} (B : BlockShape n)

/-- The block refinement that splits block `i` after its first `a + 1` coordinates
and leaves every other block whole. -/
def splitRefinement (i : Fin B.length) (a : ℕ) (ha : a + 1 < B.size i) :
    BlockRefinement B :=
  Function.update (fun j => oneBlock (B.size j) (B.positive j)) i (twoBlock (B.size i) a ha)

variable {B}

theorem splitRefinement_self (i : Fin B.length) (a : ℕ) (ha : a + 1 < B.size i) :
    splitRefinement B i a ha i = twoBlock (B.size i) a ha :=
  Function.update_self ..

theorem splitRefinement_of_ne {i j : Fin B.length} (hj : j ≠ i) (a : ℕ)
    (ha : a + 1 < B.size i) :
    splitRefinement B i a ha j = oneBlock (B.size j) (B.positive j) :=
  Function.update_of_ne hj ..

/-- Splitting a block gives a proper refined parabolic. -/
theorem splitRefinement_parabolic_ne_top {K : Type uF} [Field K]
    (i : Fin B.length) (a : ℕ) (ha : a + 1 < B.size i) :
    refinedParabolic K B (splitRefinement B i a ha) ≠ ⊤ := by
  intro htop
  have h2 : (twoBlock (B.size i) a ha).parabolic K = ⊤ := by
    rw [eq_top_iff]
    intro h _
    have hm : (Pi.mulSingle i h : B.Levi K) ∈ refinedParabolic K B (splitRefinement B i a ha) := by
      rw [htop]
      exact Subgroup.mem_top _
    have := (mem_refinedParabolic K B _ _).mp hm i
    rwa [Pi.mulSingle_eq_same, splitRefinement_self] at this
  have hs := block_indices_subsingleton_of_parabolic_eq_top _ h2
  have := hs.elim (⟨0, by simp [twoBlock]⟩ : Fin (twoBlock (B.size i) a ha).length)
    ⟨1, by simp [twoBlock]⟩
  simp [Fin.ext_iff] at this

/-- Elements of the split unipotent radical are trivial outside block `i` and split
unipotent in block `i`. -/
theorem mem_splitRefinement_unipotent {R : Type*} [CommRing R] {i : Fin B.length} {a : ℕ}
    {ha : a + 1 < B.size i} {u : B.Levi R}
    (hu : u ∈ refinedUnipotent R B (splitRefinement B i a ha)) :
    (∀ j, j ≠ i → u j = 1) ∧ SplitUnipotent (B.size i) a (u i).val := by
  rw [mem_refinedUnipotent] at hu
  refine ⟨fun j hj => ?_, ?_⟩
  · have := hu j
    rw [splitRefinement_of_ne hj] at this
    exact eq_one_of_mem_oneBlock_unipotent _ this
  · have := hu i
    rw [splitRefinement_self] at this
    exact splitUnipotent_of_mem_twoBlock ha this

end Split

/-! ### Contraction of a split unipotent radical by deep torus elements -/

section Contraction

variable {K : Type uF} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsValuativeTopology K]

/-- Integral powers of a uniformizing element tend to zero. -/
theorem tendsto_zpow_uniformizer {ϖ : Kˣ}
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation K) ϖ) :
    Tendsto (fun z : ℤ => ((ϖ ^ z : Kˣ) : K)) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero K).tendsto_right_iff]
  intro γ _
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (γ : ValuativeRel.ValueGroupWithZero K)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact γ.ne_zero hy.symm
  obtain ⟨k, hk⟩ := hϖ.2 y hy0
  have hpos : 0 < ValuativeRel.valuation K (ϖ : K) :=
    zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr ϖ.ne_zero)
  filter_upwards [eventually_gt_atTop k] with z hz
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
  rw [← hy, hk]
  exact zpow_lt_zpow_right_of_lt_one₀ hpos hϖ.1 hz

omit [ValuativeRel K] [TopologicalSpace K] [IsValuativeTopology K] in
/-- The entries of a matrix are unchanged by conjugation by `diag(ϖ ^ lam)`,
up to the factor `ϖ ^ (lam p - lam q)`. -/
theorem torus_conj_apply {m : ℕ} (ϖ : Kˣ) (lam : Fin m → ℤ)
    (g : Matrix.GeneralLinearGroup (Fin m) K) (p q : Fin m) :
    ((Iwasawa.torus ϖ lam * g * (Iwasawa.torus ϖ lam)⁻¹ :
      Matrix.GeneralLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) p q =
      ((ϖ ^ (lam p - lam q) : Kˣ) : K) * g p q := by
  rw [Units.val_mul, Units.val_mul, Iwasawa.torus_val, Iwasawa.torus_inv_val,
    Matrix.mul_diagonal, Matrix.diagonal_mul, zpow_sub, Units.val_mul]
  ring

/-- Antitone exponent vectors whose gap at the split point tends to infinity. -/
def gapFilter (m a : ℕ) (ha : a + 1 < m) : Filter (Fin m → ℤ) :=
  comap (fun lam => lam ⟨a, by omega⟩ - lam ⟨a + 1, ha⟩) atTop ⊓
    𝓟 {lam | Antitone lam}

theorem tendsto_torus_conj_val {m a : ℕ} (ha : a + 1 < m) {ϖ : Kˣ}
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation K) ϖ)
    {u : Matrix.GeneralLinearGroup (Fin m) K} (hu : SplitUnipotent m a u.val) :
    Tendsto (fun lam => ((Iwasawa.torus ϖ lam * u * (Iwasawa.torus ϖ lam)⁻¹ :
      Matrix.GeneralLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K))
      (gapFilter m a ha) (𝓝 1) := by
  apply tendsto_pi_nhds.mpr
  intro p
  apply tendsto_pi_nhds.mpr
  intro q
  simp only [torus_conj_apply]
  by_cases hpq : p.val ≤ a ∧ a < q.val
  · have hne : p ≠ q := by
      intro h
      rw [h] at hpq
      omega
    rw [Matrix.one_apply_ne hne]
    have hgap : Tendsto (fun lam : Fin m → ℤ => lam ⟨a, by omega⟩ - lam ⟨a + 1, ha⟩)
        (gapFilter m a ha) atTop :=
      tendsto_comap.mono_left inf_le_left
    have hdiff : Tendsto (fun lam : Fin m → ℤ => lam p - lam q) (gapFilter m a ha) atTop := by
      apply tendsto_atTop_mono' _ _ hgap
      filter_upwards [mem_inf_of_right (mem_principal_self {lam : Fin m → ℤ | Antitone lam})]
        with lam hlam
      have h1 : lam ⟨a, by omega⟩ ≤ lam p := hlam (show p ≤ ⟨a, by omega⟩ from hpq.1)
      have h2 : lam q ≤ lam ⟨a + 1, ha⟩ :=
        hlam (show (⟨a + 1, ha⟩ : Fin m) ≤ q from Nat.succ_le_of_lt hpq.2)
      omega
    simpa using ((tendsto_zpow_uniformizer hϖ).comp hdiff).mul_const (u.val p q)
  · rw [hu p q hpq]
    by_cases he : p = q
    · subst he
      simp only [sub_self, zpow_zero, Units.val_one, one_mul]
      exact tendsto_const_nhds
    · simp only [Matrix.one_apply_ne he, mul_zero]
      exact tendsto_const_nhds

omit [ValuativeRel K] [IsValuativeTopology K] in
/-- A filter limit in `GL_m` may be checked on the matrix and its inverse. -/
theorem tendsto_units_one {m : ℕ} {X : Type*} {l : Filter X}
    {f : X → Matrix.GeneralLinearGroup (Fin m) K}
    (h₁ : Tendsto (fun x => ((f x : Matrix.GeneralLinearGroup (Fin m) K) :
      Matrix (Fin m) (Fin m) K)) l (𝓝 1))
    (h₂ : Tendsto (fun x => (((f x)⁻¹ : Matrix.GeneralLinearGroup (Fin m) K) :
      Matrix (Fin m) (Fin m) K)) l (𝓝 1)) :
    Tendsto f l (𝓝 1) := by
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff, map_one]
  exact h₁.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp h₂)

/-- Conjugation by antitone torus elements with a deep gap at the split point
moves a split unipotent matrix into any neighbourhood of the identity. -/
theorem torus_conj_eventually_mem {m a : ℕ} (ha : a + 1 < m) {ϖ : Kˣ}
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation K) ϖ)
    {u : Matrix.GeneralLinearGroup (Fin m) K} (hu : SplitUnipotent m a u.val)
    (hu' : SplitUnipotent m a (u⁻¹ : Matrix.GeneralLinearGroup (Fin m) K).val)
    {O : Set (Matrix.GeneralLinearGroup (Fin m) K)} (hO : O ∈ 𝓝 1) :
    ∃ N : ℤ, ∀ lam : Fin m → ℤ, Antitone lam →
      N ≤ lam ⟨a, by omega⟩ - lam ⟨a + 1, ha⟩ →
      Iwasawa.torus ϖ lam * u * (Iwasawa.torus ϖ lam)⁻¹ ∈ O := by
  have ht : Tendsto (fun lam => Iwasawa.torus ϖ lam * u * (Iwasawa.torus ϖ lam)⁻¹)
      (gapFilter m a ha) (𝓝 1) := by
    apply tendsto_units_one (tendsto_torus_conj_val ha hϖ hu)
    have h := tendsto_torus_conj_val ha hϖ hu'
    refine h.congr fun lam => ?_
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  have hev : ∀ᶠ lam in gapFilter m a ha,
      Iwasawa.torus ϖ lam * u * (Iwasawa.torus ϖ lam)⁻¹ ∈ O := ht hO
  rw [gapFilter, eventually_inf_principal, eventually_comap, eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  exact ⟨N, fun lam hlam hgap => hN _ hgap lam rfl hlam⟩

end Contraction

/-! ### Block diagonal torus elements -/

section LeviTorus

variable {K : Type uF} [Field K] {n : ℕ} (B : BlockShape n)

/-- The block diagonal torus element `(diag(ϖ ^ lam j))_j`. -/
def leviTorus (ϖ : Kˣ) (lam : ∀ j : Fin B.length, Fin (B.size j) → ℤ) : B.Levi K :=
  fun j => Iwasawa.torus ϖ (lam j)

/-- Conjugating an element supported in block `i` by a block torus element. -/
theorem leviTorus_conj_of_eq_one (ϖ : Kˣ) (lam : ∀ j : Fin B.length, Fin (B.size j) → ℤ)
    {i : Fin B.length} {u : B.Levi K} (hu : ∀ j, j ≠ i → u j = 1) :
    leviTorus B ϖ lam * u * (leviTorus B ϖ lam)⁻¹ =
      Pi.mulSingle i (Iwasawa.torus ϖ (lam i) * u i * (Iwasawa.torus ϖ (lam i))⁻¹) := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Pi.mulSingle_eq_same]
    rfl
  · rw [Pi.mulSingle_eq_of_ne hj]
    change Iwasawa.torus ϖ (lam j) * u j * (Iwasawa.torus ϖ (lam j))⁻¹ = 1
    rw [hu j hj, mul_one, mul_inv_cancel]

/-- Adding a constant to each block of exponents multiplies by a block scalar. -/
theorem leviTorus_add_const (ϖ : Kˣ) (μ : ∀ j : Fin B.length, Fin (B.size j) → ℤ)
    (c : Fin B.length → ℤ) :
    leviTorus B ϖ (fun j b => μ j b + c j) =
      leviTorus B ϖ μ * leviTorus B ϖ (fun j _ => c j) := by
  funext j
  apply Units.ext
  change (Iwasawa.torus ϖ fun b => μ j b + c j).val =
    (Iwasawa.torus ϖ (μ j)).val * (Iwasawa.torus ϖ fun _ => c j).val
  rw [Iwasawa.torus_val, Iwasawa.torus_val, Iwasawa.torus_val, Matrix.diagonal_mul_diagonal]
  congr 1
  funext b
  rw [zpow_add, Units.val_mul]

/-- Block scalars are central in the Levi. -/
theorem leviTorus_const_comm (ϖ : Kˣ) (c : Fin B.length → ℤ) (g : B.Levi K) :
    g * leviTorus B ϖ (fun j _ => c j) = leviTorus B ϖ (fun j _ => c j) * g := by
  funext j
  apply Units.ext
  change (g j).val * (Iwasawa.torus ϖ fun _ => c j).val =
    (Iwasawa.torus ϖ fun _ => c j).val * (g j).val
  rw [Iwasawa.torus_val]
  ext p q
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

end LeviTorus

end Langlands.CuspidalSupport.LeviAdmissibility
