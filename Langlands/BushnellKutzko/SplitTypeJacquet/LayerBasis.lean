import Langlands.BushnellKutzko.SplittingBasis
import Langlands.BushnellKutzko.LatticeChainLayers
import Langlands.BushnellKutzko.UnitFiltration

/-! # A basis adapted to a lattice chain and to bases of its layers

Let `L` be an `𝔬_F`-lattice chain of period `e` and `b i` a basis over the residue field of
the layer `L_i / L_{i+1}` for `0 ≤ i < e`, of any rank `d i`. Lifts of these basis vectors
form an `F`-basis of the space, indexed by `Σ i, Fin (d i)`, in which the lattices `L_j`,
`0 ≤ j ≤ e`, and the filtration `End^s(L)`, `s ∈ {0, 1}`, have coordinate descriptions. -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko.SplitTypeJacquet

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (L : LatticeChain 𝒪[F] F V) {d : Fin L.period → ℕ}
  (b : ∀ i : Fin L.period, Module.Basis (Fin (d i)) 𝓀[F] (L.Layer ((i : ℕ) : ℤ)))

/-- An integral lift of a residue class. -/
def liftO (c : 𝓀[F]) : 𝒪[F] := (IsLocalRing.residue_surjective c).choose

@[simp] theorem residue_liftO (c : 𝓀[F]) : IsLocalRing.residue 𝒪[F] (liftO c) = c :=
  (IsLocalRing.residue_surjective c).choose_spec

/-- A lift to `L_i` of the `a`-th basis vector of the layer `L_i / L_{i+1}`. -/
def liftVec (p : Σ i : Fin L.period, Fin (d i)) : V :=
  (L.intervalMk_surjective _ _ (b p.1 p.2)).choose

theorem liftVec_mem (p : Σ i : Fin L.period, Fin (d i)) :
    liftVec L b p ∈ L.lattice ((p.1 : ℕ) : ℤ) :=
  (L.intervalMk_surjective _ _ (b p.1 p.2)).choose_spec.choose

theorem intervalMk_liftVec (p : Σ i : Fin L.period, Fin (d i)) :
    L.intervalMk _ _ (liftVec L b p) (liftVec_mem L b p) = b p.1 p.2 :=
  (L.intervalMk_surjective _ _ (b p.1 p.2)).choose_spec.choose_spec

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem integral_smul_mem {c : F} (hc : valuation F c ≤ 1) {i : ℤ} {x : V}
    (hx : x ∈ L.lattice i) : c • x ∈ L.lattice i := by
  have h := (L.lattice i).smul_mem (⟨c, hc⟩ : 𝒪[F]) hx
  rwa [← algebraMap_smul F (⟨c, hc⟩ : 𝒪[F]) x] at h

variable {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)

include hϖ in
/-- A coefficient in the maximal ideal moves a vector of `L_i` into `L_{i+e}`. -/
theorem maximal_smul_mem {c : F} (hc : valuation F c < 1) {i : ℤ} {x : V}
    (hx : x ∈ L.lattice i) : c • x ∈ L.lattice (i + L.period) := by
  have hc' : c = (ϖ : F) * ((ϖ : F)⁻¹ * c) := by
    rw [← mul_assoc, mul_inv_cancel₀ (coe_uniformizer_ne_zero hϖ), one_mul]
  rw [hc', mul_smul, L.uniformizer_smul_mem_iff hϖ, add_sub_cancel_right]
  have hint : valuation F ((ϖ : F)⁻¹ * c) ≤ 1 := by
    have hmem : (⟨c, (Valuation.mem_integer_iff _ _).mpr hc.le⟩ : 𝒪[F]) ∈
        IsLocalRing.maximalIdeal 𝒪[F] :=
      (valuation F).mem_maximalIdeal_iff.mpr hc
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
      Ideal.mem_span_singleton'] at hmem
    obtain ⟨y, hy⟩ := hmem
    have hcy : c = (y : F) * ϖ := by
      have := congrArg Subtype.val hy
      simpa using this.symm
    rw [hcy, mul_comm (y : F), ← mul_assoc, inv_mul_cancel₀ (coe_uniformizer_ne_zero hϖ),
      one_mul]
    exact y.2
  exact integral_smul_mem L hint hx

include hϖ in
/-- Combinations with integral coefficients, in the maximal ideal on the layers before `j`,
lie in `L_j`. -/
theorem sum_smul_liftVec_mem {j : ℕ} (hj : j ≤ L.period)
    (c : (Σ i : Fin L.period, Fin (d i)) → F) (hc : ∀ p, valuation F (c p) ≤ 1)
    (hc' : ∀ p, (p.1 : ℕ) < j → valuation F (c p) < 1) :
    ∑ p, c p • liftVec L b p ∈ L.lattice (j : ℤ) := by
  refine Submodule.sum_mem _ fun p _ => ?_
  by_cases hp : (p.1 : ℕ) < j
  · have h := maximal_smul_mem L hϖ (hc' p hp) (liftVec_mem L b p)
    exact L.antitone (by omega) h
  · exact L.antitone (by omega) (integral_smul_mem L (hc p) (liftVec_mem L b p))

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem integer_smul_eq (c : 𝒪[F]) (x : V) : c • x = (c : F) • x :=
  (algebraMap_smul F c x).symm

variable (F d) in
/-- Integral coordinate vectors with entries in the maximal ideal on the layers before `j`. -/
def coordSub (j : ℕ) : Submodule 𝒪[F] ((Σ i : Fin L.period, Fin (d i)) → 𝒪[F]) where
  carrier := {c | ∀ p : Σ i : Fin L.period, Fin (d i), (p.1 : ℕ) < j → c p ∈ 𝓂[F]}
  add_mem' ha hb p hp := Ideal.add_mem _ (ha p hp) (hb p hp)
  zero_mem' _ _ := Ideal.zero_mem _
  smul_mem' r _ hc p hp := Ideal.mul_mem_left _ r (hc p hp)

/-- The `𝔬_F`-span of the lifted vectors with the conditions of `coordSub j`. -/
def spanSub (j : ℕ) : Submodule 𝒪[F] V :=
  (coordSub F L d j).map (Fintype.linearCombination 𝒪[F] (liftVec L b))

theorem coordSub_anti {i j : ℕ} (hij : i ≤ j) : coordSub F L d j ≤ coordSub F L d i :=
  fun _ hc p hp => hc p (lt_of_lt_of_le hp hij)

theorem spanSub_anti {i j : ℕ} (hij : i ≤ j) : spanSub L b j ≤ spanSub L b i :=
  Submodule.map_mono (coordSub_anti L hij)

theorem mem_spanSub_iff (j : ℕ) (x : V) :
    x ∈ spanSub L b j ↔ ∃ c : (Σ i : Fin L.period, Fin (d i)) → F,
      (∀ p, valuation F (c p) ≤ 1) ∧ (∀ p, (p.1 : ℕ) < j → valuation F (c p) < 1) ∧
        x = ∑ p, c p • liftVec L b p := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun p => (c p : F), fun p => (c p).2, fun p hp =>
      (valuation F).mem_maximalIdeal_iff.mp (hc p hp), ?_⟩
    rw [Fintype.linearCombination_apply]
    exact Finset.sum_congr rfl fun p _ => integer_smul_eq _ _
  · rintro ⟨c, hc, hc', rfl⟩
    refine ⟨fun p => ⟨c p, hc p⟩, fun p hp => (valuation F).mem_maximalIdeal_iff.mpr (hc' p hp),
      ?_⟩
    rw [Fintype.linearCombination_apply]
    exact Finset.sum_congr rfl fun p _ => integer_smul_eq _ _

/-- Every vector of `L_j` is a lifted combination modulo `L_{j+1}`. -/
theorem lattice_le_spanSub_sup {j : ℕ} (hj : j < L.period) :
    L.lattice (j : ℤ) ≤ spanSub L b j ⊔ L.lattice ((j : ℤ) + 1) := by
  classical
  intro x hx
  let i : Fin L.period := ⟨j, hj⟩
  let q : L.Layer ((i : ℕ) : ℤ) := L.intervalMk _ _ x hx
  let r := (b i).repr q
  let z : Fin (d i) → L.lattice ((i : ℕ) : ℤ) := fun a =>
    ⟨liftVec L b ⟨i, a⟩, liftVec_mem L b ⟨i, a⟩⟩
  let ys : L.lattice ((i : ℕ) : ℤ) := ∑ a, liftO (r a) • z a
  have hQ : (L.intervalSubmodule ((i : ℕ) : ℤ) ((i : ℕ) + 1)).mkQ ys = q := by
    rw [map_sum]
    conv_rhs => rw [← (b i).sum_repr q]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [LinearMap.map_smul]
    have hz : (L.intervalSubmodule ((i : ℕ) : ℤ) ((i : ℕ) + 1)).mkQ (z a) = b i a :=
      intervalMk_liftVec L b ⟨i, a⟩
    rw [hz, ← algebraMap_smul 𝓀[F] (liftO (r a)) (b i a)]
    congr 1
    exact residue_liftO (r a)
  have hdiff : x - (ys : V) ∈ L.lattice ((j : ℤ) + 1) := by
    have h1 : (L.intervalSubmodule ((i : ℕ) : ℤ) ((i : ℕ) + 1)).mkQ ⟨x, hx⟩ =
        (L.intervalSubmodule ((i : ℕ) : ℤ) ((i : ℕ) + 1)).mkQ ys := by
      rw [hQ]; rfl
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h1
    exact h1
  let c : (Σ i : Fin L.period, Fin (d i)) → 𝒪[F] := fun p =>
    if h : p.1 = i then liftO (r (Fin.cast (congrArg d h) p.2)) else 0
  have hcS : c ∈ coordSub F L d j := by
    intro p hp
    have : p.1 ≠ i := fun h => by rw [h] at hp; exact lt_irrefl _ hp
    have hc0 : c p = 0 := by simp [c, this]
    rw [hc0]
    exact Ideal.zero_mem _
  have hys : (ys : V) = Fintype.linearCombination 𝒪[F] (liftVec L b) c := by
    rw [Fintype.linearCombination_apply, Fintype.sum_sigma, Finset.sum_eq_single i]
    · simp [ys, z, c]
    · intro k _ hk
      exact Finset.sum_eq_zero fun a _ => by simp [c, hk]
    · simp
  have hx' : x = (ys : V) + (x - (ys : V)) := by abel
  rw [hx']
  exact Submodule.add_mem_sup ⟨c, hcS, hys.symm⟩ hdiff

theorem lattice_le_spanSub_sup_period {j : ℕ} (hj : j ≤ L.period) :
    L.lattice (j : ℤ) ≤ spanSub L b j ⊔ L.lattice (L.period : ℤ) := by
  have key : ∀ k : ℕ, k ≤ L.period →
      L.lattice ((L.period - k : ℕ) : ℤ) ≤ spanSub L b (L.period - k) ⊔
        L.lattice (L.period : ℤ) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hlt : L.period - (k + 1) < L.period := by have := L.period_pos; omega
      have h1 := lattice_le_spanSub_sup L b hlt
      have heq : ((L.period - (k + 1) : ℕ) : ℤ) + 1 = ((L.period - k : ℕ) : ℤ) := by omega
      rw [heq] at h1
      refine h1.trans (sup_le le_sup_left ((ih (by omega)).trans (sup_le ?_ le_sup_right)))
      exact (spanSub_anti L b (by omega)).trans le_sup_left
  have := key (L.period - j) (by omega)
  rwa [show L.period - (L.period - j) = j by omega] at this

theorem lattice_period_eq_smul : L.lattice (L.period : ℤ) = 𝓂[F] • L.lattice 0 := by
  have h := L.lattice_add_period 0
  rw [zero_add, jacobson_integer_eq_maximalIdeal] at h
  exact h

theorem lattice_zero_le_spanSub : L.lattice 0 ≤ spanSub L b 0 := by
  have h := lattice_le_spanSub_sup_period L b (j := 0) (Nat.zero_le _)
  rw [lattice_period_eq_smul L] at h
  exact Submodule.le_of_le_smul_of_le_jacobson_bot (L.fg_lattice 0)
    (IsLocalRing.maximalIdeal_le_jacobson ⊥) h

/-- `L_j` (for `0 ≤ j ≤ e`) is spanned by the lifted vectors with the coefficient conditions
of `coordSub j`. -/
theorem lattice_le_spanSub {j : ℕ} (hj : j ≤ L.period) :
    L.lattice (j : ℤ) ≤ spanSub L b j := by
  refine (lattice_le_spanSub_sup_period L b hj).trans (sup_le le_rfl ?_)
  rw [lattice_period_eq_smul L]
  refine (Submodule.smul_mono le_rfl (lattice_zero_le_spanSub L b)).trans ?_
  rw [Submodule.smul_le]
  rintro m hm _ ⟨c, _, rfl⟩
  refine ⟨m • c, fun p _ => ?_, by rw [LinearMap.map_smul]⟩
  exact Ideal.mul_mem_right _ _ hm

include hϖ in
/-- The lifted vectors are linearly independent over `F`. -/
theorem linearIndependent_liftVec : LinearIndependent F (liftVec L b) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push Not at hne
  obtain ⟨p1, hp1⟩ := hne
  obtain ⟨p0, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun p => valuation F (g p))
    ⟨p1, Finset.mem_univ _⟩
  have hg0 : g p0 ≠ 0 := by
    intro h0
    have := hmax p1 (Finset.mem_univ _)
    rw [h0, map_zero] at this
    exact hp1 ((map_eq_zero _).mp (le_antisymm this zero_le))
  set c : (Σ i : Fin L.period, Fin (d i)) → F := fun p => g p / g p0 with hc
  have hcle : ∀ p, valuation F (c p) ≤ 1 := by
    intro p
    simp only [hc]
    rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr ((valuation F).ne_zero_iff.mpr hg0))]
    exact hmax p (Finset.mem_univ _)
  have hc0 : valuation F (c p0) = 1 := by
    simp only [hc]
    rw [div_self hg0, map_one]
  have hcsum : ∑ p, c p • liftVec L b p = 0 := by
    simp only [hc, div_eq_mul_inv, mul_comm (g _), mul_smul, ← Finset.smul_sum, hg, smul_zero]
  obtain ⟨pm, hpm, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun p => valuation F (c p) = 1) (fun p => (p.1 : ℕ))
    ⟨p0, by simp [hc0]⟩
  rw [Finset.mem_filter] at hpm
  set i0 := pm.1 with hi0
  have hlow : ∀ p : Σ i : Fin L.period, Fin (d i), (p.1 : ℕ) < i0 →
      valuation F (c p) < 1 := by
    intro p hp
    refine lt_of_le_of_ne (hcle p) fun h => ?_
    have := hmin p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    omega
  -- the layer `i0` part lies in `L_{i0+1}`
  set ys : L.lattice ((i0 : ℕ) : ℤ) := ∑ a, (⟨c ⟨i0, a⟩, hcle _⟩ : 𝒪[F]) •
    (⟨liftVec L b ⟨i0, a⟩, liftVec_mem L b ⟨i0, a⟩⟩ : L.lattice ((i0 : ℕ) : ℤ)) with hys
  have hysV : (ys : V) = ∑ a, c ⟨i0, a⟩ • liftVec L b ⟨i0, a⟩ := by
    rw [hys, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun a _ => (integer_smul_eq _ _)
  have hsum_i0 : ∑ p ∈ Finset.univ.filter (fun p : Σ i : Fin L.period, Fin (d i) => p.1 = i0),
      c p • liftVec L b p = ∑ a, c ⟨i0, a⟩ • liftVec L b ⟨i0, a⟩ := by
    rw [Finset.sum_filter, Fintype.sum_sigma, Finset.sum_eq_single i0]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  have hsplit : (ys : V) = -∑ p ∈ Finset.univ.filter
      (fun p : Σ i : Fin L.period, Fin (d i) => p.1 ≠ i0), c p • liftVec L b p := by
    rw [hysV, ← hsum_i0, eq_neg_iff_add_eq_zero, ← hcsum]
    exact Finset.sum_filter_add_sum_filter_not Finset.univ _ _
  have hmem : (ys : V) ∈ L.lattice (((i0 : ℕ) : ℤ) + 1) := by
    rw [hsplit]
    refine neg_mem (Submodule.sum_mem _ fun p hp => ?_)
    rw [Finset.mem_filter] at hp
    rcases lt_or_gt_of_ne (fun h : (p.1 : ℕ) = i0 => hp.2 (Fin.ext h)) with hlt | hgt
    · have h := maximal_smul_mem L hϖ (hlow p hlt) (liftVec_mem L b p)
      exact L.antitone (by have := i0.isLt; omega) h
    · exact L.antitone (by omega) (integral_smul_mem L (hcle p) (liftVec_mem L b p))
  have hzero : (L.intervalSubmodule ((i0 : ℕ) : ℤ) ((i0 : ℕ) + 1)).mkQ ys = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hmem
  rw [map_sum] at hzero
  have hres : ∀ a, IsLocalRing.residue 𝒪[F] (⟨c ⟨i0, a⟩, hcle _⟩ : 𝒪[F]) = 0 := by
    have hli := (b i0).linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    refine hli _ ?_
    rw [← hzero]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [LinearMap.map_smul]
    have hz : (L.intervalSubmodule ((i0 : ℕ) : ℤ) ((i0 : ℕ) + 1)).mkQ
        ⟨liftVec L b ⟨i0, a⟩, liftVec_mem L b ⟨i0, a⟩⟩ = b i0 a :=
      intervalMk_liftVec L b ⟨i0, a⟩
    rw [hz, ← algebraMap_smul 𝓀[F] _ (b i0 a)]
    rfl
  have := hres pm.2
  rw [IsLocalRing.residue_eq_zero_iff] at this
  have hv := (valuation F).mem_maximalIdeal_iff.mp this
  simp only at hv
  rw [hpm.2] at hv
  exact lt_irrefl _ hv

/-- The lifted vectors span `V` over `F`. -/
theorem span_liftVec : Submodule.span F (Set.range (liftVec L b)) = ⊤ := by
  rw [eq_top_iff, ← (L.isLattice 0).span_eq_top]
  refine Submodule.span_le.mpr fun x hx => ?_
  obtain ⟨c, -, rfl⟩ := lattice_zero_le_spanSub L b hx
  rw [Fintype.linearCombination_apply]
  refine Submodule.sum_mem _ fun p _ => ?_
  rw [integer_smul_eq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

/-- The basis of `V` formed by the lifted vectors. -/
def adaptedBasis : Module.Basis (Σ i : Fin L.period, Fin (d i)) F V :=
  Module.Basis.mk (linearIndependent_liftVec L b hϖ) (span_liftVec L b).ge

theorem adaptedBasis_apply (p : Σ i : Fin L.period, Fin (d i)) :
    adaptedBasis L b hϖ p = liftVec L b p :=
  Module.Basis.mk_apply _ _ p

theorem adaptedBasis_repr_sum (c : (Σ i : Fin L.period, Fin (d i)) → F)
    (p : Σ i : Fin L.period, Fin (d i)) :
    (adaptedBasis L b hϖ).repr (∑ q, c q • liftVec L b q) p = c p := by
  have h : ∑ q, c q • liftVec L b q = (adaptedBasis L b hϖ).equivFun.symm c := by
    rw [Module.Basis.equivFun_symm_apply]
    simp only [adaptedBasis_apply]
  rw [h, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

include hϖ in
/-- Combinations of vectors `y_q ∈ L_{q_1 + s}` with integral coefficients, in the maximal
ideal on the layers before `j`, lie in `L_{j+s}`. -/
theorem sum_smul_mem_of_coord {j : ℕ} (hj : j ≤ L.period) (s : ℤ)
    (c : (Σ i : Fin L.period, Fin (d i)) → F) (hc : ∀ p, valuation F (c p) ≤ 1)
    (hc' : ∀ p, (p.1 : ℕ) < j → valuation F (c p) < 1)
    (y : (Σ i : Fin L.period, Fin (d i)) → V)
    (hy : ∀ p, y p ∈ L.lattice (((p.1 : ℕ) : ℤ) + s)) :
    ∑ p, c p • y p ∈ L.lattice ((j : ℤ) + s) := by
  refine Submodule.sum_mem _ fun p _ => ?_
  by_cases hp : (p.1 : ℕ) < j
  · have h := maximal_smul_mem L hϖ (hc' p hp) (hy p)
    exact L.antitone (by omega) h
  · exact L.antitone (by omega) (integral_smul_mem L (hc p) (hy p))

/-- Membership in `L_j`, `0 ≤ j ≤ e`, read off from the coordinates in the adapted basis. -/
theorem mem_lattice_iff_repr {j : ℕ} (hj : j ≤ L.period) (x : V) :
    x ∈ L.lattice (j : ℤ) ↔ ∀ p, valuation F ((adaptedBasis L b hϖ).repr x p) ≤ 1 ∧
      ((p.1 : ℕ) < j → valuation F ((adaptedBasis L b hϖ).repr x p) < 1) := by
  constructor
  · intro hx
    obtain ⟨c, hc, hc', rfl⟩ := (mem_spanSub_iff L b j x).mp (lattice_le_spanSub L b hj hx)
    intro p
    rw [adaptedBasis_repr_sum]
    exact ⟨hc p, hc' p⟩
  · intro h
    have hx := (adaptedBasis L b hϖ).sum_repr x
    simp only [adaptedBasis_apply] at hx
    rw [← hx]
    exact sum_smul_liftVec_mem L b hϖ hj _ (fun p => (h p).1) (fun p => (h p).2)

include hϖ in
/-- A test of `End^n(L)` on the lattices `L_j`, `0 ≤ j < e`, of one period. -/
theorem mem_endFiltration_of_lt_period {x : Module.End F V} {n : ℤ}
    (hx : ∀ j : ℕ, j < L.period → ∀ v ∈ L.lattice (j : ℤ), x v ∈ L.lattice ((j : ℤ) + n)) :
    x ∈ L.endFiltration n := by
  intro i v hv
  have hepos : (0 : ℤ) < L.period := by have := L.period_pos; omega
  have hj0 : 0 ≤ i % (L.period : ℤ) := Int.emod_nonneg _ hepos.ne'
  have hje : i % (L.period : ℤ) < L.period := Int.emod_lt_of_pos _ hepos
  have hij : i % (L.period : ℤ) + L.period * (i / (L.period : ℤ)) = i := Int.emod_add_mul_ediv i _
  have hv' : (ϖ : F) ^ (-(i / (L.period : ℤ))) • v ∈
      L.lattice (((i % (L.period : ℤ)).toNat : ℕ) : ℤ) := by
    rw [L.zpow_smul_mem_iff hϖ, Int.toNat_of_nonneg hj0]
    convert hv using 2
    linarith
  have h := hx (i % (L.period : ℤ)).toNat (by omega) _ hv'
  rw [map_smul, L.zpow_smul_mem_iff hϖ, Int.toNat_of_nonneg hj0] at h
  convert h using 2
  linarith

/-- The endomorphism with matrix `M` in the adapted basis lies in `End^s(L)`, `s ∈ {0, 1}`,
exactly when the entries of `M` are integral and lie in the maximal ideal at the positions
`(p, q)` with `p_1 < q_1 + s`. -/
theorem toLin_mem_endFiltration_iff {s : ℕ} (hs : s ≤ 1)
    (M : Matrix (Σ i : Fin L.period, Fin (d i)) (Σ i : Fin L.period, Fin (d i)) F) :
    Matrix.toLin (adaptedBasis L b hϖ) (adaptedBasis L b hϖ) M ∈ L.endFiltration (s : ℤ) ↔
      ∀ p q, valuation F (M p q) ≤ 1 ∧
        ((p.1 : ℕ) < (q.1 : ℕ) + s → valuation F (M p q) < 1) := by
  set β := adaptedBasis L b hϖ
  have hcol : ∀ q, Matrix.toLin β β M (β q) = ∑ p, M p q • liftVec L b p := by
    intro q
    rw [Matrix.toLin_self]
    simp only [β, adaptedBasis_apply]
  constructor
  · intro hM p q
    have hq : β q ∈ L.lattice (((q.1 : ℕ) : ℤ)) := by
      rw [adaptedBasis_apply]; exact liftVec_mem L b q
    have h := hM _ _ hq
    rw [hcol, show (((q.1 : ℕ) : ℤ) + (s : ℤ)) = (((q.1 : ℕ) + s : ℕ) : ℤ) by push_cast; ring,
      mem_lattice_iff_repr L b hϖ (by have := q.1.isLt; omega)] at h
    have h' := h p
    rw [adaptedBasis_repr_sum] at h'
    exact h'
  · intro hM
    refine mem_endFiltration_of_lt_period L hϖ fun j hj v hv => ?_
    have hv' := (mem_lattice_iff_repr L b hϖ hj.le v).mp hv
    rw [← β.sum_repr v, map_sum]
    simp only [map_smul]
    refine sum_smul_mem_of_coord L hϖ hj.le (s : ℤ) _ (fun p => (hv' p).1)
      (fun p => (hv' p).2) _ fun q => ?_
    rw [hcol, show (((q.1 : ℕ) : ℤ) + (s : ℤ)) = (((q.1 : ℕ) + s : ℕ) : ℤ) by push_cast; ring]
    exact sum_smul_liftVec_mem L b hϖ (by have := q.1.isLt; omega) _ (fun p => (hM p q).1)
      (fun p hp => (hM p q).2 hp)

end Langlands.BushnellKutzko.SplitTypeJacquet
