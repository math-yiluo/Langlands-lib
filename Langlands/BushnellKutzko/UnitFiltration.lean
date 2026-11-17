import Langlands.BushnellKutzko.LatticeChain

/-! # Unit filtration, the group `𝔎(𝔄)` and the valuation `v_𝔄` (Bushnell–Kutzko 1993, §1.1)

Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), §1.1,
printed pp. 21–22: the unit groups `U^0(𝔄) = 𝔄^×` and `U^n(𝔄) = 1 + 𝔓^n` (`n ≥ 1`), the group
`𝔎(𝔄) = {g ∈ G : g L_i ∈ 𝓛 for all i}`, the integer `v_𝔄(g)` with `g L_i = L_{i + v_𝔄(g)}`
for `g ∈ 𝔎(𝔄)`, and the valuation `v_𝔄(x) = max {n : x ∈ 𝔓^n}` of (1.1.3).
-/

noncomputable section

namespace Langlands.BushnellKutzko

universe uO uK uV

variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

namespace LatticeChain

variable (𝓛 : LatticeChain O K V)

/-! ### The unit groups `U^n(𝔄)` -/

/-- The unit group `U^n(𝔄)` (BK93 p. 21) as a subgroup of `G = Aut_K(V) = (End_K(V))ˣ`: the
units `g` with `g, g⁻¹ ∈ 𝔄(𝓛)` and `g - 1 ∈ 𝔓^n = End^n_O(𝓛)`. For `n = 0` this is
`𝔄^× = U^0(𝔄)`; for `n ≥ 1`, `coe_image_unitFiltration` shows that its image in `A` is exactly
`1 + 𝔓^n`, BK93's definition of `U^n(𝔄)`. -/
def unitFiltration (n : ℕ) : Subgroup (Module.End K V)ˣ where
  carrier := {g | (g : Module.End K V) ∈ 𝓛.order ∧
    ((g⁻¹ : (Module.End K V)ˣ) : Module.End K V) ∈ 𝓛.order ∧
    (g : Module.End K V) - 1 ∈ 𝓛.endFiltration n}
  one_mem' := by
    refine ⟨one_mem _, ?_, ?_⟩
    · simp only [inv_one, Units.val_one]
      exact one_mem 𝓛.order
    · simp
  mul_mem' := by
    rintro a b ⟨ha, ha', ha1⟩ ⟨hb, hb', hb1⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa using mul_mem ha hb
    · simpa [mul_inv_rev] using mul_mem hb' ha'
    · have h : ((a * b : (Module.End K V)ˣ) : Module.End K V) - 1 =
          (a : Module.End K V) * ((b : Module.End K V) - 1) + ((a : Module.End K V) - 1) := by
        simp only [Units.val_mul]
        noncomm_ring
      rw [h]
      refine add_mem ?_ ha1
      simpa using 𝓛.mul_mem_endFiltration (m := 0) ha hb1
  inv_mem' := by
    rintro a ⟨ha, ha', ha1⟩
    refine ⟨ha', by simpa using ha, ?_⟩
    have h : ((a⁻¹ : (Module.End K V)ˣ) : Module.End K V) - 1 =
        -(((a⁻¹ : (Module.End K V)ˣ) : Module.End K V) * ((a : Module.End K V) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one]
      noncomm_ring
    rw [h]
    exact neg_mem (by simpa using 𝓛.mul_mem_endFiltration (m := 0) ha' ha1)

theorem mem_unitFiltration {n : ℕ} {g : (Module.End K V)ˣ} :
    g ∈ 𝓛.unitFiltration n ↔ (g : Module.End K V) ∈ 𝓛.order ∧
      ((g⁻¹ : (Module.End K V)ˣ) : Module.End K V) ∈ 𝓛.order ∧
      (g : Module.End K V) - 1 ∈ 𝓛.endFiltration n :=
  Iff.rfl

/-- `U^0(𝔄)` is the unit group `𝔄^×` of `𝔄`. -/
theorem mem_unitFiltration_zero {g : (Module.End K V)ˣ} :
    g ∈ 𝓛.unitFiltration 0 ↔ (g : Module.End K V) ∈ 𝓛.order ∧
      ((g⁻¹ : (Module.End K V)ˣ) : Module.End K V) ∈ 𝓛.order := by
  refine ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, ?_⟩⟩
  have h1 := sub_mem ((𝓛.mem_order_iff_mem_endFiltration).1 h.1)
    ((𝓛.mem_order_iff_mem_endFiltration).1 (one_mem 𝓛.order))
  simpa using h1

theorem unitFiltration_antitone : Antitone 𝓛.unitFiltration := by
  intro m n hmn g hg
  exact ⟨hg.1, hg.2.1, 𝓛.endFiltration_antitone (by exact_mod_cast hmn) hg.2.2⟩

/-- Every `L_i` is an `O`-module of finite type. -/
theorem fg_lattice (i : ℤ) : (𝓛.lattice i).FG :=
  (𝓛.isLattice i).fg

include 𝓛 in
/-- A space carrying a lattice chain is finite-dimensional. -/
theorem finiteDimensional : FiniteDimensional K V := by
  obtain ⟨s, hs⟩ := 𝓛.fg_lattice 0
  refine ⟨⟨s, ?_⟩⟩
  rw [← Submodule.span_span_of_tower O K (s : Set V), hs]
  exact (𝓛.isLattice 0).span_eq_top

/-- For `n ≥ 1` and `x ∈ 𝔓^n`, the endomorphism `1 + x` maps every `L_i` onto `L_i`
(Nakayama's lemma). -/
theorem map_one_add_eq {n : ℤ} (hn : 1 ≤ n) {x : Module.End K V}
    (hx : x ∈ 𝓛.endFiltration n) (i : ℤ) :
    (𝓛.lattice i).map ((1 + x : Module.End K V).restrictScalars O) = 𝓛.lattice i := by
  set y : V →ₗ[O] V := (1 + x : Module.End K V).restrictScalars O with hy
  have hstep : ∀ j, 𝓛.lattice j ≤ (𝓛.lattice j).map y ⊔ 𝓛.lattice (j + 1) := by
    intro j v hv
    rw [Submodule.mem_sup]
    refine ⟨y v, Submodule.mem_map_of_mem hv, -(x v), neg_mem ?_, ?_⟩
    · exact 𝓛.antitone (by omega) (hx j v hv)
    · simp [hy]
  have hmapmono : ∀ j k, j ≤ k → (𝓛.lattice k).map y ≤ (𝓛.lattice j).map y :=
    fun j k hjk => Submodule.map_mono (𝓛.antitone hjk)
  have hk : ∀ k : ℕ, 𝓛.lattice i ≤ (𝓛.lattice i).map y ⊔ 𝓛.lattice (i + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      refine ih.trans (sup_le le_sup_left ((hstep (i + k)).trans (sup_le ?_ ?_)))
      · exact (hmapmono i (i + k) (by omega)).trans le_sup_left
      · exact le_sup_of_le_right (by push_cast; rw [add_assoc])
  have hle : 𝓛.lattice i ≤ (𝓛.lattice i).map y := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ring.jacobson O) (𝓛.fg_lattice i)
      (by rw [Ideal.jacobson_bot]) ?_
    rw [← 𝓛.lattice_add_period]
    exact hk 𝓛.period
  refine le_antisymm ?_ hle
  rintro _ ⟨v, hv, rfl⟩
  have h1 : (1 + x : Module.End K V) ∈ 𝓛.order :=
    add_mem (one_mem _) ((𝓛.mem_order_iff_mem_endFiltration).2
      (𝓛.endFiltration_antitone (by omega) hx))
  simpa [hy] using (𝓛.mem_order.1 h1) i v hv

/-- For `n ≥ 1` and `x ∈ 𝔓^n`, the element `1 + x` is a unit lying in `U^n(𝔄)`
(BK93 p. 21). -/
theorem exists_mem_unitFiltration {n : ℕ} (hn : 1 ≤ n) {x : Module.End K V}
    (hx : x ∈ 𝓛.endFiltration n) :
    ∃ g ∈ 𝓛.unitFiltration n, (g : Module.End K V) = 1 + x := by
  have := 𝓛.finiteDimensional
  have hmap := 𝓛.map_one_add_eq (n := n) (by exact_mod_cast hn) hx
  have hunit : IsUnit (1 + x : Module.End K V) := by
    rw [LinearMap.isUnit_iff_range_eq_top, eq_top_iff, ← (𝓛.isLattice 0).span_eq_top,
      Submodule.span_le]
    intro v hv
    rw [← hmap 0] at hv
    obtain ⟨w, -, hw⟩ := hv
    exact ⟨w, hw⟩
  refine ⟨hunit.unit, ⟨?_, ?_, ?_⟩, hunit.unit_spec⟩
  · rw [hunit.unit_spec]
    exact add_mem (one_mem _) ((𝓛.mem_order_iff_mem_endFiltration).2
      (𝓛.endFiltration_antitone (by omega) hx))
  · rw [mem_order]
    intro i v hv
    rw [← hmap i] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    have h : ((hunit.unit⁻¹ : (Module.End K V)ˣ) : Module.End K V)
        ((1 + x : Module.End K V) w) = w := by
      rw [← Module.End.mul_apply, hunit.val_inv_mul, Module.End.one_apply]
    show ((hunit.unit⁻¹ : (Module.End K V)ˣ) : Module.End K V)
      ((1 + x : Module.End K V) w) ∈ 𝓛.lattice i
    rw [h]
    exact hw
  · simpa [hunit.unit_spec] using hx

/-- For `n ≥ 1`, the image of `U^n(𝔄)` in `A = End_K(V)` is `1 + 𝔓^n` (BK93 p. 21). -/
theorem coe_image_unitFiltration {n : ℕ} (hn : 1 ≤ n) :
    ((↑) : (Module.End K V)ˣ → Module.End K V) '' (𝓛.unitFiltration n : Set (Module.End K V)ˣ) =
      {y | y - 1 ∈ 𝓛.endFiltration n} := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hg.2.2
  · intro hy
    obtain ⟨g, hg, hgy⟩ := 𝓛.exists_mem_unitFiltration hn hy
    exact ⟨g, hg, by rw [hgy]; abel⟩

/-! ### The group `𝔎(𝔄)` and the integer `v_𝔄(g)` -/

/-- If a unit `g` maps every `L_i` onto some member of the chain, then it shifts the chain by a
fixed integer: `g L_i = L_{i+d}` for all `i`. -/
theorem exists_shift {g : (Module.End K V)ˣ}
    (hg : ∀ i, ∃ j, (𝓛.lattice i).map ((g : Module.End K V).restrictScalars O) = 𝓛.lattice j) :
    ∃ d : ℤ, ∀ i,
      (𝓛.lattice i).map ((g : Module.End K V).restrictScalars O) = 𝓛.lattice (i + d) := by
  choose σ hσ using hg
  have hinj : Function.Injective ((g : Module.End K V).restrictScalars O) := by
    intro a b h
    have h' := congrArg (fun w => ((g⁻¹ : (Module.End K V)ˣ) : Module.End K V) w) h
    simpa [← Module.End.mul_apply] using h'
  have hmono : ∀ i, σ i < σ (i + 1) := by
    intro i
    have h1 : 𝓛.lattice (σ (i + 1)) < 𝓛.lattice (σ i) := by
      rw [← hσ, ← hσ]
      exact Submodule.map_strictMono_of_injective hinj (𝓛.lattice_succ_lt i)
    exact 𝓛.strictAnti.lt_iff_gt.mp h1
  have hper : ∀ i, σ (i + 𝓛.period) = σ i + 𝓛.period := by
    intro i
    apply 𝓛.injective
    rw [← hσ, 𝓛.lattice_add_period, Submodule.map_smul'', hσ, 𝓛.lattice_add_period]
  have hkey : ∀ (a : ℤ) (k : ℕ), σ a + k ≤ σ (a + k) := by
    intro a k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hmono (a + k)
      push_cast
      rw [show a + ((k : ℤ) + 1) = a + k + 1 by ring]
      omega
  have hsucc : ∀ i, σ (i + 1) = σ i + 1 := by
    intro i
    have h1 := hkey (i + 1) (𝓛.period - 1)
    have h2 := hper i
    have h3 := hmono i
    have hp := 𝓛.period_pos
    have hcast : ((𝓛.period - 1 : ℕ) : ℤ) = (𝓛.period : ℤ) - 1 := by omega
    rw [hcast, show i + 1 + ((𝓛.period : ℤ) - 1) = i + 𝓛.period by ring] at h1
    omega
  have hlin : ∀ i, σ i = σ 0 + i := by
    intro i
    induction i using Int.induction_on with
    | zero => simp
    | succ k ih => rw [hsucc, ih]; ring
    | pred k ih =>
      have := hsucc (-(k : ℤ) - 1)
      rw [show -(k : ℤ) - 1 + 1 = -k by ring, ih] at this
      omega
  exact ⟨σ 0, fun i => by rw [hσ, hlin, add_comm]⟩

/-- The group `𝔎(𝔄) = {g ∈ G : g L_i ∈ 𝓛 for all i ∈ ℤ}` of BK93 p. 21, as a subgroup of
`G = Aut_K(V)`: the units `g` such that for every `i` the image `g L_i` is some member `L_j`
of the chain. -/
def stabilizer : Subgroup (Module.End K V)ˣ where
  carrier := {g | ∀ i, ∃ j,
    (𝓛.lattice i).map ((g : Module.End K V).restrictScalars O) = 𝓛.lattice j}
  one_mem' := by
    intro i
    refine ⟨i, ?_⟩
    convert Submodule.map_id (𝓛.lattice i)
    ext v
    simp
  mul_mem' := by
    intro a b ha hb i
    obtain ⟨j, hj⟩ := hb i
    obtain ⟨k, hk⟩ := ha j
    refine ⟨k, ?_⟩
    rw [← hk, ← hj, ← Submodule.map_comp]
    rfl
  inv_mem' := by
    intro a ha i
    obtain ⟨d, hd⟩ := 𝓛.exists_shift ha
    refine ⟨i - d, ?_⟩
    rw [← (show 𝓛.lattice (i - d + d) = 𝓛.lattice i by rw [sub_add_cancel]), ← hd,
      ← Submodule.map_comp]
    convert Submodule.map_id (𝓛.lattice (i - d))
    ext v
    simp [← Module.End.mul_apply]

theorem mem_stabilizer {g : (Module.End K V)ˣ} :
    g ∈ 𝓛.stabilizer ↔ ∀ i, ∃ j,
      (𝓛.lattice i).map ((g : Module.End K V).restrictScalars O) = 𝓛.lattice j :=
  Iff.rfl

/-- The integer `v_𝔄(g)` attached to `g ∈ 𝔎(𝔄)` (BK93 pp. 21–22): the unique integer with
`g L_i = L_{i + v_𝔄(g)}` for all `i` (`map_lattice_stabilizer`, `stabilizerValuation_unique`). -/
def stabilizerValuation (g : 𝓛.stabilizer) : ℤ :=
  Classical.choose (𝓛.exists_shift g.2)

theorem map_lattice_stabilizer (g : 𝓛.stabilizer) (i : ℤ) :
    (𝓛.lattice i).map (((g : (Module.End K V)ˣ) : Module.End K V).restrictScalars O) =
      𝓛.lattice (i + 𝓛.stabilizerValuation g) :=
  Classical.choose_spec (𝓛.exists_shift g.2) i

theorem stabilizerValuation_unique (g : 𝓛.stabilizer) {d : ℤ} (i : ℤ)
    (hd : (𝓛.lattice i).map (((g : (Module.End K V)ˣ) : Module.End K V).restrictScalars O) =
      𝓛.lattice (i + d)) :
    d = 𝓛.stabilizerValuation g := by
  have h := 𝓛.injective (hd.symm.trans (𝓛.map_lattice_stabilizer g i))
  omega

/-! ### The valuation `v_𝔄` on `A` -/

open scoped Classical in
/-- The valuation `v_𝔄(x) = max {n ∈ ℤ : x ∈ 𝔓^n}` of BK93 (1.1.3), printed p. 22, with
`v_𝔄(0) = ∞`. For `x ≠ 0` it is defined as the supremum in `ℤ` of `{n : x ∈ 𝔓^n}`. The
unproved statement `RadicalFiltrationStatement` asserts that, for a lattice chain over a
nonarchimedean local field, this set is nonempty and bounded above when `x ≠ 0`, so that the
supremum is its maximum. -/
def valuation (x : Module.End K V) : WithTop ℤ :=
  if x = 0 then ⊤ else ((sSup {n : ℤ | x ∈ 𝓛.endFiltration n} : ℤ) : WithTop ℤ)

theorem valuation_zero : 𝓛.valuation 0 = ⊤ := by
  simp [valuation]

end LatticeChain

end Langlands.BushnellKutzko
