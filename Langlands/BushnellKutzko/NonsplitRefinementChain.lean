import Langlands.BushnellKutzko.MoyReduction
import Langlands.BushnellKutzko.CriticalDerivedCyclicRows

/-! # Refining a lattice chain by the images of a residually nilpotent element

Let `𝓛 = (L_i)` be an `𝔬_F`-lattice chain in `V` and let `z ∈ 𝔄(𝓛)` with `z^m ∈ 𝔓(𝓛)`. The
lattices `z^t L_i + L_{i+1}` (`imageLattice`) are the lattices of a lattice chain containing every
`L_i` (`exists_imageChain`). `exists_refinement` describes this chain relative to a unit that
commutes with `z` and shifts `𝓛`.
-/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko.NonsplitRefinement

open CriticalDerived

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
variable {V : Type v} [AddCommGroup V] [Module F V]

/-! ### Lattice chains from totally ordered sets of lattices -/

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The pointwise action of a unit of `F` on submodules is monotone. -/
theorem units_smul_mono (u : Fˣ) {A B : Submodule 𝒪[F] V} (h : A ≤ B) :
    u • A ≤ u • B := by
  rw [Units.smul_def, Units.smul_def]
  exact Submodule.map_mono h

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The pointwise action of a unit of `F` on submodules reflects inclusion. -/
theorem units_smul_le_units_smul_iff (u : Fˣ) {A B : Submodule 𝒪[F] V} :
    u • A ≤ u • B ↔ A ≤ B := by
  refine ⟨fun h => ?_, units_smul_mono u⟩
  have h' := units_smul_mono u⁻¹ h
  rwa [inv_smul_smul, inv_smul_smul] at h'

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The pointwise action of a unit of `F` on submodules reflects strict inclusion. -/
theorem units_smul_lt_units_smul_iff (u : Fˣ) {A B : Submodule 𝒪[F] V} :
    u • A < u • B ↔ A < B := by
  simp only [lt_iff_le_not_ge, units_smul_le_units_smul_iff]

/-- `ϖ L = 𝔭 L` for the pointwise action of the unit `ϖ` of `F`. -/
theorem uniformizerAsUnit_smul_eq (L : Submodule 𝒪[F] V) :
    LatticeChain.uniformizerAsUnit hϖ • L = Ring.jacobson 𝒪[F] • L := by
  rw [jacobson_integer_eq_maximalIdeal, hϖ.maximalIdeal_eq, Submodule.ideal_span_singleton_smul]
  ext v
  simp only [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, (algebraMap_smul F ϖ b).symm⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, algebraMap_smul F ϖ b⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The pointwise action of a unit of `F` on submodules is the image under the scalar
endomorphism. -/
theorem units_smul_eq_map (u : Fˣ) (L : Submodule 𝒪[F] V) :
    u • L = L.map ((scalarEndUnit (V := V) u : Module.End F V).restrictScalars 𝒪[F]) := by
  rw [Units.smul_def, Submodule.pointwise_smul_def]
  congr 1

include hϖ in
/-- A nonempty totally ordered set of lattices in `V`, stable under all powers of `ϖ`, on which
`ϖ` acts strictly decreasingly, and with finite intervals, is the set of lattices of a lattice
chain. -/
theorem exists_latticeChain_range_eq (C : Set (Submodule 𝒪[F] V))
    (hlat : ∀ L ∈ C, L.IsLattice F)
    (hchain : IsChain (· ≤ ·) C) (hne : C.Nonempty)
    (hsmul : ∀ L ∈ C, ∀ k : ℤ, LatticeChain.uniformizerAsUnit hϖ ^ k • L ∈ C)
    (hlt : ∀ L ∈ C, LatticeChain.uniformizerAsUnit hϖ • L < L)
    (hfin : ∀ L ∈ C, ∀ L' ∈ C, {M | M ∈ C ∧ L' ≤ M ∧ M ≤ L}.Finite) :
    ∃ 𝓜 : LatticeChain 𝒪[F] F V, Set.range 𝓜.lattice = C := by
  set ϖu := LatticeChain.uniformizerAsUnit hϖ with hϖu
  have hsmul1 : ∀ L ∈ C, ϖu • L ∈ C := fun L hL => by
    simpa using hsmul L hL 1
  have hsmulinv : ∀ L ∈ C, ϖu⁻¹ • L ∈ C := fun L hL => by
    simpa using hsmul L hL (-1)
  let s : Set (Submodule 𝒪[F] V)ᵒᵈ := OrderDual.ofDual ⁻¹' C
  have hs : IsChain (· ≤ ·) s := by
    intro a ha b hb hab
    rcases hchain ha hb hab with h | h
    · exact Or.inr h
    · exact Or.inl h
  obtain ⟨f, hf, hrange⟩ := exists_strictMono_int_range_eq hs
    (by obtain ⟨L, hL⟩ := hne; exact ⟨OrderDual.toDual L, hL⟩)
    (fun a ha => ⟨OrderDual.toDual (ϖu • OrderDual.ofDual a), hsmul1 _ ha, hlt _ ha⟩)
    (fun a ha => by
      refine ⟨OrderDual.toDual (ϖu⁻¹ • OrderDual.ofDual a), hsmulinv _ ha, ?_⟩
      have h : ϖu • (ϖu⁻¹ • OrderDual.ofDual a) < ϖu⁻¹ • OrderDual.ofDual a :=
        hlt _ (hsmulinv _ ha)
      rw [smul_inv_smul] at h
      exact h)
    (fun a ha b hb => by
      have h := (hfin (OrderDual.ofDual a) ha (OrderDual.ofDual b) hb).image OrderDual.toDual
      refine h.subset ?_
      intro c hc
      exact ⟨OrderDual.ofDual c, ⟨hc.1, hc.2.2, hc.2.1⟩, rfl⟩)
  have hmemC : ∀ t, OrderDual.ofDual (f t) ∈ C := fun t => by
    have : f t ∈ s := hrange ▸ Set.mem_range_self t
    exact this
  have hrangeC : ∀ L ∈ C, ∃ t, OrderDual.ofDual (f t) = L := by
    intro L hL
    have : OrderDual.toDual L ∈ Set.range f := hrange ▸ hL
    obtain ⟨t, ht⟩ := this
    exact ⟨t, by rw [ht]; rfl⟩
  obtain ⟨c, hc⟩ := exists_shift_of_strictMono hf
    (fun a => OrderDual.toDual (ϖu • OrderDual.ofDual a))
    (fun t => by
      obtain ⟨u, hu⟩ := hrangeC _ (hsmul1 _ (hmemC t))
      exact ⟨u, hu⟩)
    (fun t u htu => by
      have h : OrderDual.ofDual (f u) < OrderDual.ofDual (f t) := hf htu
      show ϖu • OrderDual.ofDual (f u) < ϖu • OrderDual.ofDual (f t)
      exact (units_smul_lt_units_smul_iff ϖu).2 h)
    (fun u => by
      obtain ⟨t, ht⟩ := hrangeC _ (hsmulinv _ (hmemC u))
      refine ⟨t, ?_⟩
      show OrderDual.toDual (ϖu • OrderDual.ofDual (f t)) = f u
      rw [ht, smul_inv_smul]
      rfl)
  have hcpos : 0 < c := by
    have h1 : f 0 < f (0 + c) := by
      rw [hc 0]
      exact hlt _ (hmemC 0)
    have := hf.lt_iff_lt.mp h1
    omega
  refine ⟨{ lattice := fun t => OrderDual.ofDual (f t)
            isLattice := fun t => hlat _ (hmemC t)
            lattice_succ_lt := fun t => hf (lt_add_one t)
            exists_period := ⟨c.toNat, by omega, fun t => ?_⟩ }, ?_⟩
  · rw [Int.toNat_of_nonneg hcpos.le, hc t]
    exact uniformizerAsUnit_smul_eq hϖ _
  · ext L
    constructor
    · rintro ⟨t, rfl⟩
      exact hmemC t
    · intro hL
      exact hrangeC L hL

/-! ### Shifting units -/

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A unit mapping each lattice onto the lattice `d` steps further shifts the chain by `d`. -/
theorem shifts_of_map_eq (C : LatticeChain 𝒪[F] F V) {g : (Module.End F V)ˣ} {d : ℤ}
    (h : ∀ t, (C.lattice t).map ((g : Module.End F V).restrictScalars 𝒪[F]) =
      C.lattice (t + d)) : Shifts C d g := by
  have hs : g ∈ C.stabilizer := fun t => ⟨t + d, h t⟩
  have h1 := Shifts.of_stabilizer (𝓛 := C) ⟨g, hs⟩
  rwa [← C.stabilizerValuation_unique ⟨g, hs⟩ 0 (h 0)] at h1

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The image under a product is the iterated image. -/
theorem map_restrictScalars_mul (N : Submodule 𝒪[F] V) (a c : Module.End F V) :
    N.map ((a * c).restrictScalars 𝒪[F]) =
      (N.map (c.restrictScalars 𝒪[F])).map (a.restrictScalars 𝒪[F]) := by
  rw [← Submodule.map_comp]
  rfl

/-! ### The image lattices -/

variable (𝓛 : LatticeChain 𝒪[F] F V)

/-- The lattice `z^t L_i + L_{i+1}`. -/
def imageLattice (z : Module.End F V) (i : ℤ) (t : ℕ) : Submodule 𝒪[F] V :=
  (𝓛.lattice i).map ((z ^ t).restrictScalars 𝒪[F]) ⊔ 𝓛.lattice (i + 1)

variable {𝓛} {z : Module.End F V}

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `L_{i+1} ⊆ z^t L_i + L_{i+1}`. -/
theorem lattice_succ_le_imageLattice (i : ℤ) (t : ℕ) :
    𝓛.lattice (i + 1) ≤ imageLattice 𝓛 z i t :=
  le_sup_right

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Powers of an element of `𝔄(𝓛)` preserve every `L_i`. -/
theorem pow_apply_mem (hz : z ∈ 𝓛.endFiltration 0) (t : ℕ) {i : ℤ} {v : V}
    (hv : v ∈ 𝓛.lattice i) : (z ^ t) v ∈ 𝓛.lattice i := by
  have hz' : z ∈ 𝓛.order := 𝓛.mem_order_iff_mem_endFiltration.mpr hz
  exact 𝓛.mem_order.mp (pow_mem hz' t) i v hv

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `z^t L_i + L_{i+1} ⊆ L_i` for `z ∈ 𝔄(𝓛)`. -/
theorem imageLattice_le (hz : z ∈ 𝓛.endFiltration 0) (i : ℤ) (t : ℕ) :
    imageLattice 𝓛 z i t ≤ 𝓛.lattice i := by
  refine sup_le ?_ (𝓛.antitone (by omega))
  rintro _ ⟨v, hv, rfl⟩
  exact pow_apply_mem hz t hv

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The image lattice at `t = 0` is `L_i`. -/
theorem imageLattice_zero (hz : z ∈ 𝓛.endFiltration 0) (i : ℤ) :
    imageLattice 𝓛 z i 0 = 𝓛.lattice i := by
  refine le_antisymm (imageLattice_le hz i 0) (le_sup_of_le_left ?_)
  intro v hv
  exact ⟨v, hv, by simp⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The image lattices at `i` decrease with `t`. -/
theorem imageLattice_antitone (hz : z ∈ 𝓛.endFiltration 0) (i : ℤ) {s t : ℕ} (hst : s ≤ t) :
    imageLattice 𝓛 z i t ≤ imageLattice 𝓛 z i s := by
  refine sup_le (le_sup_of_le_left ?_) le_sup_right
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨(z ^ (t - s)) v, pow_apply_mem hz _ hv, ?_⟩
  change (z ^ s) ((z ^ (t - s)) v) = (z ^ t) v
  rw [← Module.End.mul_apply, ← pow_add, Nat.add_sub_cancel' hst]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- If `z^m ∈ 𝔓(𝓛)`, the image lattices at `i` with `t ≥ m` equal `L_{i+1}`. -/
theorem imageLattice_of_le (hz : z ∈ 𝓛.endFiltration 0) {m : ℕ}
    (hzm : z ^ m ∈ 𝓛.endFiltration 1) (i : ℤ) {t : ℕ} (hmt : m ≤ t) :
    imageLattice 𝓛 z i t = 𝓛.lattice (i + 1) := by
  refine le_antisymm (sup_le ?_ le_rfl) (lattice_succ_le_imageLattice i t)
  rintro _ ⟨v, hv, rfl⟩
  change (z ^ t) v ∈ 𝓛.lattice (i + 1)
  rw [show t = m + (t - m) by omega, pow_add, Module.End.mul_apply]
  exact hzm i _ (pow_apply_mem hz _ hv)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `z^{t+1} L_i + L_{i+1} = z (z^t L_i + L_{i+1}) + L_{i+1}`. -/
theorem imageLattice_succ (hz : z ∈ 𝓛.endFiltration 0) (i : ℤ) (t : ℕ) :
    imageLattice 𝓛 z i (t + 1) =
      (imageLattice 𝓛 z i t).map (z.restrictScalars 𝒪[F]) ⊔ 𝓛.lattice (i + 1) := by
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    rintro _ ⟨v, hv, rfl⟩
    refine le_sup_left (a := (imageLattice 𝓛 z i t).map (z.restrictScalars 𝒪[F]))
      ⟨(z ^ t) v, le_sup_left (b := 𝓛.lattice (i + 1)) ⟨v, hv, rfl⟩, ?_⟩
    change z ((z ^ t) v) = (z ^ (t + 1)) v
    rw [← Module.End.mul_apply, ← pow_succ']
  · refine sup_le ?_ le_sup_right
    rw [imageLattice, Submodule.map_sup, ← map_restrictScalars_mul, ← pow_succ']
    refine sup_le le_sup_left (le_sup_of_le_right ?_)
    rintro _ ⟨v, hv, rfl⟩
    have h := hz (i + 1) v hv
    rwa [add_zero] at h

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `z` maps the image lattice at `t` into the image lattice at `t + 1`. -/
theorem map_imageLattice_le (hz : z ∈ 𝓛.endFiltration 0) (i : ℤ) (t : ℕ) :
    (imageLattice 𝓛 z i t).map (z.restrictScalars 𝒪[F]) ≤ imageLattice 𝓛 z i (t + 1) := by
  rw [imageLattice_succ hz]
  exact le_sup_left

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- If two consecutive image lattices agree, they are the next lattice of the chain. -/
theorem imageLattice_eq_of_succ_eq (hz : z ∈ 𝓛.endFiltration 0) {m : ℕ}
    (hzm : z ^ m ∈ 𝓛.endFiltration 1) {i : ℤ} {t : ℕ}
    (h : imageLattice 𝓛 z i (t + 1) = imageLattice 𝓛 z i t) :
    imageLattice 𝓛 z i t = 𝓛.lattice (i + 1) := by
  have key : ∀ r : ℕ, imageLattice 𝓛 z i (t + r) = imageLattice 𝓛 z i t := by
    intro r
    induction r with
    | zero => rfl
    | succ r ih =>
      rw [← add_assoc, imageLattice_succ hz, ih, ← imageLattice_succ hz, h]
  rw [← key m]
  exact imageLattice_of_le hz hzm i (by omega)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A unit commuting with `z` and shifting the chain by `d` maps the image lattices at `i` to
those at `i + d`. -/
theorem map_imageLattice_of_shifts {g : (Module.End F V)ˣ} {d : ℤ} (hg : Shifts 𝓛 d g)
    (hgz : Commute (g : Module.End F V) z) (i : ℤ) (t : ℕ) :
    (imageLattice 𝓛 z i t).map ((g : Module.End F V).restrictScalars 𝒪[F]) =
      imageLattice 𝓛 z (i + d) t := by
  rw [imageLattice, Submodule.map_sup, ← map_restrictScalars_mul, (hgz.pow_right t).eq,
    map_restrictScalars_mul, hg.map_lattice, hg.map_lattice, imageLattice,
    show i + 1 + d = i + d + 1 by ring]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The image lattices are totally ordered. -/
theorem imageLattice_le_total (hz : z ∈ 𝓛.endFiltration 0) (i i' : ℤ) (t t' : ℕ) :
    imageLattice 𝓛 z i t ≤ imageLattice 𝓛 z i' t' ∨
      imageLattice 𝓛 z i' t' ≤ imageLattice 𝓛 z i t := by
  rcases lt_trichotomy i i' with h | rfl | h
  · right
    exact (imageLattice_le hz i' t').trans ((𝓛.antitone (by omega)).trans
      (lattice_succ_le_imageLattice i t))
  · rcases le_total t t' with h | h
    · right
      exact imageLattice_antitone hz i h
    · left
      exact imageLattice_antitone hz i h
  · left
    exact (imageLattice_le hz i t).trans ((𝓛.antitone (by omega)).trans
      (lattice_succ_le_imageLattice i' t'))

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Every image lattice is an image lattice at an index where it strictly contains the next
lattice of the chain. -/
theorem exists_imageLattice_eq_sandwich (hz : z ∈ 𝓛.endFiltration 0) (a : ℤ) (s : ℕ) :
    ∃ (i : ℤ) (t : ℕ), imageLattice 𝓛 z a s = imageLattice 𝓛 z i t ∧
      𝓛.lattice (i + 1) < imageLattice 𝓛 z i t := by
  by_cases h : 𝓛.lattice (a + 1) < imageLattice 𝓛 z a s
  · exact ⟨a, s, rfl, h⟩
  · have heq : imageLattice 𝓛 z a s = 𝓛.lattice (a + 1) :=
      ((lattice_succ_le_imageLattice a s).lt_or_eq.resolve_left h).symm
    refine ⟨a + 1, 0, by rw [heq, imageLattice_zero hz], ?_⟩
    rw [imageLattice_zero hz]
    exact 𝓛.lattice_succ_lt _

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Scalar endomorphisms commute with every endomorphism. -/
theorem scalarEndUnit_commute (u : Fˣ) (x : Module.End F V) :
    Commute ((scalarEndUnit (V := V) u : (Module.End F V)ˣ) : Module.End F V) x :=
  Algebra.commutes (u : F) x

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A unit of `End_F(V)` is injective. -/
theorem injective_restrictScalars (g : (Module.End F V)ˣ) :
    Function.Injective ((g : Module.End F V).restrictScalars 𝒪[F]) := by
  intro a c h
  have h' := congrArg (fun w => ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) w) h
  simpa [← Module.End.mul_apply] using h'

include hϖ in
/-- The image lattices `z^t L_i + L_{i+1}` are the lattices of a lattice chain. -/
theorem exists_imageChain (hz : z ∈ 𝓛.endFiltration 0) {m : ℕ}
    (hzm : z ^ m ∈ 𝓛.endFiltration 1) :
    ∃ 𝓜 : LatticeChain 𝒪[F] F V,
      Set.range 𝓜.lattice = Set.range (fun p : ℤ × ℕ => imageLattice 𝓛 z p.1 p.2) := by
  set ϖu := LatticeChain.uniformizerAsUnit hϖ
  have hπ : Shifts 𝓛 𝓛.period (scalarEndUnit ϖu) := uniformizerUnit_shifts hϖ 𝓛
  have hsmul' (i : ℤ) (t : ℕ) (k : ℤ) :
      ϖu ^ k • imageLattice 𝓛 z i t = imageLattice 𝓛 z (i + k * 𝓛.period) t := by
    have hk : scalarEndUnit (V := V) (ϖu ^ k) = scalarEndUnit ϖu ^ k :=
      map_zpow (Units.map (algebraMap F (Module.End F V)).toMonoidHom) ϖu k
    rw [units_smul_eq_map, hk]
    exact map_imageLattice_of_shifts (hπ.zpow k) (hk ▸ scalarEndUnit_commute _ z) i t
  apply exists_latticeChain_range_eq hϖ
  · rintro _ ⟨⟨i, t⟩, rfl⟩
    have := 𝓛.isLattice (i + 1)
    exact Submodule.IsLattice.of_le_of_isLattice_of_fg F (lattice_succ_le_imageLattice i t)
      ((𝓛.isLattice i).1.of_le (imageLattice_le hz i t))
  · rintro _ ⟨⟨i, t⟩, rfl⟩ _ ⟨⟨i', t'⟩, rfl⟩ _
    exact imageLattice_le_total hz i i' t t'
  · exact ⟨_, ⟨(0, 0), rfl⟩⟩
  · rintro _ ⟨⟨i, t⟩, rfl⟩ k
    exact ⟨(i + k * 𝓛.period, t), (hsmul' i t k).symm⟩
  · rintro _ ⟨⟨a, s⟩, rfl⟩
    obtain ⟨i, t, heq, hlt⟩ := exists_imageLattice_eq_sandwich hz a s
    change ϖu • imageLattice 𝓛 z a s < imageLattice 𝓛 z a s
    have h1 := hsmul' i t 1
    rw [zpow_one] at h1
    rw [heq, h1]
    refine lt_of_le_of_lt ((imageLattice_le hz _ t).trans (𝓛.antitone ?_)) hlt
    have := 𝓛.period_pos
    omega
  · rintro _ ⟨⟨i, t⟩, rfl⟩ _ ⟨⟨i', t'⟩, rfl⟩
    refine (((Set.finite_Icc (i - 1) (i' + 1)).prod (Set.finite_Iic m)).image
      (fun p : ℤ × ℕ => imageLattice 𝓛 z p.1 p.2)).subset ?_
    rintro _ ⟨⟨⟨a, s⟩, rfl⟩, h1, h2⟩
    refine ⟨(a, min s m), ⟨⟨?_, ?_⟩, Set.mem_Iic.mpr (min_le_right _ _)⟩, ?_⟩
    · have h := (lattice_succ_le_imageLattice a s).trans (h2.trans (imageLattice_le hz i t))
      have := 𝓛.strictAnti.le_iff_ge.mp h
      change i - 1 ≤ a
      omega
    · have h := (lattice_succ_le_imageLattice i' t').trans (h1.trans (imageLattice_le hz a s))
      have := 𝓛.strictAnti.le_iff_ge.mp h
      change a ≤ i' + 1
      omega
    · change imageLattice 𝓛 z a (min s m) = imageLattice 𝓛 z a s
      rcases le_total s m with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h, imageLattice_of_le hz hzm a le_rfl, imageLattice_of_le hz hzm a h]

include hϖ in
/-- **Refinement by images.** Let `z ∈ 𝔄(𝓛)` with `z^m ∈ 𝔓(𝓛)`, and let `b` be a unit commuting
with `z` and shifting `𝓛` by `ℓ`. The chain `𝓜` of image lattices `z^t L_i + L_{i+1}` contains
every `L_i`, `b` shifts `𝓜` by some `ℓ'`, `𝔓^{ℓ+1}(𝓛) ⊆ 𝔓^{ℓ'+1}(𝓜)`, `z ∈ 𝔓(𝓜)`, and every
unit of `𝔄(𝓛)` commuting with `z` is a unit of `𝔄(𝓜)`. -/
theorem exists_refinement (hz : z ∈ 𝓛.endFiltration 0) {m : ℕ}
    (hzm : z ^ m ∈ 𝓛.endFiltration 1) {b : (Module.End F V)ˣ} {ℓ : ℤ} (hb : Shifts 𝓛 ℓ b)
    (hbz : Commute (b : Module.End F V) z) :
    ∃ (𝓜 : LatticeChain 𝒪[F] F V) (ℓ' : ℤ), Shifts 𝓜 ℓ' b ∧
      (∀ i, ∃ j, 𝓛.lattice i = 𝓜.lattice j) ∧
      𝓛.endFiltration (ℓ + 1) ≤ 𝓜.endFiltration (ℓ' + 1) ∧ z ∈ 𝓜.endFiltration 1 ∧
      ∀ g : (Module.End F V)ˣ, Shifts 𝓛 0 g → Commute (g : Module.End F V) z → Shifts 𝓜 0 g := by
  obtain ⟨𝓜, h𝓜⟩ := exists_imageChain hϖ hz hzm
  have hmem (i : ℤ) (t : ℕ) : ∃ j, 𝓜.lattice j = imageLattice 𝓛 z i t := by
    have : imageLattice 𝓛 z i t ∈ Set.range 𝓜.lattice := h𝓜 ▸ ⟨(i, t), rfl⟩
    exact this
  have hrep (j : ℤ) : ∃ (i : ℤ) (t : ℕ), 𝓜.lattice j = imageLattice 𝓛 z i t ∧
      𝓛.lattice (i + 1) < imageLattice 𝓛 z i t := by
    have : 𝓜.lattice j ∈ Set.range (fun p : ℤ × ℕ => imageLattice 𝓛 z p.1 p.2) :=
      h𝓜 ▸ ⟨j, rfl⟩
    obtain ⟨⟨a, s⟩, has⟩ := this
    obtain ⟨i, t, heq, hlt⟩ := exists_imageLattice_eq_sandwich hz a s
    exact ⟨i, t, has.symm.trans heq, hlt⟩
  have hstab (g : (Module.End F V)ˣ) (d : ℤ) (hg : Shifts 𝓛 d g)
      (hgz : Commute (g : Module.End F V) z) (j : ℤ) :
      ∃ j', (𝓜.lattice j).map ((g : Module.End F V).restrictScalars 𝒪[F]) = 𝓜.lattice j' := by
    obtain ⟨i, t, hj, -⟩ := hrep j
    obtain ⟨j', hj'⟩ := hmem (i + d) t
    exact ⟨j', by rw [hj, map_imageLattice_of_shifts hg hgz, hj']⟩
  obtain ⟨ℓ', hℓ'⟩ := 𝓜.exists_shift (hstab b ℓ hb hbz)
  refine ⟨𝓜, ℓ', shifts_of_map_eq 𝓜 hℓ', ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨j, hj⟩ := hmem i 0
    exact ⟨j, by rw [hj, imageLattice_zero hz]⟩
  · intro x hx j v hv
    obtain ⟨i, t, hj, hlt⟩ := hrep j
    rw [hj] at hv
    have hxv : x v ∈ 𝓛.lattice (i + 1 + ℓ) := by
      have := hx i v (imageLattice_le hz i t hv)
      rwa [show i + (ℓ + 1) = i + 1 + ℓ by ring] at this
    obtain ⟨q, hq⟩ := hmem (i + 1 + ℓ) 0
    rw [imageLattice_zero hz] at hq
    have hlt' : 𝓜.lattice q < 𝓜.lattice (j + ℓ') := by
      rw [hq, ← hℓ' j, hj, ← hb.map_lattice (i + 1)]
      exact Submodule.map_strictMono_of_injective (injective_restrictScalars b) hlt
    have hjq : j + ℓ' < q := 𝓜.strictAnti.lt_iff_gt.mp hlt'
    exact 𝓜.antitone (show j + (ℓ' + 1) ≤ q by omega) (hq ▸ hxv)
  · intro j v hv
    obtain ⟨i, t, hj, hlt⟩ := hrep j
    rw [hj] at hv
    have hzv : z v ∈ imageLattice 𝓛 z i (t + 1) := map_imageLattice_le hz i t ⟨v, hv, rfl⟩
    have hne : imageLattice 𝓛 z i (t + 1) ≠ imageLattice 𝓛 z i t :=
      fun h => hlt.ne (imageLattice_eq_of_succ_eq hz hzm h).symm
    have hlt2 : imageLattice 𝓛 z i (t + 1) < imageLattice 𝓛 z i t :=
      lt_of_le_of_ne (imageLattice_antitone hz i (Nat.le_succ t)) hne
    obtain ⟨q, hq⟩ := hmem i (t + 1)
    have hjq : j < q := 𝓜.strictAnti.lt_iff_gt.mp (by rw [hq, hj]; exact hlt2)
    exact 𝓜.antitone (show j + 1 ≤ q by omega) (hq ▸ hzv)
  · intro g hg hgz
    apply shifts_of_map_eq 𝓜
    intro j
    obtain ⟨i, t, hj, -⟩ := hrep j
    rw [hj, map_imageLattice_of_shifts hg hgz, add_zero, ← hj, add_zero]

end Langlands.BushnellKutzko.NonsplitRefinement
