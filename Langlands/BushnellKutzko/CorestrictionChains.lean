import Langlands.BushnellKutzko.CorestrictionIntegers
import Langlands.BushnellKutzko.CorestrictionLatticeDual

/-! # Lattice chains normalized by an extension field -/

noncomputable section

open Module ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe uF uE uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {E : Type uE} [Field E] [Algebra F E] [FiniteDimensional F E]
  {V : Type uV} [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]

local notation "O" => 𝒪[F]
local notation "S" => subfieldIntegers F E

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem lattice_smul_zpow (𝓛 : LatticeChain O F V) {K : Type*} [Field K]
    [Module K V] [SMulCommClass K O V] {a : K} (ha : a ≠ 0) {d : ℤ}
    (h : ∀ i, a • 𝓛.lattice i = 𝓛.lattice (i + d)) (i n : ℤ) :
    a ^ n • 𝓛.lattice i = 𝓛.lattice (i + n * d) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one₀ ha, mul_comm _ a, mul_smul, ih, h]
    congr 1
    ring
  | pred n ih =>
    have hcancel : Function.Injective (fun N : Submodule O V => a • N) := by
      intro X Y hxy
      have he := congrArg (fun N : Submodule O V => a⁻¹ • N) hxy
      simpa only [← mul_smul, inv_mul_cancel₀ ha, one_smul] using he
    apply hcancel
    change a • (a ^ (-(n : ℤ) - 1) • 𝓛.lattice i) =
      a • 𝓛.lattice (i + (-(n : ℤ) - 1) * d)
    rw [← mul_smul, mul_comm a, ← zpow_add_one₀ ha, sub_add_cancel, ih, h]
    congr 1
    ring

private theorem exists_mem_lattice (𝓛 : LatticeChain O F V) (v : V) :
    ∃ i, v ∈ 𝓛.lattice i := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπF : algebraMap O F π ≠ 0 := by
    rw [← map_zero (algebraMap O F)]
    exact (IsFractionRing.injective O F).ne hπ.ne_zero
  have ha i : (algebraMap O F π) • 𝓛.lattice i = 𝓛.lattice (i + 𝓛.period) :=
    (𝓛.lattice_add_period_uniformizer hπ i).symm
  let U : Submodule F V :=
    { carrier := {w | ∃ i, w ∈ 𝓛.lattice i}
      zero_mem' := ⟨0, zero_mem _⟩
      add_mem' := by
        rintro x y ⟨i, hi⟩ ⟨j, hj⟩
        exact ⟨min i j, add_mem (𝓛.antitone (min_le_left _ _) hi)
          (𝓛.antitone (min_le_right _ _) hj)⟩
      smul_mem' := by
        rintro c w ⟨i, hi⟩
        by_cases hc : c = 0
        · exact ⟨0, by simp [hc]⟩
        obtain ⟨n, u, hcu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
          hπ hc
        have hs : (algebraMap O F π ^ n) • w ∈ 𝓛.lattice (i + n * 𝓛.period) := by
          rw [← lattice_smul_zpow 𝓛 hπF ha i n]
          exact Submodule.smul_mem_pointwise_smul w _ _ hi
        refine ⟨i + n * 𝓛.period, ?_⟩
        change c • w ∈ 𝓛.lattice (i + n * 𝓛.period)
        rw [hcu, Units.smul_def, Algebra.smul_def, mul_smul, algebraMap_smul]
        exact Submodule.smul_mem _ (u : O) hs }
  have hspan : Submodule.span F (𝓛.lattice 0 : Set V) ≤ U :=
    Submodule.span_le.mpr fun _ hw => ⟨0, hw⟩
  rw [(𝓛.isLattice 0).span_eq_top] at hspan
  exact hspan (Submodule.mem_top (R := F))

private theorem exists_le_lattice (𝓛 : LatticeChain O F V) (N : Submodule O V) (hN : N.FG) :
    ∃ i, N ≤ 𝓛.lattice i := by
  classical
  obtain ⟨s, hspan⟩ := hN
  have hfinite (t : Finset V) : ∃ i, ∀ v ∈ t, v ∈ 𝓛.lattice i := by
    induction t using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert v t _ ih =>
      obtain ⟨i, hi⟩ := ih
      obtain ⟨j, hj⟩ := exists_mem_lattice 𝓛 v
      refine ⟨min i j, ?_⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact 𝓛.antitone (min_le_right _ _) hj
      · exact 𝓛.antitone (min_le_left _ _) (hi w hw)
  obtain ⟨i, hi⟩ := hfinite s
  exact ⟨i, hspan ▸ Submodule.span_le.mpr hi⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F E] in
private theorem units_smul_eq_map (a : Eˣ) (L : Submodule O V) :
    (a : E) • L = L.map ((subfieldUnits F E V a : Module.End F V).restrictScalars O) := by
  rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F E] in
private theorem exists_scalar_shift (𝓛 : LatticeChain O F V)
    (h : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer) (a : Eˣ) :
    ∃ d : ℤ, ∀ i, (a : E) • 𝓛.lattice i = 𝓛.lattice (i + d) := by
  obtain ⟨d, hd⟩ := 𝓛.exists_shift (h a)
  exact ⟨d, fun i => (units_smul_eq_map a _).trans (hd i)⟩

private theorem scalar_shift_nonneg (𝓛 : LatticeChain O F V) {a : Eˣ}
    (ha : (a : E) ∈ S) {d : ℤ} (hshift : ∀ i, (a : E) • 𝓛.lattice i = 𝓛.lattice (i + d)) :
    0 ≤ d := by
  have hlt : 𝓛.lattice 1 < 𝓛.lattice 0 := by simpa using 𝓛.lattice_succ_lt 0
  obtain ⟨v, _, hv⟩ := SetLike.exists_of_lt hlt
  let f : S →ₗ[O] V :=
    (((LinearMap.id : E →ₗ[E] E).smulRight v).restrictScalars O).comp
      (subfieldIntegers F E).val.toLinearMap
  obtain ⟨j, hj⟩ := exists_le_lattice 𝓛 f.range (Submodule.fg_range f)
  by_contra! hd
  let m := (1 - j).toNat
  have hm : 1 + (m : ℤ) * d ≤ j := by
    have hmul := mul_le_mul_of_nonneg_left (show d ≤ -1 by omega)
      (Int.natCast_nonneg m)
    dsimp only [m] at hmul ⊢
    simp only [mul_neg, mul_one] at hmul
    omega
  have hmem : ((a : E) ^ m) • v ∈ f.range :=
    ⟨⟨(a : E) ^ m, pow_mem ha m⟩, rfl⟩
  have hs := 𝓛.antitone hm (hj hmem)
  rw [← lattice_smul_zpow 𝓛 a.ne_zero hshift 1 m, zpow_natCast] at hs
  obtain ⟨w, hw, heq⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hs
  exact hv ((smul_right_injective V (pow_ne_zero m a.ne_zero) heq) ▸ hw)

private theorem subfieldIntegers_smul_mem (𝓛 : LatticeChain O F V)
    (h : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)
    (x : S) {i : ℤ} {v : V} (hv : v ∈ 𝓛.lattice i) :
    (x : E) • v ∈ 𝓛.lattice i := by
  by_cases hx : (x : E) = 0
  · simp [hx]
  let a := Units.mk0 (x : E) hx
  obtain ⟨d, hd⟩ := exists_scalar_shift 𝓛 h a
  have hsign := scalar_shift_nonneg 𝓛 (a := a) x.property hd
  have hs := Submodule.smul_mem_pointwise_smul v (a : E) (𝓛.lattice i) hv
  rw [hd] at hs
  exact 𝓛.antitone (by omega : i ≤ i + d) hs

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F E] in
private theorem integerUnit_smul_restrict_eq (N : Submodule S V) (u : Sˣ) :
    ((u : S) : E) • N.restrictScalars O = N.restrictScalars O := by
  ext v
  have h : (u : S) • N = N := Submodule.smul_eq_self_of_isUnit u.isUnit
  exact Iff.of_eq (congrArg (fun P : Submodule S V => v ∈ P) h)

/-- A base lattice in a chain normalized by the extension field, with its integer scalars. -/
def LatticeChain.extensionLattice (𝓛 : LatticeChain O F V)
    (h : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer) (i : ℤ) : Submodule S V where
  carrier := 𝓛.lattice i
  add_mem' := (𝓛.lattice i).add_mem
  zero_mem' := (𝓛.lattice i).zero_mem
  smul_mem' := fun a _ hv => subfieldIntegers_smul_mem 𝓛 h a hv

private theorem extensionLattice_isLattice (𝓛 : LatticeChain O F V)
    (h : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer) (i : ℤ) :
    (𝓛.extensionLattice h i).IsLattice E := by
  refine ⟨?_, ?_⟩
  · obtain ⟨s, hs⟩ := (𝓛.isLattice i).fg
    refine ⟨s, le_antisymm (Submodule.span_le.mpr ?_) ?_⟩
    · intro v hv
      change v ∈ 𝓛.lattice i
      rw [← hs]
      exact Submodule.subset_span hv
    · change 𝓛.lattice i ≤ (Submodule.span S (s : Set V)).restrictScalars O
      rw [← hs]
      exact Submodule.span_le.mpr fun _ hv => Submodule.subset_span hv
  · have hspan : Submodule.span F (𝓛.lattice i : Set V) ≤
        (Submodule.span E (𝓛.extensionLattice h i : Set V)).restrictScalars F :=
      Submodule.span_le.mpr fun _ hv => Submodule.subset_span hv
    rw [(𝓛.isLattice i).span_eq_top] at hspan
    exact eq_top_iff.mpr fun _ _ => hspan (Submodule.mem_top (R := F))

private theorem base_uniformizer_factor {π : O} (hπ : Irreducible π)
    {ϖ : S} (hϖ : Irreducible ϖ) :
    ∃ (n : ℕ) (u : Sˣ), 0 < n ∧ algebraMap O S π = (u : S) * ϖ ^ n := by
  have hinj : Function.Injective (algebraMap O S) := by
    intro x y h
    apply IsFractionRing.injective O F
    apply (algebraMap F E).injective
    exact congrArg (fun z : S => (z : E)) h
  have hπ' : algebraMap O S π ≠ 0 := by
    rw [← map_zero (algebraMap O S)]
    exact hinj.ne hπ.ne_zero
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπ' hϖ
  refine ⟨n, u, Nat.pos_of_ne_zero ?_, hu⟩
  intro hn
  have : IsLocalHom (algebraMap O S) :=
    (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral O S)).isLocalHom hinj
  apply hπ.not_isUnit
  apply isUnit_of_map_unit (algebraMap O S)
  rw [hu, hn, pow_zero, mul_one]
  exact u.isUnit

private theorem extension_uniformizer_shift (𝓛 : LatticeChain O F V)
    (h : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer) {ϖ : S} (hϖ : Irreducible ϖ) :
    ∃ d : ℕ, 0 < d ∧ ∀ i, (ϖ : E) • 𝓛.lattice i = 𝓛.lattice (i + d) := by
  have hϖ' : (ϖ : E) ≠ 0 := by
    intro hz
    exact hϖ.ne_zero (Subtype.ext hz)
  let a := Units.mk0 (ϖ : E) hϖ'
  obtain ⟨d, hd⟩ := exists_scalar_shift 𝓛 h a
  have hnonneg := scalar_shift_nonneg 𝓛 (a := a) ϖ.property hd
  have hshift (i : ℤ) : (ϖ : E) • 𝓛.lattice i = 𝓛.lattice (i + d) := hd i
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, _, hu⟩ := base_uniformizer_factor hπ hϖ
  have hbase : ((algebraMap O S π : S) : E) • 𝓛.lattice 0 = 𝓛.lattice (0 + 𝓛.period) := by
    rw [𝓛.lattice_add_period_uniformizer hπ]
    ext v
    simp only [Submodule.mem_smul_pointwise_iff_exists]
    have hc : ((algebraMap O S π : S) : E) = algebraMap F E (algebraMap O F π) := rfl
    rw [hc]
    simp only [algebraMap_smul]
  rw [hu, Subalgebra.coe_mul, Subalgebra.coe_pow, mul_smul, ← zpow_natCast,
    lattice_smul_zpow 𝓛 hϖ' hshift] at hbase
  have hu' : ((u : S) : E) • 𝓛.lattice (0 + (n : ℤ) * d) =
      𝓛.lattice (0 + (n : ℤ) * d) :=
    integerUnit_smul_restrict_eq (𝓛.extensionLattice h _) u
  rw [hu'] at hbase
  have he := 𝓛.injective hbase
  have hdpos : 0 < d := by
    by_contra! hdle
    have hd0 : d = 0 := le_antisymm hdle hnonneg
    simp only [hd0, mul_zero, add_zero, zero_add] at he
    have hp : 0 < (𝓛.period : ℤ) := Int.natCast_pos.mpr 𝓛.period_pos
    omega
  refine ⟨d.toNat, by omega, fun i => ?_⟩
  rw [Int.toNat_of_nonneg hnonneg]
  exact hshift i

/-- The same chain of subsets, viewed as a lattice chain over the extension integers. -/
def LatticeChain.extensionChain (𝓛 : LatticeChain O F V)
    (h : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer) : LatticeChain S E V where
  lattice := 𝓛.extensionLattice h
  isLattice := extensionLattice_isLattice 𝓛 h
  lattice_succ_lt := fun i => 𝓛.lattice_succ_lt i
  exists_period := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
    obtain ⟨d, hd, hshift⟩ := extension_uniformizer_shift 𝓛 h hϖ
    refine ⟨d, hd, fun i => ?_⟩
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal, hϖ.maximalIdeal_eq,
      Submodule.ideal_span_singleton_smul]
    ext v
    have he := Iff.of_eq (congrArg (fun N : Submodule O V => v ∈ N) (hshift i).symm)
    exact he

/-- The relative filtration is the intersection with the extension-linear endomorphisms. -/
theorem LatticeChain.mem_extensionChain_endFiltration (𝓛 : LatticeChain O F V)
    (h : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer) (n : ℤ) (x : Module.End E V) :
    x ∈ (𝓛.extensionChain h).endFiltration n ↔ x.restrictScalars F ∈ 𝓛.endFiltration n :=
  Iff.rfl

section BasisChain

variable {ι : Type*} [Finite ι] (b : Basis ι E V)

private theorem span_basis_restrict_isLattice :
    ((Submodule.span S (Set.range b)).restrictScalars O).IsLattice F := by
  let N := Submodule.span S (Set.range b)
  let M := N.restrictScalars O
  refine ⟨?_, ?_⟩
  · have : Module.Finite S N := Module.Finite.of_fg (Submodule.fg_span (Set.finite_range b))
    have : Module.Finite O N := Module.Finite.trans S N
    exact Module.Finite.iff_fg.mp (show Module.Finite O M from this)
  · let P := Submodule.span F (M : Set V)
    have hmul (z : E) (j : ι) : z • b j ∈ P := by
      obtain ⟨a, ha, haz⟩ := exists_smul_mem_subfieldIntegers F E z
      have hb : b j ∈ N := Submodule.subset_span ⟨j, rfl⟩
      have h : (a • z) • b j ∈ N := N.smul_mem (⟨a • z, haz⟩ : S) hb
      have hP : a • (z • b j) ∈ P := by
        rw [← smul_assoc]
        exact Submodule.subset_span (show (a • z) • b j ∈ M from h)
      simpa only [inv_smul_smul₀ ha] using P.smul_mem a⁻¹ hP
    apply eq_top_iff.mpr
    intro v _
    have := Fintype.ofFinite ι
    rw [← b.sum_repr v]
    exact P.sum_mem (fun j _ => hmul _ j)

omit [Finite ι] in
private theorem uniformizer_smul_span_basis_lt [Nonempty ι] {ϖ : S} (hϖ : Irreducible ϖ) :
    (ϖ : E) • (Submodule.span S (Set.range b)).restrictScalars O <
      (Submodule.span S (Set.range b)).restrictScalars O := by
  classical
  let N := Submodule.span S (Set.range b)
  let M := N.restrictScalars O
  refine lt_of_le_not_ge ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact N.smul_mem ϖ hw
  · intro h
    let j : ι := Classical.choice inferInstance
    have hb : b j ∈ M := Submodule.subset_span ⟨j, rfl⟩
    obtain ⟨v, hv, he⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (h hb)
    obtain ⟨z, hz⟩ := (Basis.mem_span_iff_repr_mem S b v).mp hv j
    change (z : E) = b.repr v j at hz
    have heq := congrArg (fun w : V => b.repr w j) he
    have hmul : algebraMap S E (ϖ * z) = 1 := by
      change ((ϖ * z : S) : E) = 1
      rw [Subalgebra.coe_mul]
      simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul, Basis.repr_self,
        Finsupp.single_eq_same, ← hz] using heq
    apply hϖ.not_isUnit
    exact IsUnit.of_mul_eq_one z
      (IsFractionRing.injective S E (by rw [hmul, map_one]))

/-- A base lattice chain obtained by rescaling an extension-basis lattice by a uniformizer. -/
def subfieldBasisChain [Nonempty ι] {ϖ : S} (hϖ : Irreducible ϖ) : LatticeChain O F V := by
  let N := Submodule.span S (Set.range b)
  let M := N.restrictScalars O
  let c := (ϖ : E)
  have hc : c ≠ 0 := fun hz => hϖ.ne_zero (Subtype.ext hz)
  let L (i : ℤ) : Submodule O V := c ^ i • M
  have hM : M.IsLattice F := span_basis_restrict_isLattice (F := F) b
  refine ⟨L, ?_, ?_, ?_⟩
  · intro i
    refine ⟨hM.fg.map _, ?_⟩
    change Submodule.span F ((c ^ i • M : Submodule O V) : Set V) = ⊤
    rw [Submodule.coe_pointwise_smul, ← Submodule.smul_span, hM.span_eq_top]
    apply eq_top_iff.mpr
    intro v _
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
      ⟨(c ^ i)⁻¹ • v, Submodule.mem_top, ?_⟩
    exact smul_inv_smul₀ (zpow_ne_zero i hc) v
  · intro i
    change c ^ (i + 1) • M < c ^ i • M
    rw [zpow_add_one₀ hc, mul_smul]
    apply Submodule.map_strictMono_of_injective
      (f := DistribSMul.toLinearMap O V (c ^ i)) (smul_right_injective V (zpow_ne_zero i hc))
    exact uniformizer_smul_span_basis_lt b hϖ
  · obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨n, u, hn, hu⟩ := base_uniformizer_factor hπ hϖ
    refine ⟨n, hn, fun i => ?_⟩
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal, hπ.maximalIdeal_eq,
      Submodule.ideal_span_singleton_smul]
    have hπE : π • L i = ((algebraMap O S π : S) : E) • L i := by
      ext v
      simp only [Submodule.mem_smul_pointwise_iff_exists]
      have hcoe : ((algebraMap O S π : S) : E) = algebraMap F E (algebraMap O F π) := rfl
      rw [hcoe]
      simp only [algebraMap_smul]
    rw [hπE, hu, Subalgebra.coe_mul, Subalgebra.coe_pow]
    change c ^ (i + (n : ℤ)) • M = (((u : S) : E) * c ^ n) • (c ^ i • M)
    rw [zpow_add₀ hc, zpow_natCast, ← mul_smul]
    calc
      (c ^ i * c ^ n) • M = (c ^ i * c ^ n) • (((u : S) : E) • M) :=
        congrArg (fun P : Submodule O V => (c ^ i * c ^ n) • P)
          (integerUnit_smul_restrict_eq N u).symm
      _ = (((u : S) : E) * c ^ n * c ^ i) • M := by rw [← mul_smul]; congr 1; ac_rfl

variable [Nonempty ι]

theorem subfieldBasisChain_lattice {ϖ : S} (hϖ : Irreducible ϖ) (i : ℤ) :
    (subfieldBasisChain (F := F) b hϖ).lattice i =
      (ϖ : E) ^ i • (Submodule.span S (Set.range b)).restrictScalars O :=
  rfl

/-- The uniformizer powers of an extension-basis lattice give a normalized base chain. -/
theorem subfieldBasisChain_normalized {ϖ : S} (hϖ : Irreducible ϖ) (a : Eˣ) :
    subfieldUnits F E V a ∈ (subfieldBasisChain (F := F) b hϖ).stabilizer := by
  intro i
  let c := (ϖ : E)
  have hc : c ≠ 0 := fun hz => hϖ.ne_zero (Subtype.ext hz)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    hϖ a.ne_zero
  refine ⟨i + n, ?_⟩
  rw [← units_smul_eq_map, subfieldBasisChain_lattice, subfieldBasisChain_lattice]
  let N := Submodule.span S (Set.range b)
  let M := N.restrictScalars O
  change (a : E) • (c ^ i • M) = c ^ (i + n) • M
  rw [hu, Units.smul_def, Algebra.smul_def, zpow_add₀ hc, ← mul_smul]
  change (((u : S) : E) * c ^ n * c ^ i) • M = (c ^ i * c ^ n) • M
  calc
    _ = (c ^ i * c ^ n) • (((u : S) : E) • M) := by rw [← mul_smul]; congr 1; ac_rfl
    _ = _ := congrArg (fun P : Submodule O V => (c ^ i * c ^ n) • P)
      (integerUnit_smul_restrict_eq N u)

/-- A scalar preserving the extension-basis chain belongs to the extension integer ring. -/
theorem mem_subfieldIntegers_of_mem_subfieldBasisChain_order {ϖ : S} (hϖ : Irreducible ϖ)
    (z : E) (hz : subfieldEmbedding F E V z ∈ (subfieldBasisChain (F := F) b hϖ).order) :
    z ∈ S := by
  classical
  let 𝓛 := subfieldBasisChain b hϖ
  let j : ι := Classical.choice inferInstance
  have hb : b j ∈ 𝓛.lattice 0 := by
    rw [subfieldBasisChain_lattice, zpow_zero, one_smul]
    exact Submodule.subset_span ⟨j, rfl⟩
  have h := 𝓛.mem_order.mp hz 0 (b j) hb
  change z • b j ∈ 𝓛.lattice 0 at h
  rw [subfieldBasisChain_lattice, zpow_zero, one_smul] at h
  obtain ⟨w, hw⟩ := (Basis.mem_span_iff_repr_mem S b (z • b j)).mp h j
  change (w : E) = b.repr (z • b j) j at hw
  have he : (w : E) = z := by
    simpa only [map_smul, Finsupp.smul_apply, Basis.repr_self, Finsupp.single_eq_same,
      smul_eq_mul, mul_one] using hw
  exact he ▸ w.property

end BasisChain

end Langlands.BushnellKutzko
