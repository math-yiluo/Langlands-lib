import Langlands.BushnellKutzko.PureStratumApproximationScaling
import Langlands.BushnellKutzko.PureStratumApproximationDiagonalTransport
import Langlands.BushnellKutzko.CorestrictionChains

/-! # Lattice chains over an extension field, viewed over the base field

An `𝔬_E`-lattice chain in an `E`-vector space `V` is an `𝔬_F`-lattice chain normalized by
`Eˣ` (BK93 (1.2.1), printed p. 24). This module constructs the `𝔬_F`-chain, computes its
period, and compares valuations and critical exponents of an element of `E` on two such chains
(BK93 (1.4.13), printed p. 39).
-/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko.PureApproximation

universe uF uE uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type uE} [Field E] [Algebra F E] [FiniteDimensional F E]
  {V : Type uV} [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]

section Lift

omit [IsScalarTower F E V] in
/-- The ramification index of a finite extension is positive. -/
theorem subfieldRamificationIndex_pos' : 0 < subfieldRamificationIndex F E := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F E)
  exact LatticeChain.subfieldRamificationIndex_pos E
    (subfieldBasisChain (F := F) (Module.Basis.singleton Unit E) hϖ)
    (subfieldBasisChain_normalized (Module.Basis.singleton Unit E) hϖ)

/-- An `𝔬_E`-lattice of `V` is an `𝔬_F`-lattice. -/
theorem isLattice_restrictScalars (M : Submodule (subfieldIntegers F E) V) (hM : M.IsLattice E) :
    (M.restrictScalars 𝒪[F]).IsLattice F := by
  refine ⟨?_, ?_⟩
  · have : Module.Finite (subfieldIntegers F E) M := Module.Finite.iff_fg.mpr hM.fg
    have : Module.Finite 𝒪[F] M := Module.Finite.trans (subfieldIntegers F E) M
    exact Module.Finite.iff_fg.mp (show Module.Finite 𝒪[F] (M.restrictScalars 𝒪[F]) from this)
  · let P := Submodule.span F (M : Set V)
    have hmem (z : E) {v : V} (hv : v ∈ M) : z • v ∈ P := by
      obtain ⟨a, ha, haz⟩ := exists_smul_mem_subfieldIntegers F E z
      have h : (a • z) • v ∈ M := M.smul_mem (⟨a • z, haz⟩ : (subfieldIntegers F E)) hv
      have hP : a • (z • v) ∈ P := by
        rw [← smul_assoc]
        exact Submodule.subset_span h
      simpa only [inv_smul_smul₀ ha] using P.smul_mem a⁻¹ hP
    have hclosed (z : E) {x : V} (hx : x ∈ P) : z • x ∈ P := by
      induction hx using Submodule.span_induction with
      | mem x hx => exact hmem z hx
      | zero => simp
      | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
      | smul c x _ hx =>
        rw [← algebraMap_smul E c x, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
        exact P.smul_mem c hx
    apply eq_top_iff.mpr
    rintro v -
    have hv : v ∈ Submodule.span E (M : Set V) := hM.span_eq_top ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul z x _ hx => exact hclosed z hx

variable (M : LatticeChain (subfieldIntegers F E) E V)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Module F V] [IsScalarTower F E V]
  [FiniteDimensional F E] in
theorem smul_coe_eq (a : (subfieldIntegers F E)) (v : V) : a • v = (a : E) • v := rfl

omit [Module F V] [IsScalarTower F E V] in
/-- Multiplication by an extension uniformizer moves a vector one period down the chain. -/
theorem uniformizer_smul_mem_iff {ϖ : (subfieldIntegers F E)} (hϖ : Irreducible ϖ) (i : ℤ)
    (v : V) : (ϖ : E) • v ∈ M.lattice (i + M.period) ↔ v ∈ M.lattice i := by
  have hc : (ϖ : E) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  rw [M.lattice_add_period_uniformizer hϖ i]
  change (ϖ : E) • v ∈ (ϖ : E) • M.lattice i ↔ _
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, hw, he⟩
    rwa [← smul_right_injective V hc he]
  · intro hv
    exact ⟨v, hv, rfl⟩

omit [Module F V] [IsScalarTower F E V] in
theorem zpow_uniformizer_smul_mem_iff {ϖ : (subfieldIntegers F E)} (hϖ : Irreducible ϖ)
    (k i : ℤ) (v : V) :
    (ϖ : E) ^ k • v ∈ M.lattice (i + k * M.period) ↔ v ∈ M.lattice i := by
  have hc : (ϖ : E) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  induction k using Int.induction_on generalizing i v with
  | zero => simp
  | succ k ih =>
    rw [zpow_add_one₀ hc, mul_smul,
      show i + ((k : ℤ) + 1) * (M.period : ℤ) = (i + M.period) + k * M.period by ring]
    exact (ih (i + M.period) ((ϖ : E) • v)).trans (uniformizer_smul_mem_iff M hϖ i v)
  | pred k ih =>
    rw [← uniformizer_smul_mem_iff M hϖ (i + (-(k : ℤ) - 1) * M.period), smul_smul,
      ← zpow_one_add₀ hc, show 1 + (-(k : ℤ) - 1) = -(k : ℤ) by ring,
      show i + (-(k : ℤ) - 1) * (M.period : ℤ) + M.period = i + -(k : ℤ) * M.period by ring]
    exact ih i v

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F E] [Module F V]
  [IsScalarTower F E V] in
theorem integerUnit_smul_mem_iff (u : (subfieldIntegers F E)ˣ) (i : ℤ) (v : V) :
    ((u : (subfieldIntegers F E)) : E) • v ∈ M.lattice i ↔ v ∈ M.lattice i := by
  constructor
  · intro h
    have h' := (M.lattice i).smul_mem ((u⁻¹ : (subfieldIntegers F E)ˣ) : (subfieldIntegers F E)) h
    rwa [smul_coe_eq, smul_smul, ← Subalgebra.coe_mul, Units.inv_mul, Subalgebra.coe_one,
      one_smul] at h'
  · intro h
    exact (M.lattice i).smul_mem (u : (subfieldIntegers F E)) h

omit [Module F V] [IsScalarTower F E V] in
/-- A field unit `u ϖ^k` moves the chain by `k` periods. -/
theorem units_smul_mem_iff {ϖ : (subfieldIntegers F E)} (hϖ : Irreducible ϖ) (a : Eˣ) {k : ℤ} {u : (subfieldIntegers F E)ˣ}
    (ha : (a : E) = ((u : (subfieldIntegers F E)) : E) * (ϖ : E) ^ k) (i : ℤ) (v : V) :
    (a : E) • v ∈ M.lattice (i + k * M.period) ↔ v ∈ M.lattice i := by
  rw [ha, mul_smul, integerUnit_smul_mem_iff, zpow_uniformizer_smul_mem_iff M hϖ]

/-- The base uniformizer moves the chain by `e(E|F)` periods. -/
theorem baseUniformizer_smul_mem_iff {π : 𝒪[F]} (hπ : Irreducible π) (i : ℤ) (v : V) :
    (π : F) • v ∈ M.lattice (i + subfieldRamificationIndex F E * M.period) ↔
      v ∈ M.lattice i := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F E)
  obtain ⟨u, hu⟩ := baseUniformizer_factorization F E hπ hϖ
  have h : (π : F) • v = (((u : (subfieldIntegers F E)) : E) * (ϖ : E) ^ (subfieldRamificationIndex F E : ℤ)) • v := by
    rw [← algebraMap_smul E (π : F) v]
    congr 1
    have := congrArg (fun x : (subfieldIntegers F E) => (x : E)) hu
    simp only [Subalgebra.coe_mul, Subalgebra.coe_pow] at this
    rw [zpow_natCast, ← this]
    rfl
  rw [h, mul_smul, integerUnit_smul_mem_iff]
  exact zpow_uniformizer_smul_mem_iff M hϖ _ i v

/-- The lattices of an `𝔬_E`-chain, as an `𝔬_F`-lattice chain. -/
def liftChain : LatticeChain 𝒪[F] F V where
  lattice i := (M.lattice i).restrictScalars 𝒪[F]
  isLattice i := isLattice_restrictScalars _ (M.isLattice i)
  lattice_succ_lt i := by
    rw [← SetLike.coe_ssubset_coe, Submodule.coe_restrictScalars,
      Submodule.coe_restrictScalars, SetLike.coe_ssubset_coe]
    exact M.lattice_succ_lt i
  exists_period := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
    have he : 0 < subfieldRamificationIndex F E := subfieldRamificationIndex_pos'
    refine ⟨subfieldRamificationIndex F E * M.period, Nat.mul_pos he M.period_pos, fun i => ?_⟩
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal, hπ.maximalIdeal_eq,
      Submodule.ideal_span_singleton_smul]
    have hπ0 : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
    ext v
    rw [Submodule.mem_smul_pointwise_iff_exists]
    change v ∈ M.lattice _ ↔ ∃ w ∈ M.lattice i, (π : F) • w = v
    push_cast
    constructor
    · intro hv
      refine ⟨(π : F)⁻¹ • v, ?_, smul_inv_smul₀ hπ0 v⟩
      rw [← baseUniformizer_smul_mem_iff M hπ, smul_inv_smul₀ hπ0]
      exact hv
    · rintro ⟨w, hw, rfl⟩
      exact (baseUniformizer_smul_mem_iff M hπ i w).mpr hw

@[simp] theorem mem_liftChain_lattice (i : ℤ) (v : V) :
    v ∈ (liftChain M).lattice i ↔ v ∈ M.lattice i := Iff.rfl

theorem coe_liftChain_lattice (i : ℤ) :
    ((liftChain M).lattice i : Set V) = M.lattice i := rfl

/-- The period of the lifted chain is `e(E|F)` times the period over `𝔬_E`. -/
theorem liftChain_period :
    (liftChain M).period = subfieldRamificationIndex F E * M.period := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hπ0 : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  symm
  apply LatticeChain.period_unique
  intro i
  rw [IsLocalRing.ringJacobson_eq_maximalIdeal, hπ.maximalIdeal_eq,
    Submodule.ideal_span_singleton_smul]
  ext v
  rw [Submodule.mem_smul_pointwise_iff_exists]
  change v ∈ M.lattice _ ↔ ∃ w ∈ M.lattice i, (π : F) • w = v
  push_cast
  constructor
  · intro hv
    refine ⟨(π : F)⁻¹ • v, ?_, smul_inv_smul₀ hπ0 v⟩
    rw [← baseUniformizer_smul_mem_iff M hπ, smul_inv_smul₀ hπ0]
    exact hv
  · rintro ⟨w, hw, rfl⟩
    exact (baseUniformizer_smul_mem_iff M hπ i w).mpr hw

/-- The units of `E` normalize the lifted chain. -/
theorem liftChain_normalized (a : Eˣ) : subfieldUnits F E V a ∈ (liftChain M).stabilizer := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F E)
  obtain ⟨k, u, hu⟩ := subfieldUnit_factorization E hϖ a
  have ha : (a : E) = ((u : subfieldIntegers F E) : E) * (ϖ : E) ^ k := by
    have := congrArg (fun x : Eˣ => (x : E)) hu
    simpa [Units.val_zpow_eq_zpow_val] using this
  intro i
  refine ⟨i + k * M.period, ?_⟩
  ext v
  rw [Submodule.mem_map]
  change (∃ w, w ∈ M.lattice i ∧ (a : E) • w = v) ↔ v ∈ M.lattice (i + k * M.period)
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (units_smul_mem_iff M hϖ a ha i w).mpr hw
  · intro hv
    refine ⟨((a⁻¹ : Eˣ) : E) • v, ?_, by simp [smul_smul]⟩
    rw [← units_smul_mem_iff M hϖ a ha i, smul_smul, Units.mul_inv, one_smul]
    exact hv

/-- The filtration of the lifted chain restricts to that of the chain over `𝔬_E`. -/
theorem mem_liftChain_endFiltration_iff {k : ℤ} (y : Module.End E V) :
    y.restrictScalars F ∈ (liftChain M).endFiltration k ↔ y ∈ M.endFiltration k := Iff.rfl

end Lift

section Comparison

variable (𝓛 : LatticeChain 𝒪[F] F V) (hL : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)

/-- The `𝔬_F`-chain obtained by lifting the subfield chain of `𝓛` has the lattices of `𝓛`. -/
theorem coe_liftChain_subfieldChain_lattice (i : ℤ) :
    ((liftChain (𝓛.subfieldChain E hL)).lattice i : Set V) = 𝓛.lattice i := rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F E] in
/-- The valuation of a nonzero field element on a normalized chain is its uniformizer exponent
times the shift of the extension uniformizer. -/
theorem valuation_subfieldEmbedding {ϖ : subfieldIntegers F E} (hϖ : Irreducible ϖ) {a : Eˣ}
    {m : ℤ} {u : (subfieldIntegers F E)ˣ}
    (ha : a = subfieldIntegerUnits E u * subfieldIntegerUnit E hϖ.ne_zero ^ m) :
    𝓛.valuation (subfieldEmbedding F E V (a : E)) =
      (((𝓛.fieldShift E hL (subfieldIntegerUnit E hϖ.ne_zero)).toAdd * m : ℤ) : WithTop ℤ) := by
  have h := 𝓛.valuation_eq_shift ⟨subfieldUnits F E V a, hL a⟩
  rw [← 𝓛.fieldShift_eq_mul_of_factorization E hL hϖ.ne_zero ha]
  exact h

include hL in
/-- Valuations of a field element on two normalized chains have the same normalized value. -/
theorem exists_valuation_of_normalized (𝓛' : LatticeChain 𝒪[F] F V)
    (hL' : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛'.stabilizer) {β : E} (hβ : β ≠ 0) {n : ℤ}
    (hv : 𝓛.valuation (subfieldEmbedding F E V β) = ((-n : ℤ) : WithTop ℤ)) :
    ∃ n' : ℤ, 𝓛'.valuation (subfieldEmbedding F E V β) = ((-n' : ℤ) : WithTop ℤ) ∧
      n' * 𝓛.period = n * 𝓛'.period := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F E)
  obtain ⟨m, u, hu⟩ := subfieldUnit_factorization E hϖ (Units.mk0 β hβ)
  have h1 := valuation_subfieldEmbedding 𝓛 hL hϖ hu
  have h2 := valuation_subfieldEmbedding 𝓛' hL' hϖ hu
  simp only [Units.val_mk0] at h1 h2
  set d := (𝓛.fieldShift E hL (subfieldIntegerUnit E hϖ.ne_zero)).toAdd
  set d' := (𝓛'.fieldShift E hL' (subfieldIntegerUnit E hϖ.ne_zero)).toAdd
  have he : d * (subfieldRamificationIndex F E : ℤ) = 𝓛.period :=
    𝓛.fieldShift_uniformizer_mul_ramification E hL hϖ
  have he' : d' * (subfieldRamificationIndex F E : ℤ) = 𝓛'.period :=
    𝓛'.fieldShift_uniformizer_mul_ramification E hL' hϖ
  have hn : -n = d * m := WithTop.coe_injective (hv.symm.trans h1)
  refine ⟨-(d' * m), by rw [h2, neg_neg], ?_⟩
  rw [← he, ← he']
  have : n = -(d * m) := by omega
  rw [this]
  ring

end Comparison

section Critical

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F E] in
/-- The regular action of a generator of `E` generates the image of `E`, whose units normalize
any normalized chain on the line `E`. -/
theorem normalizingUnits_regular (C : LatticeChain 𝒪[F] F E)
    (hC : ∀ a : Eˣ, subfieldUnits F E E a ∈ C.stabilizer) {β : E}
    (hgen : Algebra.adjoin F ({β} : Set E) = ⊤) :
    NormalizingUnits C (elementAlgebra (subfieldEmbedding F E E β)) := by
  have h : elementAlgebra (subfieldEmbedding F E E β) = (subfieldEmbedding F E E).range := by
    change Algebra.adjoin F ({subfieldEmbedding F E E β} : Set (Module.End F E)) = _
    rw [← AlgHom.map_adjoin_singleton (subfieldEmbedding F E E) β, hgen, Algebra.map_top]
  rw [h]
  intro x hx hx0
  obtain ⟨a, rfl⟩ := hx
  have ha : a ≠ 0 := fun h => hx0 (by simp [h])
  exact ⟨subfieldUnits F E E (Units.mk0 a ha), rfl, hC _⟩

/-- **BK93 (1.4.13)** for a generator of `E`: on a chain normalized by `E`, the critical
exponent is the critical exponent on the line chain `{𝔭_E^i}`, scaled by the shift of an
extension uniformizer. -/
theorem criticalExponent_subfieldEmbedding_eq (𝓛 : LatticeChain 𝒪[F] F V)
    (hL : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer) {β : E}
    (hgen : Algebra.adjoin F ({β} : Set E) = ⊤) {ϖ : subfieldIntegers F E} (hϖ : Irreducible ϖ) :
    criticalExponent 𝓛 (subfieldEmbedding F E V β) =
      WithBot.map (fun k => (𝓛.fieldShift E hL (subfieldIntegerUnit E hϖ.ne_zero)).toAdd * k)
        (criticalExponent (subfieldBasisChain (F := F) (Module.Basis.singleton Unit E) hϖ)
          (subfieldEmbedding F E E β)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  let C : LatticeChain 𝒪[F] F E :=
    subfieldBasisChain (F := F) (Module.Basis.singleton Unit E) hϖ
  have hC : ∀ u : Eˣ, subfieldUnits F E E u ∈ C.stabilizer :=
    subfieldBasisChain_normalized (Module.Basis.singleton Unit E) hϖ
  have := 𝓛.finiteDimensional
  obtain ⟨q, w, hw⟩ := exists_relSplits_basis 𝓛 hπ hL
  let : Nontrivial V := 𝓛.nontrivialSpace
  let j : Fin q := Classical.choice w.index_nonempty
  let d := (𝓛.fieldShift E hL (subfieldIntegerUnit E hϖ.ne_zero)).toAdd
  let p (i : Fin q) := 𝓛.index hπ (w i) - d * C.index hπ 1
  have hd : 0 < d := 𝓛.fieldShift_uniformizer_pos E hL hϖ
  have hc : ScaledLatticeCoordinates 𝓛 C w d p :=
    scaledLatticeCoordinates_of_normalizing 𝓛 C w hL hC hπ hϖ
  have hb : diagonal F w (subfieldEmbedding F E E β) = subfieldEmbedding F E V β := by
    change diagonal F w (LinearMap.mulLeft F β) = _
    rw [diagonal_mulLeft]
  have hka := diagonalCriticalExponent 𝓛 C w d p hw hd hc ⟨j⟩ (subfieldEmbedding F E E β)
    (normalizingUnits_regular C hC hgen)
  rw [hb] at hka
  exact hka

/-- Simplicity transfers to a second normalized chain at a depth whose normalized value is not
larger (BK93 (1.4.13), printed p. 39). -/
theorem criticalExponent_lt_of_normalized (𝓛 𝓛' : LatticeChain 𝒪[F] F V)
    (hL : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)
    (hL' : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛'.stabilizer) {β : E}
    (hgen : Algebra.adjoin F ({β} : Set E) = ⊤) {r ρ : ℤ}
    (hk : criticalExponent 𝓛 (subfieldEmbedding F E V β) < ((-r : ℤ) : WithBot ℤ))
    (hρ : ρ * 𝓛.period ≤ r * 𝓛'.period) :
    criticalExponent 𝓛' (subfieldEmbedding F E V β) < ((-ρ : ℤ) : WithBot ℤ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F E)
  rw [criticalExponent_subfieldEmbedding_eq 𝓛 hL hgen hϖ] at hk
  rw [criticalExponent_subfieldEmbedding_eq 𝓛' hL' hgen hϖ]
  set d := (𝓛.fieldShift E hL (subfieldIntegerUnit E hϖ.ne_zero)).toAdd with hd_def
  set d' := (𝓛'.fieldShift E hL' (subfieldIntegerUnit E hϖ.ne_zero)).toAdd with hd'_def
  have hd : 0 < d := 𝓛.fieldShift_uniformizer_pos E hL hϖ
  have hd' : 0 < d' := 𝓛'.fieldShift_uniformizer_pos E hL' hϖ
  have he : d * (subfieldRamificationIndex F E : ℤ) = 𝓛.period :=
    𝓛.fieldShift_uniformizer_mul_ramification E hL hϖ
  have he' : d' * (subfieldRamificationIndex F E : ℤ) = 𝓛'.period :=
    𝓛'.fieldShift_uniformizer_mul_ramification E hL' hϖ
  have hepos : (0 : ℤ) < subfieldRamificationIndex F E := by
    exact_mod_cast subfieldRamificationIndex_pos' (F := F) (E := E)
  rw [← he, ← he'] at hρ
  have hρ' : ρ * d ≤ r * d' := by
    have : (ρ * d) * subfieldRamificationIndex F E ≤ (r * d') * subfieldRamificationIndex F E := by
      linarith
    exact le_of_mul_le_mul_right this hepos
  cases h : criticalExponent (subfieldBasisChain (F := F) (Module.Basis.singleton Unit E) hϖ)
      (subfieldEmbedding F E E β) with
  | bot => simp
  | coe k =>
    rw [h, WithBot.map_coe] at hk
    rw [WithBot.map_coe]
    have hk' : d * k < -r := WithBot.coe_lt_coe.mp hk
    apply WithBot.coe_lt_coe.mpr
    have h1 : d * (d' * k) < d * (-ρ) := by nlinarith
    exact lt_of_mul_lt_mul_left h1 hd.le

end Critical

end Langlands.BushnellKutzko.PureApproximation
