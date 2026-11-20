import Langlands.BushnellKutzko.StratumEquivalenceShift

/-! # Ramification index and residue degree from `𝔅 + 𝔓` (BK93 (2.1.4)(iii))

Helper results for `StratumEquivalenceStatement`. Let `E` be a finite field extension of `F`
acting on `V`, with `E^×` normalizing an `𝔬_F`-lattice chain `𝓛`, and let
`𝔅_E = 𝔄 ∩ End_E(V)` and `M = 𝔅_E + 𝔓`. Both `e(E|F)` and `f(E|F)` are recovered from `𝓛`
and `M` alone:

* the integers `d` for which `x ↦ [x L_j ⊆ L_{j+1}]` is `d`-periodic on `M` are exactly the
  shifts of elements of `E^×`, that is, the multiples of `e' = e(𝓛)/e(E|F)`;
* with `Z(M) = {x ∈ 𝔄 : [x, M] L_0 ⊆ L_1}` and `K = {x : x L_0 ⊆ L_1}`, the quotient
  `Z(M)/(Z(M) ∩ K)` is isomorphic to `𝔬_E/𝔭_E` as an `𝔬_F`-module.

This file proves the first point and deduces that two such fields with the same `M` have the
same ramification index; the second point and the residue degree are in
`StratumEquivalenceResidueDegree`.
-/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

namespace StratumEquivalence

universe uF uV uE uE'

variable {F : Type uF} [Field F] [ValuativeRel F]
  {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)

local notation "L" => 𝓛.lattice
local notation "P" => 𝓛.endFiltration

section Commutant

variable (E : Type uE) [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]

/-- The endomorphisms commuting with the action of `E`, that is, `End_E(V)`. -/
def fieldCommutant : Submodule 𝒪[F] (Module.End F V) where
  carrier := {x | ∀ (a : E) (v : V), x (a • v) = a • x v}
  add_mem' := by
    intro x y hx hy a v
    simp only [LinearMap.add_apply, hx a v, hy a v, smul_add]
  zero_mem' := by
    intro a v
    simp
  smul_mem' := by
    intro c x hx a v
    have h : ∀ w : V, c • w = (c : F) • w := fun _ => rfl
    simp only [LinearMap.smul_apply, h, hx a v]
    exact smul_comm (c : F) a (x v)

/-- `𝔅_E = 𝔄 ∩ End_E(V)`. -/
def fieldOrder : Submodule 𝒪[F] (Module.End F V) :=
  P 0 ⊓ fieldCommutant E

end Commutant

/-- `x` maps `L_j` into `L_{j+1}`. -/
def LayerNull (x : Module.End F V) (j : ℤ) : Prop :=
  ∀ v ∈ L j, x v ∈ L (j + 1)

/-- `d` is a period of the layer-null condition on `M`. -/
def IsLayerPeriod (M : Submodule 𝒪[F] (Module.End F V)) (d : ℤ) : Prop :=
  ∀ j : ℤ, ∀ x ∈ M, LayerNull 𝓛 x j ↔ LayerNull 𝓛 x (j + d)

theorem layerNull_add_iff {x p : Module.End F V} (hp : p ∈ P 1) (j : ℤ) :
    LayerNull 𝓛 (x + p) j ↔ LayerNull 𝓛 x j := by
  have hpv : ∀ v ∈ L j, p v ∈ L (j + 1) := fun v hv => hp j v hv
  constructor
  · intro h v hv
    have := sub_mem (h v hv) (hpv v hv)
    rwa [LinearMap.add_apply, add_sub_cancel_right] at this
  · intro h v hv
    rw [LinearMap.add_apply]
    exact add_mem (h v hv) (hpv v hv)

variable {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
  (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)

/-- An element commuting with `E` has the same layer-null behaviour at `j` and at
`j + shift a`. -/
theorem layerNull_iff_of_commute {x : Module.End F V} (hx : x ∈ fieldCommutant E)
    {a : E} (ha : a ≠ 0) (j : ℤ) :
    LayerNull 𝓛 x j ↔ LayerNull 𝓛 x (j + shift 𝓛 hE a) := by
  have hx' : ∀ (c : E) (v : V), x (c • v) = c • x v := hx
  constructor
  · intro h v hv
    have hv' : a⁻¹ • v ∈ L j := by
      rw [← smul_mem_shift_iff 𝓛 hE ha j, smul_inv_smul₀ ha]
      exact hv
    have hxv := h _ hv'
    rw [← smul_mem_shift_iff 𝓛 hE ha, ← hx', smul_inv_smul₀ ha] at hxv
    rwa [show j + shift 𝓛 hE a + 1 = j + 1 + shift 𝓛 hE a by ring]
  · intro h v hv
    have hav : a • v ∈ L (j + shift 𝓛 hE a) := (smul_mem_shift_iff 𝓛 hE ha j v).mpr hv
    have hxv := h _ hav
    rw [hx', show j + shift 𝓛 hE a + 1 = j + 1 + shift 𝓛 hE a by ring,
      smul_mem_shift_iff 𝓛 hE ha] at hxv
    exact hxv

section Basis

variable {n : ℕ} {w : Module.Basis (Fin n) E V}

variable (F) in
/-- The rank-one map `v ↦ w_k^*(v) c⁻¹ y`, as an `F`-endomorphism. -/
def rankOne (w : Module.Basis (Fin n) E V) (k : Fin n) (c : E) (y : V) : Module.End F V :=
  ((w.coord k).smulRight (c⁻¹ • y)).restrictScalars F

omit [ValuativeRel F] in
theorem rankOne_apply (k : Fin n) (c : E) (y v : V) :
    rankOne F w k c y v = w.coord k v • c⁻¹ • y :=
  rfl

omit [ValuativeRel F] in
theorem rankOne_apply_basis (k : Fin n) {c : E} (hc : c ≠ 0) (y : V) :
    rankOne F w k c y (c • w k) = y := by
  rw [rankOne_apply, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_eq_same, smul_eq_mul, mul_one, smul_inv_smul₀ hc]

theorem rankOne_mem_fieldCommutant (k : Fin n) (c : E) (y : V) :
    rankOne F w k c y ∈ fieldCommutant E := by
  intro a v
  exact ((w.coord k).smulRight (c⁻¹ • y)).map_smul a v

theorem ExactDepth.ne_zero {v : V} {i : ℤ} (hv : ExactDepth 𝓛 v i) : v ≠ 0 := by
  rintro rfl
  exact hv.2 (zero_mem _)

include hE in
/-- For `c • w_k` of exact depth `0` and `y ∈ L_0`, the rank-one map lies in `𝔅_E`. -/
theorem rankOne_mem_fieldOrder (hw : RelativeSplits (E := E) 𝓛 w) {k : Fin n} {c : E}
    (hu : ExactDepth 𝓛 (c • w k) 0) {y : V} (hy : y ∈ L 0) :
    rankOne F w k c y ∈ fieldOrder 𝓛 E := by
  refine ⟨fun i v hv => ?_, rankOne_mem_fieldCommutant k c y⟩
  have hc : c ≠ 0 := by
    rintro rfl
    exact hu.ne_zero 𝓛 (zero_smul E _)
  rw [rankOne_apply, smul_smul, add_zero]
  by_cases hs : w.coord k v * c⁻¹ = 0
  · rw [hs, zero_smul]
    exact zero_mem _
  have hsu : (w.coord k v * c⁻¹) • (c • w k) ∈ L i := by
    rw [smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
    exact coord_smul_mem 𝓛 hw hv k
  have hle := (hu.smul 𝓛 hE hs).le 𝓛 hsu
  exact smul_mem_of_shift_le 𝓛 hE hs hle hy

end Basis

section LocalField

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F V]

include hE in
/-- A splitting basis vector, scaled to have exact depth `0`. -/
theorem exists_basis_depth_zero :
    ∃ (n : ℕ) (w : Module.Basis (Fin n) E V) (k : Fin n) (c : E),
      RelativeSplits (E := E) 𝓛 w ∧ ExactDepth 𝓛 (c • w k) 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨n, w, hw⟩ := exists_relative_splitting_basis 𝓛 hϖ hE
  obtain ⟨k, c, h1, h2⟩ := exists_scaled_basis_at_depth 𝓛 hw 0
  exact ⟨n, w, k, c, hw, h1, h2⟩

/-- The layer periods of `𝔅_E + 𝔓` are exactly the shifts of elements of `E^×`. -/
theorem isLayerPeriod_iff (d : ℤ) :
    IsLayerPeriod 𝓛 (fieldOrder 𝓛 E ⊔ P 1) d ↔ ∃ a : E, a ≠ 0 ∧ shift 𝓛 hE a = d := by
  constructor
  · intro hd
    obtain ⟨n, w, k, c, hw, hu⟩ := exists_basis_depth_zero 𝓛 hE
    have hc : c ≠ 0 := by
      rintro rfl
      exact hu.ne_zero 𝓛 (zero_smul E _)
    let p := rankOne F w k c (c • w k)
    have hp : p ∈ fieldOrder 𝓛 E ⊔ P 1 :=
      Submodule.mem_sup_left (rankOne_mem_fieldOrder 𝓛 hE hw hu hu.1)
    have hnot : ¬ LayerNull 𝓛 p 0 := by
      intro h
      have := h _ hu.1
      rw [rankOne_apply_basis k hc] at this
      exact hu.2 this
    rw [hd 0 p hp, zero_add] at hnot
    simp only [LayerNull, not_forall] at hnot
    obtain ⟨v, hv, hpv⟩ := hnot
    let t := w.coord k v
    have hpv' : p v = t • w k := by
      change w.coord k v • c⁻¹ • c • w k = t • w k
      rw [inv_smul_smul₀ hc]
    rw [hpv'] at hpv
    have ht : t • w k ∈ L d := coord_smul_mem 𝓛 hw hv k
    let a := t * c⁻¹
    have hau : a • (c • w k) = t • w k := by
      simp only [a, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
    have ha : a ≠ 0 := by
      intro ha
      rw [ha, zero_smul] at hau
      rw [← hau] at hpv
      exact hpv (zero_mem _)
    refine ⟨a, ha, ?_⟩
    have h1 := hu.smul 𝓛 hE ha
    rw [hau, zero_add] at h1
    exact h1.unique 𝓛 ⟨ht, hpv⟩
  · rintro ⟨a, ha, rfl⟩ j x hx
    obtain ⟨b, hb, p, hp, rfl⟩ := Submodule.mem_sup.mp hx
    rw [layerNull_add_iff 𝓛 hp, layerNull_add_iff 𝓛 hp]
    exact layerNull_iff_of_commute 𝓛 hE hb.2 ha j

variable [FiniteDimensional F E]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F V]
  [FiniteDimensional F E] in
/-- Every multiple of `e'` is a shift. -/
theorem exists_shift_eq_mul {ϖ : subfieldIntegers F E} (hϖ : Irreducible ϖ) (m : ℤ) :
    ∃ a : E, a ≠ 0 ∧ shift 𝓛 hE a = m * shift 𝓛 hE (ϖ : E) := by
  have hϖ0 : (ϖ : E) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · exact ⟨(ϖ : E) ^ n, pow_ne_zero n hϖ0, shift_pow 𝓛 hE hϖ0 n⟩
  · refine ⟨((ϖ : E) ^ n)⁻¹, inv_ne_zero (pow_ne_zero n hϖ0), ?_⟩
    rw [shift_inv 𝓛 hE (pow_ne_zero n hϖ0), shift_pow 𝓛 hE hϖ0 n, neg_mul]

/-- The layer periods of `𝔅_E + 𝔓` are the multiples of `e'`. -/
theorem isLayerPeriod_iff_dvd {ϖ : subfieldIntegers F E} (hϖ : Irreducible ϖ) (d : ℤ) :
    IsLayerPeriod 𝓛 (fieldOrder 𝓛 E ⊔ P 1) d ↔ shift 𝓛 hE (ϖ : E) ∣ d := by
  rw [isLayerPeriod_iff 𝓛 hE]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact shift_uniformizer_dvd 𝓛 hE hϖ ha
  · rintro ⟨m, rfl⟩
    rw [mul_comm]
    exact exists_shift_eq_mul 𝓛 hE hϖ m

/-- Two normalizing fields with the same `𝔅 + 𝔓` have uniformizers of the same shift. -/
theorem shift_uniformizer_eq_of_sup_eq
    {E' : Type uE'} [Field E'] [Algebra F E'] [Module E' V] [IsScalarTower F E' V]
    [FiniteDimensional F E']
    (hE' : ∀ a : E'ˣ, subfieldUnits F E' V a ∈ 𝓛.stabilizer)
    (hM : fieldOrder 𝓛 E ⊔ P 1 = fieldOrder 𝓛 E' ⊔ P 1)
    {ϖ : subfieldIntegers F E} (hϖ : Irreducible ϖ)
    {ϖ' : subfieldIntegers F E'} (hϖ' : Irreducible ϖ') :
    shift 𝓛 hE (ϖ : E) = shift 𝓛 hE' (ϖ' : E') := by
  have h1 : shift 𝓛 hE (ϖ : E) ∣ shift 𝓛 hE' (ϖ' : E') := by
    rw [← isLayerPeriod_iff_dvd 𝓛 hE hϖ, hM, isLayerPeriod_iff_dvd 𝓛 hE' hϖ']
  have h2 : shift 𝓛 hE' (ϖ' : E') ∣ shift 𝓛 hE (ϖ : E) := by
    rw [← isLayerPeriod_iff_dvd 𝓛 hE' hϖ', ← hM, isLayerPeriod_iff_dvd 𝓛 hE hϖ]
  exact Int.dvd_antisymm (shift_uniformizer_pos 𝓛 hE hϖ).le
    (shift_uniformizer_pos 𝓛 hE' hϖ').le h1 h2

include hE in
/-- Two normalizing fields with the same `𝔅 + 𝔓` have the same ramification index. -/
theorem ramificationIndex_eq_of_sup_eq
    {E' : Type uE'} [Field E'] [Algebra F E'] [Module E' V] [IsScalarTower F E' V]
    [FiniteDimensional F E']
    (hE' : ∀ a : E'ˣ, subfieldUnits F E' V a ∈ 𝓛.stabilizer)
    (hM : fieldOrder 𝓛 E ⊔ P 1 = fieldOrder 𝓛 E' ⊔ P 1) :
    subfieldRamificationIndex F E = subfieldRamificationIndex F E' := by
  have := subfieldIntegers_isDiscreteValuationRing F E
  have := subfieldIntegers_isDiscreteValuationRing F E'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F E)
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F E')
  have h := ramificationIndex_mul_shift 𝓛 hE hϖ
  have h' := ramificationIndex_mul_shift 𝓛 hE' hϖ'
  rw [shift_uniformizer_eq_of_sup_eq 𝓛 hE hE' hM hϖ hϖ', ← h'] at h
  have hpos := shift_uniformizer_pos 𝓛 hE' hϖ'
  exact_mod_cast mul_right_cancel₀ hpos.ne' h

end LocalField

end StratumEquivalence

end Langlands.BushnellKutzko
