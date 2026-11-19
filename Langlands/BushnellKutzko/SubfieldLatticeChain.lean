import Langlands.BushnellKutzko.LatticeChainShifts
import Langlands.BushnellKutzko.SubfieldIntegerArithmetic

/-! # A lattice chain with scalars from a normalizing field -/

noncomputable section

open ValuativeRel IsDiscreteValuationRing
open scoped Pointwise

namespace Langlands.BushnellKutzko.LatticeChain

universe uF uV uE

variable {F : Type uF} [Field F] [ValuativeRel F]
  {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)
  (E : Type uE) [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
  (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)

local notation "𝒪ₑ[" F "," E "]" => subfieldIntegers F E
local notation "shiftₑ(" L "," E "," h "," a ")" =>
  Multiplicative.toAdd (LatticeChain.fieldShift L E h a)

include 𝓛 in
/-- A field acting compatibly on a lattice chain is finite over the base. -/
theorem finiteDimensional_subfield : FiniteDimensional F E := by
  have := 𝓛.nontrivialSpace
  have := 𝓛.finiteDimensional
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let f : E →ₗ[F] V :=
    { toFun := fun a => a • v
      map_add' := fun a b => add_smul a b v
      map_smul' := fun c a => smul_assoc c a v }
  exact FiniteDimensional.of_injective f (smul_left_injective E hv)

include hE in
/-- Each base lattice is stable under the integral closure. -/
theorem subfieldInteger_smul_mem (i : ℤ) (a : 𝒪ₑ[F,E]) {v : V}
    (hv : v ∈ 𝓛.lattice i) : (a : E) • v ∈ 𝓛.lattice i := by
  by_cases ha : (a : E) = 0
  · rw [ha, zero_smul]
    exact (𝓛.lattice i).zero_mem
  let u := Units.mk0 (a : E) ha
  have h := 𝓛.fieldShift_nonneg_of_integral E hE u a.property
  exact 𝓛.antitone (le_add_of_nonneg_right h) ((𝓛.mem_lattice_fieldShift E hE u i).mpr hv)

/-- The lattice with the same vectors and the action by the extension integer ring. -/
def subfieldLattice (i : ℤ) : Submodule 𝒪ₑ[F,E] V where
  carrier := 𝓛.lattice i
  add_mem' := (𝓛.lattice i).add_mem'
  zero_mem' := (𝓛.lattice i).zero_mem'
  smul_mem' := fun a _ hv => 𝓛.subfieldInteger_smul_mem E hE i a hv

@[simp] theorem mem_subfieldLattice (i : ℤ) (v : V) :
    v ∈ 𝓛.subfieldLattice E hE i ↔ v ∈ 𝓛.lattice i := Iff.rfl

/-- The scalar extension of each lattice is still finitely generated and spanning. -/
theorem isLattice_subfield (i : ℤ) : (𝓛.subfieldLattice E hE i).IsLattice E := by
  constructor
  · have hL : Module.Finite 𝒪[F] (𝓛.lattice i) := Module.Finite.iff_fg.mpr (𝓛.fg_lattice i)
    have : Module.Finite 𝒪[F] (𝓛.subfieldLattice E hE i) := hL
    exact Module.Finite.iff_fg.mp
      (Module.Finite.of_restrictScalars_finite 𝒪[F] 𝒪ₑ[F,E] (𝓛.subfieldLattice E hE i))
  · apply eq_top_iff.mpr
    intro v _
    have hle : Submodule.span F (𝓛.lattice i : Set V) ≤
        (Submodule.span E (𝓛.subfieldLattice E hE i : Set V)).restrictScalars F :=
      Submodule.span_le.mpr Submodule.subset_span
    exact hle ((𝓛.isLattice i).span_eq_top ▸ Submodule.mem_top)

/-- Units of the extension integer ring have zero shift. -/
theorem fieldShift_integerUnit (u : 𝒪ₑ[F,E]ˣ) :
    shiftₑ(𝓛,E,hE,Units.map (algebraMap 𝒪ₑ[F,E] E).toMonoidHom u) = 0 := by
  let a := Units.map (algebraMap 𝒪ₑ[F,E] E).toMonoidHom u
  have h₁ := 𝓛.fieldShift_nonneg_of_integral E hE a u.val.property
  have h₂ := 𝓛.fieldShift_nonneg_of_integral E hE a⁻¹ (u⁻¹ : 𝒪ₑ[F,E]ˣ).val.property
  change 0 ≤ shiftₑ(𝓛,E,hE,a) at h₁
  change 0 ≤ shiftₑ(𝓛,E,hE,a⁻¹) at h₂
  rw [map_inv] at h₂
  change 0 ≤ -shiftₑ(𝓛,E,hE,a) at h₂
  exact le_antisymm (neg_nonneg.mp h₂) h₁

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- A base uniformizer acts on the chain by one base period. -/
theorem fieldShift_baseUniformizer {π : 𝒪[F]} (hπ : Irreducible π) :
    shiftₑ(𝓛,E,hE,Units.mk0 (algebraMap F E (π : F)) (by
      intro h
      exact hπ.ne_zero (Subtype.ext ((algebraMap F E).injective (h.trans (map_zero _).symm)))))
        = 𝓛.period := by
  set a : Eˣ := Units.mk0 (algebraMap F E (π : F)) (by
    intro h
    exact hπ.ne_zero (Subtype.ext ((algebraMap F E).injective (h.trans (map_zero _).symm))))
  change 𝓛.stabilizerValuation ⟨subfieldUnits F E V a, hE a⟩ = _
  symm
  apply 𝓛.stabilizerValuation_unique _ 0
  rw [𝓛.lattice_add_period, jacobson_integer_eq_maximalIdeal, hπ.maximalIdeal_eq,
    Submodule.ideal_span_singleton_smul, Submodule.pointwise_smul_def]
  congr 1
  ext v
  change algebraMap F E (π : F) • v = π • v
  exact algebraMap_smul E _ _

variable [IsDiscreteValuationRing 𝒪ₑ[F,E]]

/-- The shifts of the two uniformizers differ by the ramification index. -/
theorem fieldShift_uniformizer_mul_ramification {ϖ : 𝒪ₑ[F,E]} (hϖ : Irreducible ϖ) :
    shiftₑ(𝓛,E,hE,Units.mk0 (ϖ : E) (fun h => hϖ.ne_zero (Subtype.ext h))) *
      (subfieldRamificationIndex F E : ℤ) = 𝓛.period := by
  obtain ⟨π, hπ⟩ := exists_irreducible 𝒪[F]
  obtain ⟨u, hu⟩ := baseUniformizer_factorization F E hπ hϖ
  let a := Units.mk0 (ϖ : E) (fun h => hϖ.ne_zero (Subtype.ext h))
  let b := Units.mk0 (algebraMap F E (π : F)) (by
    intro h
    exact hπ.ne_zero (Subtype.ext ((algebraMap F E).injective (h.trans (map_zero _).symm))))
  have hab : b = Units.map (algebraMap 𝒪ₑ[F,E] E).toMonoidHom u *
      a ^ subfieldRamificationIndex F E := by
    apply Units.ext
    exact congrArg (fun x : 𝒪ₑ[F,E] => (x : E)) hu
  have hb : shiftₑ(𝓛,E,hE,b) = 𝓛.period := 𝓛.fieldShift_baseUniformizer E hE hπ
  rw [hab, map_mul, map_pow] at hb
  change shiftₑ(𝓛,E,hE,Units.map (algebraMap 𝒪ₑ[F,E] E).toMonoidHom u) +
    ((𝓛.fieldShift E hE a) ^ subfieldRamificationIndex F E).toAdd = 𝓛.period at hb
  rw [𝓛.fieldShift_integerUnit E hE, zero_add, Int.toAdd_pow] at hb
  exact hb

/-- Every extension uniformizer has positive shift. -/
theorem fieldShift_uniformizer_pos {ϖ : 𝒪ₑ[F,E]} (hϖ : Irreducible ϖ) :
    0 < shiftₑ(𝓛,E,hE,Units.mk0 (ϖ : E) (fun h => hϖ.ne_zero (Subtype.ext h))) := by
  have h := 𝓛.fieldShift_uniformizer_mul_ramification E hE hϖ
  have hp : (0 : ℤ) < 𝓛.period := by exact_mod_cast 𝓛.period_pos
  by_contra! hn
  exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hn (Int.natCast_nonneg _))) (h ▸ hp)

/-- The original lattices form a periodic chain over the extension integers. -/
def subfieldChain : LatticeChain 𝒪ₑ[F,E] E V where
  lattice := 𝓛.subfieldLattice E hE
  isLattice := 𝓛.isLattice_subfield E hE
  lattice_succ_lt i := by
    exact SetLike.lt_iff_le_and_exists.mpr
      (SetLike.lt_iff_le_and_exists.mp (𝓛.lattice_succ_lt i))
  exists_period := by
    obtain ⟨ϖ, hϖ⟩ := exists_irreducible 𝒪ₑ[F,E]
    let a := Units.mk0 (ϖ : E) (fun h => hϖ.ne_zero (Subtype.ext h))
    have hpos : 0 < shiftₑ(𝓛,E,hE,a) := 𝓛.fieldShift_uniformizer_pos E hE hϖ
    refine ⟨(shiftₑ(𝓛,E,hE,a)).toNat, by omega, fun i => ?_⟩
    rw [Int.toNat_of_nonneg hpos.le, IsLocalRing.ringJacobson_eq_maximalIdeal,
      hϖ.maximalIdeal_eq, Submodule.ideal_span_singleton_smul]
    ext v
    rw [Submodule.mem_smul_pointwise_iff_exists]
    change v ∈ 𝓛.lattice (i + shiftₑ(𝓛,E,hE,a)) ↔
      ∃ w ∈ 𝓛.lattice i, (a : E) • w = v
    constructor
    · intro hv
      let w := ((a⁻¹ : Eˣ) : E) • v
      have hw : (a : E) • w = v := by simp only [w, smul_smul, Units.mul_inv, one_smul]
      exact ⟨w, (𝓛.mem_lattice_fieldShift E hE a i).mp (hw ▸ hv), hw⟩
    · rintro ⟨w, hw, rfl⟩
      exact (𝓛.mem_lattice_fieldShift E hE a i).mpr hw

@[simp] theorem mem_subfieldChain_lattice (i : ℤ) (v : V) :
    v ∈ (𝓛.subfieldChain E hE).lattice i ↔ v ∈ 𝓛.lattice i := Iff.rfl

end Langlands.BushnellKutzko.LatticeChain
