import Langlands.BushnellKutzko.AdjointCriticalExponent
import Langlands.BushnellKutzko.SubfieldIntegers

/-! # Multiplicative shifts of a lattice chain -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.LatticeChain

universe uO uK uV uE

variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [Field K]
  [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
  (𝓛 : LatticeChain O K V)

/-- The stabilizer valuation is additive under multiplication of stabilizer units. -/
theorem stabilizerValuation_mul (g h : 𝓛.stabilizer) :
    𝓛.stabilizerValuation (g * h) = 𝓛.stabilizerValuation g + 𝓛.stabilizerValuation h := by
  symm
  apply 𝓛.stabilizerValuation_unique (g * h) 0
  change (𝓛.lattice 0).map (((↑g : (Module.End K V)ˣ) : Module.End K V).restrictScalars O ∘ₗ
    ((↑h : (Module.End K V)ˣ) : Module.End K V).restrictScalars O) = _
  rw [Submodule.map_comp, 𝓛.map_lattice_stabilizer h, 𝓛.map_lattice_stabilizer g]
  congr 1
  omega

include 𝓛 in
/-- A strictly decreasing lattice chain has a nonzero underlying vector space. -/
theorem nontrivialSpace : Nontrivial V := by
  by_contra! h
  exact (ne_of_lt (𝓛.lattice_succ_lt 0)) (Subsingleton.elim _ _)

/-- The valuation of a shifting unit is its shift. -/
theorem valuation_eq_shift (g : 𝓛.stabilizer) :
    𝓛.valuation ((↑g : (Module.End K V)ˣ) : Module.End K V) = 𝓛.stabilizerValuation g := by
  have := 𝓛.nontrivialSpace
  have h₀ : ((↑g : (Module.End K V)ˣ) : Module.End K V) ≠ 0 := Units.ne_zero g.val
  have hset : {n : ℤ | ((↑g : (Module.End K V)ˣ) : Module.End K V) ∈ 𝓛.endFiltration n} =
      Set.Iic (𝓛.stabilizerValuation g) := by
    ext n
    change (∀ i, ∀ v ∈ 𝓛.lattice i, (g.val : Module.End K V) v ∈ 𝓛.lattice (i + n)) ↔
      n ≤ 𝓛.stabilizerValuation g
    constructor
    · intro hn
      have hmap : (𝓛.lattice 0).map ((g.val : Module.End K V).restrictScalars O) ≤
          𝓛.lattice (0 + n) := Submodule.map_le_iff_le_comap.mpr (hn 0)
      rw [𝓛.map_lattice_stabilizer g, 𝓛.strictAnti.le_iff_ge] at hmap
      simpa using hmap
    · intro hn i v hv
      have hm := Submodule.mem_map_of_mem (f := (g.val : Module.End K V).restrictScalars O) hv
      rw [𝓛.map_lattice_stabilizer g] at hm
      exact 𝓛.antitone (by omega) hm
  rw [valuation, ite_eq_right h₀, hset, csSup_Iic]

section Subfield

variable (E : Type uE) [Field E] [Algebra K E] [Module E V] [IsScalarTower K E V]
  (hE : ∀ a : Eˣ, subfieldUnits K E V a ∈ 𝓛.stabilizer)

/-- The shift of the action of a field unit in a normalizing field. -/
def fieldShift : Eˣ →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (𝓛.stabilizerValuation ⟨subfieldUnits K E V a, hE a⟩)
  map_one' := by
    change 𝓛.stabilizerValuation ⟨subfieldUnits K E V 1, hE 1⟩ = 0
    have h : (⟨subfieldUnits K E V 1, hE 1⟩ : 𝓛.stabilizer) = 1 :=
      Subtype.ext (map_one (subfieldUnits K E V))
    rw [h]
    symm
    apply 𝓛.stabilizerValuation_unique 1 0
    change (𝓛.lattice 0).map LinearMap.id = 𝓛.lattice (0 + 0)
    rw [add_zero, Submodule.map_id]
  map_mul' a b := by
    have h : (⟨subfieldUnits K E V (a * b), hE (a * b)⟩ : 𝓛.stabilizer) =
        ⟨subfieldUnits K E V a, hE a⟩ * ⟨subfieldUnits K E V b, hE b⟩ := by
      apply Subtype.ext
      exact map_mul (subfieldUnits K E V) a b
    change 𝓛.stabilizerValuation ⟨subfieldUnits K E V (a * b), hE (a * b)⟩ = _
    rw [h, 𝓛.stabilizerValuation_mul]
    rfl

/-- Multiplication by a field unit carries a lattice onto the translated lattice. -/
theorem mem_lattice_fieldShift (a : Eˣ) (i : ℤ) {v : V} :
    (a : E) • v ∈ 𝓛.lattice (i + (𝓛.fieldShift E hE a).toAdd) ↔ v ∈ 𝓛.lattice i := by
  change (a : E) • v ∈ 𝓛.lattice
    (i + 𝓛.stabilizerValuation ⟨subfieldUnits K E V a, hE a⟩) ↔ _
  rw [← 𝓛.map_lattice_stabilizer ⟨subfieldUnits K E V a, hE a⟩ i]
  let f : V →ₗ[O] V := (subfieldEmbedding K E V (a : E)).restrictScalars O
  change f v ∈ (𝓛.lattice i).map f ↔ _
  have hf : Function.Injective f := by
    intro v w heq
    have he := congrArg (fun x : V => ((a⁻¹ : Eˣ) : E) • x) heq
    simpa [f, subfieldEmbedding_apply, smul_smul] using he
  constructor
  · rintro ⟨w, hw, heq⟩
    exact hf heq ▸ hw
  · exact Submodule.mem_map_of_mem

variable [Algebra O E] [IsScalarTower O E V]

/-- An integral field unit has nonnegative shift, by its monic polynomial relation. -/
theorem fieldShift_nonneg_of_integral (a : Eˣ) (ha : IsIntegral O (a : E)) :
    0 ≤ (𝓛.fieldShift E hE a).toAdd := by
  let d : ℤ := (𝓛.fieldShift E hE a).toAdd
  by_contra! hd
  obtain ⟨p, hp, hroot⟩ := ha
  change Polynomial.aeval (a : E) p = 0 at hroot
  have hrel := congrArg (fun f : Polynomial O => Polynomial.aeval (a : E) f) hp.as_sum
  simp only [map_add, map_sum, map_pow, Polynomial.aeval_X, map_mul,
    Polynomial.aeval_C] at hrel
  rw [hroot] at hrel
  have heq : (a : E) ^ p.natDegree =
      -(∑ j ∈ Finset.range p.natDegree, algebraMap O E (p.coeff j) * (a : E) ^ j) := by
    exact (eq_neg_of_add_eq_zero_left hrel.symm)
  have hs (n : ℕ) : (𝓛.fieldShift E hE (a ^ n)).toAdd = (n : ℤ) * d := by
    simp [d, toAdd_pow]
  have hle : 𝓛.lattice (0 + (p.natDegree : ℤ) * d) ≤
      𝓛.lattice (0 + ((p.natDegree : ℤ) * d - d)) := by
    intro w hw
    let v : V := ((a⁻¹ : Eˣ) : E) ^ p.natDegree • w
    have hvw : (a : E) ^ p.natDegree • v = w := by
      simp only [v, smul_smul, ← mul_pow, Units.mul_inv, one_pow, one_smul]
    have hv : v ∈ 𝓛.lattice 0 := by
      apply (𝓛.mem_lattice_fieldShift E hE (a ^ p.natDegree) 0).mp
      simpa only [hs, Units.val_pow_eq_pow_val, hvw] using hw
    rw [← hvw, heq, neg_smul, Finset.sum_smul]
    apply neg_mem
    apply Submodule.sum_mem
    intro j hj
    rw [mul_smul, algebraMap_smul]
    apply Submodule.smul_mem
    apply 𝓛.antitone _
      (show (a : E) ^ j • v ∈ 𝓛.lattice (0 + (j : ℤ) * d) by
        simpa only [hs, Units.val_pow_eq_pow_val] using
          (𝓛.mem_lattice_fieldShift E hE (a ^ j) 0).mpr hv)
    have hj' : (j : ℤ) ≤ (p.natDegree : ℤ) - 1 := by
      have := Finset.mem_range.mp hj
      omega
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hj') hd.le]
  exact (not_le_of_gt (𝓛.strictAnti (by omega))) hle

end Subfield

end Langlands.BushnellKutzko.LatticeChain
