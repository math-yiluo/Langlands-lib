import Langlands.BushnellKutzko.CorestrictionIntegers
import Langlands.BushnellKutzko.SubfieldValuationShifts
import Langlands.BushnellKutzko.SplittingBasis

/-! # Indices for a normalizing field and uniqueness on one field line -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.PureApproximation

universe uF uE uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type uE} [Field E] [Algebra F E] [FiniteDimensional F E]
  {V : Type uV} [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]
  (A : LatticeChain 𝒪[F] F V) (hA : ∀ g : Eˣ, subfieldUnits F E V g ∈ A.stabilizer)
  {π : 𝒪[F]} (hπ : Irreducible π)

omit [FiniteDimensional F E] in
/-- The index of a nonzero vector increases by the field shift of the scalar. -/
theorem index_smul_unit (g : Eˣ) {v : V} (hv : v ≠ 0) :
    A.index hπ ((g : E) • v) = A.index hπ v + (A.fieldShift E hA g).toAdd := by
  refine A.index_eq_of_forall hπ (smul_ne_zero g.ne_zero hv) ?_
  intro i
  let d := (A.fieldShift E hA g).toAdd
  have h := A.mem_lattice_fieldShift E hA g (i - d) (v := v)
  change ((g : E) • v ∈ A.lattice ((i - d) + d) ↔ v ∈ A.lattice (i - d)) at h
  rw [sub_add_cancel, A.mem_iff_le_index hπ hv] at h
  exact h.trans (by omega)

variable {ϖ : subfieldIntegers F E} (hϖ : Irreducible ϖ)

/-- On a field line, the uniformizer of the normalizing field shifts a strict chain by one. -/
theorem uniformizerShift_eq_one_of_cyclic {v : V} (hv : v ≠ 0)
    (hspan : ∀ x : V, ∃ a : E, a • v = x) :
    (A.fieldShift E hA (subfieldIntegerUnit E hϖ.ne_zero)).toAdd = 1 := by
  obtain ⟨π₀, hπ₀⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  let i := A.index hπ₀ v + 1
  obtain ⟨x, hx, hxn⟩ := (SetLike.lt_iff_le_and_exists.mp (A.lattice_succ_lt i)).2
  have hxne : x ≠ 0 := fun e => hxn (e.symm ▸ zero_mem _)
  have h₁ := (A.mem_iff_le_index hπ₀ hxne i).mp hx
  have h₂ : ¬ i + 1 ≤ A.index hπ₀ x :=
    fun h => hxn ((A.mem_iff_le_index hπ₀ hxne (i + 1)).mpr h)
  have hidx : A.index hπ₀ x = i := by omega
  obtain ⟨a, ha⟩ := hspan x
  have hane : a ≠ 0 := fun e => hxne (by rw [← ha, e, zero_smul])
  let g := Units.mk0 a hane
  have hxg : (g : E) • v = x := ha
  obtain ⟨m, u, hu⟩ := subfieldUnit_factorization E hϖ g
  have he := index_smul_unit A hA hπ₀ g hv
  rw [hxg, hidx, A.fieldShift_eq_mul_of_factorization E hA hϖ.ne_zero hu] at he
  have hd : (A.fieldShift E hA (subfieldIntegerUnit E hϖ.ne_zero)).toAdd * m = 1 := by
    change A.index hπ₀ v + 1 = A.index hπ₀ v + _ at he
    omega
  have hpos : 0 < (A.fieldShift E hA (subfieldIntegerUnit E hϖ.ne_zero)).toAdd :=
    A.fieldShift_uniformizer_pos E hA hϖ
  rcases Int.isUnit_iff.mp (IsUnit.of_mul_eq_one m hd) with h | h
  · exact h
  · rw [h] at hpos
    omega

variable (B : LatticeChain 𝒪[F] F V)

/-- Strict chains on an `E`-line normalized by `Eˣ` coincide up to an integer translation.
Here `F` is a nonarchimedean local field and `E/F` is finite; every hypothesis is a binder of
this definition, not a section variable. -/
def LineChainTranslationStatement {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {E : Type uE} [Field E] [Algebra F E] [FiniteDimensional F E]
    {V : Type uV} [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]
    (A B : LatticeChain 𝒪[F] F V) : Prop :=
  (∀ g : Eˣ, subfieldUnits F E V g ∈ A.stabilizer) →
  (∀ g : Eˣ, subfieldUnits F E V g ∈ B.stabilizer) →
  (∃ v : V, v ≠ 0 ∧ ∀ x : V, ∃ a : E, a • v = x) →
    ∃ t : ℤ, ∀ i : ℤ, A.lattice i = B.lattice (i + t)

/-- Compare the indices of every nonzero vector relative to a common generator of the line. -/
theorem lineChainTranslation : LineChainTranslationStatement (E := E) A B := by
  intro hA' hB ⟨v, hv, hspan⟩
  obtain ⟨π', hπ'⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F E)
  have hA1 := uniformizerShift_eq_one_of_cyclic A hA' hϖ' hv hspan
  have hB1 := uniformizerShift_eq_one_of_cyclic B hB hϖ' hv hspan
  let t := B.index hπ' v - A.index hπ' v
  refine ⟨t, fun i => ?_⟩
  ext x
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨a, ha⟩ := hspan x
  have hane : a ≠ 0 := fun e => hx (by rw [← ha, e, zero_smul])
  let g := Units.mk0 a hane
  have hxg : (g : E) • v = x := ha
  obtain ⟨m, u, hu⟩ := subfieldUnit_factorization E hϖ' g
  have hAx := index_smul_unit A hA' hπ' g hv
  have hBx := index_smul_unit B hB hπ' g hv
  rw [hxg, A.fieldShift_eq_mul_of_factorization E hA' hϖ'.ne_zero hu, hA1, one_mul] at hAx
  rw [hxg, B.fieldShift_eq_mul_of_factorization E hB hϖ'.ne_zero hu, hB1, one_mul] at hBx
  change x ∈ A.lattice i ↔ x ∈ B.lattice (i + t)
  rw [A.mem_iff_le_index hπ' hx, B.mem_iff_le_index hπ' hx, hAx, hBx]
  dsimp only [t]
  omega

end Langlands.BushnellKutzko.PureApproximation
