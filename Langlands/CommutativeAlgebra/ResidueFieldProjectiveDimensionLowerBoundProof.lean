import Langlands.CommutativeAlgebra.ResidueFieldProjectiveDimensionLowerBoundStatement
import Langlands.CommutativeAlgebra.MinimalResolutionComparison
import Langlands.CommutativeAlgebra.MinimalMaximalIdealGenerators
import Langlands.CommutativeAlgebra.FinitePiIdealMultiples
import Langlands.CommutativeAlgebra.FiniteKoszulComplex

/-! # The residue-field projective-dimension lower bound -/

universe u v

namespace Langlands.CommutativeAlgebra

open IsLocalRing CategoryTheory

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {ι : Type v} [Fintype ι] [LinearOrder ι]

omit [IsLocalRing R] [Fintype ι] in
lemma koszulSign_mul_self (s : Finset ι) (i : ι) :
    koszulSign R s i * koszulSign R s i = 1 := by
  unfold koszulSign
  rw [← mul_pow]
  simp

/-- Cotangent independence makes the Koszul differential detect the maximal
ideal multiple from membership in its square. -/
theorem finiteKoszulDifferential_detect
    (a : ι → maximalIdeal R)
    (ha : LinearIndependent (ResidueField R)
      (fun i ↦ (maximalIdeal R).toCotangent (a i)))
    (n : ℕ) (x : FiniteKoszulModule R ι (n + 1))
    (hx : finiteKoszulDifferential (fun i ↦ (a i : R)) n x ∈
      maximalIdeal R • (maximalIdeal R •
        (⊤ : Submodule R (FiniteKoszulModule R ι n)))) :
    x ∈ maximalIdeal R • (⊤ : Submodule R (FiniteKoszulModule R ι (n + 1))) := by
  classical
  rw [mem_ideal_smul_top_pi_iff]
  intro s
  have hne : s.val.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨j, hj⟩ := hne
  let t : {t : Finset ι // t.card = n} :=
    ⟨s.val.erase j, by rw [Finset.card_erase_of_mem hj, s.property]; omega⟩
  let c : ι → R := fun i ↦
    if i ∈ t.val then 0 else koszulSign R t.val i *
      koszulExtend (n + 1) x (insert i t.val)
  have hsum : ∑ i, c i * (a i : R) ∈ maximalIdeal R ^ 2 := by
    have ht := (mem_ideal_smul_smul_top_pi_iff (maximalIdeal R) _).mp hx t
    convert ht using 1
    change (∑ i, c i * (a i : R)) =
      ∑ i, koszulCoefficient (fun i ↦ (a i : R)) t.val i *
        koszulExtend (n + 1) x (insert i t.val)
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ t.val <;> simp [c, koszulCoefficient, hi] <;> ring
  have hc := coefficients_mem_maximalIdeal_of_cotangent_independent a ha c hsum j
  have hjt : j ∉ t.val := Finset.notMem_erase j s.val
  have htj : insert j t.val = s.val := Finset.insert_erase hj
  have hcard : (insert j t.val).card = n + 1 := by rw [htj, s.property]
  have heval : koszulExtend (n + 1) x (insert j t.val) = x s := by
    simp only [koszulExtend, LinearMap.coe_mk, AddHom.coe_mk, hcard, ↓reduceDIte]
    congr 1
    exact Subtype.ext htj
  change (if j ∈ t.val then 0 else koszulSign R t.val j *
    koszulExtend (n + 1) x (insert j t.val)) ∈ maximalIdeal R at hc
  simp only [hjt, ↓reduceIte, heval] at hc
  have h := (maximalIdeal R).mul_mem_left (koszulSign R t.val j) hc
  simpa only [← mul_assoc, koszulSign_mul_self, one_mul] using h

variable (R)

/-- Evaluate the empty coordinate and reduce it to the residue field. -/
noncomputable def finiteKoszulAugmentation (e : ℕ) :
    FiniteKoszulModule R (Fin e) 0 →ₗ[R] ResidueField R :=
  (Algebra.linearMap R (ResidueField R)).comp
    (LinearMap.proj (⟨∅, rfl⟩ : {s : Finset (Fin e) // s.card = 0}))

lemma maximalIdeal_smul_residueField :
    maximalIdeal R • (⊤ : Submodule R (ResidueField R)) = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.smul_le.mpr
  intro r hr y _
  change r • y = 0
  have hz : algebraMap R (ResidueField R) r = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hr
  rw [Algebra.smul_def, hz, zero_mul]

lemma finiteKoszulAugmentation_lTensor_injective (e : ℕ) :
    Function.Injective ((finiteKoszulAugmentation R e).lTensor (ResidueField R)) := by
  apply lTensor_residueField_injective_of_preimage
  intro x hx
  rw [maximalIdeal_smul_residueField] at hx
  have hz : algebraMap R (ResidueField R)
      (x (⟨∅, rfl⟩ : {s : Finset (Fin e) // s.card = 0})) = 0 := hx
  have hxe := Ideal.Quotient.eq_zero_iff_mem.mp hz
  rw [mem_ideal_smul_top_pi_iff]
  intro s
  have hs : s = (⟨∅, rfl⟩ : {s : Finset (Fin e) // s.card = 0}) :=
    Subtype.ext (Finset.card_eq_zero.mp s.property)
  simpa only [hs] using hxe

lemma finiteKoszulAugmentation_comp_differential (e : ℕ)
    (a : Fin e → maximalIdeal R) :
    (finiteKoszulAugmentation R e).comp
      (finiteKoszulDifferential (fun i ↦ (a i : R)) 0) = 0 := by
  apply LinearMap.ext
  intro x
  change algebraMap R (ResidueField R)
    (∑ i, koszulCoefficient (fun i ↦ (a i : R)) ∅ i *
      koszulExtend 1 x (insert i ∅)) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  simp [koszulCoefficient, map_mul]

/-- The unconditional embedding-dimension lower bound, Stacks Project Tag 00OA. -/
theorem residueFieldProjectiveDimensionLowerBound :
    ResidueFieldProjectiveDimensionLowerBoundStatement.{u} := by
  intro R _ _ _
  classical
  let e := (maximalIdeal R).spanFinrank
  let a : Fin e → maximalIdeal R := minimalMaximalIdealGenerators R
  let C := FiniteKoszulModule R (Fin e)
  let M := FGModuleCat.of R (ResidueField R)
  have : Nonempty {s : Finset (Fin e) // s.card = e} :=
    ⟨⟨Finset.univ, by simp⟩⟩
  have : Nontrivial (C e) := inferInstance
  exact projectiveDimension_ge_of_projectiveComplex R M C
    (finiteKoszulDifferential (fun i ↦ (a i : R)))
    (finiteKoszulAugmentation R e)
    (finiteKoszulAugmentation_comp_differential R e a)
    (finiteKoszulDifferential_sq (fun i ↦ (a i : R)))
    (finiteKoszulAugmentation_lTensor_injective R e)
    (finiteKoszulDifferential_detect a (minimalMaximalIdealGenerators_independent R)) e

end Langlands.CommutativeAlgebra
