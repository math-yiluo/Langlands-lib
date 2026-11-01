import Langlands.Representation.IntegerLattice.GeneralizedWeightProductStatement
import Langlands.Representation.IntegerLattice.GeneralizedWeightBlockBasisProof
import Langlands.LinearAlgebra.UnipotentBinomialProof
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

universe u

namespace Langlands.IntegerLattice

variable {d : ℕ} {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- The published generator reconstruction in increasing coordinate order. -/
theorem representation_eq_ordered_product
    (ρ : Representation ℂ (Lattice d) V) (n : Lattice d) :
    ρ n =
      (List.ofFn (fun i : Fin d =>
        ((ρ.asGroupHom (generator d i) ^ n.toAdd i : (Module.End ℂ V)ˣ) :
          Module.End ℂ V))).prod := by
  rw [representation_eq_product]
  have h := Finset.noncommProd_toFinset (List.finRange d)
    (fun i => ρ.asGroupHom (generator d i) ^ n.toAdd i)
    (fun i _ j _ _ => (generator_values_commute d V ρ i j).zpow_zpow _ _)
    (List.nodup_finRange d)
  rw [List.toFinset_finRange, ← List.ofFn_eq_map] at h
  rw [h]
  change (Units.coeHom _) (List.ofFn (fun i : Fin d =>
    ρ.asGroupHom (generator d i) ^ n.toAdd i)).prod = _
  rw [map_list_prod, List.map_ofFn]
  rfl

/-- The first requested identity for the actual restricted representation. -/
theorem generalizedWeightBlockRepresentation_eq_ordered_product
    (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ) (n : Lattice d) :
    generalizedWeightBlockRepresentation A c n =
      (List.ofFn (fun i : Fin d =>
        ((generalizedWeightBlockGenerator A c i ^ n.toAdd i :
          (Module.End ℂ (generalizedWeightBlock A c))ˣ) :
            Module.End ℂ (generalizedWeightBlock A c)))).prod :=
  representation_eq_ordered_product (generalizedWeightBlockRepresentation A c) n

private theorem scalar_unit_mul_zpow (z : ℂˣ) (g : (Module.End ℂ V)ˣ) (m : ℤ) :
    (((Units.map (algebraMap ℂ (Module.End ℂ V)).toMonoidHom z * g) ^ m :
        (Module.End ℂ V)ˣ) : Module.End ℂ V) =
      (z : ℂ) ^ m • ((g ^ m : (Module.End ℂ V)ˣ) : Module.End ℂ V) := by
  have hc : Commute (Units.map (algebraMap ℂ (Module.End ℂ V)).toMonoidHom z) g := by
    apply Units.ext
    exact Algebra.commutes (z : ℂ) (g : Module.End ℂ V)
  rw [hc.mul_zpow, Units.val_mul, ← map_zpow, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_zpow_eq_zpow_val,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

/-- Scalar normalization commutes with every genuine integer unit power. -/
theorem generalizedWeightBlockGenerator_zpow_eq_smul
    (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ) (i : Fin d) (m : ℤ) :
    ((generalizedWeightBlockGenerator A c i ^ m :
        (Module.End ℂ (generalizedWeightBlock A c))ˣ) :
          Module.End ℂ (generalizedWeightBlock A c)) =
      (c i : ℂ) ^ m •
        ((normalizedBlockGenerator A c i ^ m :
          (Module.End ℂ (generalizedWeightBlock A c))ˣ) :
            Module.End ℂ (generalizedWeightBlock A c)) := by
  have h := scalar_unit_mul_zpow (c i)⁻¹ (generalizedWeightBlockGenerator A c i) m
  change ((normalizedBlockGenerator A c i ^ m :
      (Module.End ℂ (generalizedWeightBlock A c))ˣ) :
        Module.End ℂ (generalizedWeightBlock A c)) = _ at h
  rw [h, Units.val_inv_eq_inv_val, inv_zpow, smul_smul,
    mul_inv_cancel₀ (zpow_ne_zero m (c i).ne_zero), one_smul]

private theorem list_prod_smul {ι : Type*} (l : List ι)
    (s : ι → ℂ) (f : ι → Module.End ℂ V) :
    (l.map (fun i => s i • f i)).prod = (l.map s).prod • (l.map f).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, ih]
    exact smul_mul_smul_comm _ _ _ _

private theorem nilpotent_submodule_pow_ambient_finrank [FiniteDimensional ℂ V]
    (W : Submodule ℂ V) (N : Module.End ℂ W) (hN : IsNilpotent N) :
    N ^ Module.finrank ℂ V = 0 := by
  obtain ⟨r, hr⟩ := hN
  have hdim : N ^ Module.finrank ℂ W = 0 := by
    apply LinearMap.ext
    intro w
    change (N ^ Module.finrank ℂ W) w = 0
    apply Module.End.ker_pow_le_ker_pow_finrank N r
    simp [hr]
  exact pow_eq_zero_of_le W.finrank_le hdim

/-- The second requested identity, still without finite-dimensionality. -/
theorem generalizedWeightBlockRepresentation_eq_normalized_product
    (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ) (n : Lattice d) :
    generalizedWeightBlockRepresentation A c n =
      (coordinateCharacter c n : ℂ) •
        (List.ofFn (fun i : Fin d =>
          ((normalizedBlockGenerator A c i ^ n.toAdd i :
            (Module.End ℂ (generalizedWeightBlock A c))ˣ) :
              Module.End ℂ (generalizedWeightBlock A c)))).prod := by
  rw [generalizedWeightBlockRepresentation_eq_ordered_product]
  simp_rw [generalizedWeightBlockGenerator_zpow_eq_smul]
  rw [List.ofFn_eq_map, list_prod_smul, ← List.ofFn_eq_map,
    ← List.ofFn_eq_map, List.prod_ofFn, ← coe_coordinateCharacter]

private theorem block_binomial_product_of_bound
    (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ) (n : Lattice d) (r : ℕ)
    (hN : ∀ i, normalizedGeneratorDifference A c i ^ r = 0) :
    generalizedWeightBlockRepresentation A c n =
      (coordinateCharacter c n : ℂ) •
        (List.ofFn (fun i : Fin d =>
          ∑ k ∈ Finset.range r,
            Ring.choose (n.toAdd i : ℂ) k •
              normalizedGeneratorDifference A c i ^ k)).prod := by
  have hfactor (i : Fin d) :
      ((normalizedBlockGenerator A c i ^ n.toAdd i :
        (Module.End ℂ (generalizedWeightBlock A c))ˣ) :
          Module.End ℂ (generalizedWeightBlock A c)) =
        ∑ k ∈ Finset.range r,
          Ring.choose (n.toAdd i : ℂ) k •
            normalizedGeneratorDifference A c i ^ k :=
    renardCIIIUnipotentBinomial.1 (generalizedWeightBlock A c)
      (normalizedBlockGenerator A c i) r (hN i) (n.toAdd i)
  rw [generalizedWeightBlockRepresentation_eq_normalized_product]
  simp_rw [hfactor]

end Langlands.IntegerLattice

namespace Langlands

open IntegerLattice

/-- The three ordered product formulas on each actual generalized-weight block. -/
theorem commutingTupleGeneralizedWeightProduct :
    CommutingTupleGeneralizedWeightProductStatement.{u} := by
  intro d V _ _ _ A c n
  refine ⟨generalizedWeightBlockRepresentation_eq_ordered_product A c n,
    generalizedWeightBlockRepresentation_eq_normalized_product A c n, ?_⟩
  exact block_binomial_product_of_bound A c n (Module.finrank ℂ V) (fun i =>
    nilpotent_submodule_pow_ambient_finrank (generalizedWeightBlock A c)
      (normalizedGeneratorDifference A c i)
      (normalizedGeneratorDifference_isNilpotent A c i))

end Langlands
