import Langlands.Representation.IntegerLattice.GeneralizedWeightGlobalBasisStatement
import Langlands.Representation.IntegerLattice.GeneralizedWeightProof
import Langlands.LinearAlgebra.CommutingNilpotentStrictUpperBasisProof
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Matrix.Block

/-! # A common global basis for the actual generalized-weight blocks -/

set_option autoImplicit false

namespace Langlands

universe u

namespace IntegerLattice.GlobalBlockBasis

variable {d : ℕ} {V : Type u} [AddCommGroup V] [Module ℂ V]

theorem normalizedDifference_isNilpotent [FiniteDimensional ℂ V]
    (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ) (t : Fin d) :
    IsNilpotent (normalizedGeneratorDifference A c t) := by
  let f : Module.End ℂ V := (A.1 t : Module.End ℂ V)
  let W := generalizedWeightBlock A c
  have hf : Set.MapsTo (f - algebraMap ℂ (Module.End ℂ V) (c t : ℂ)) W W := by
    intro x hx
    change f x - (c t : ℂ) • x ∈ W
    exact W.sub_mem
      (by
        simpa only [W, f, tupleRepresentationEquiv_generator, SetLike.mem_coe] using
          mapsTo_generalizedWeightBlock A c (generator d t) hx)
      (W.smul_mem _ hx)
  have hn : IsNilpotent
      ((f - algebraMap ℂ (Module.End ℂ V) (c t : ℂ)).restrict hf) :=
    Module.End.isNilpotent_restrict_of_le
      (show W ≤ f.maxGenEigenspace (c t : ℂ) from iInf_le _ t)
      (f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap (c t : ℂ))
  have heq : normalizedGeneratorDifference A c t =
      (c t : ℂ)⁻¹ •
        ((f - algebraMap ℂ (Module.End ℂ V) (c t : ℂ)).restrict hf) := by
    ext w
    simp only [normalizedGeneratorDifference_apply_coe, LinearMap.smul_apply,
      Submodule.coe_smul, LinearMap.restrict_apply, LinearMap.sub_apply,
      Algebra.algebraMap_eq_smul_one, Module.End.one_apply, smul_sub, smul_smul]
    rw [inv_mul_cancel₀ (c t).ne_zero, one_smul]
  rw [heq]
  exact hn.smul _

theorem normalizedDifference_commute (A : CommutingInvertibleTuple d V)
    (c : Fin d → ℂˣ) (s t : Fin d) :
    Commute (normalizedGeneratorDifference A c s) (normalizedGeneratorDifference A c t) := by
  have h : Commute
      (generalizedWeightBlockGenerator A c s : Module.End ℂ (generalizedWeightBlock A c))
      (generalizedWeightBlockGenerator A c t : Module.End ℂ (generalizedWeightBlock A c)) := by
    simp only [coe_generalizedWeightBlockGenerator]
    exact (Commute.all (generator d s) (generator d t)).map
      (generalizedWeightBlockRepresentation A c)
  have h' : Commute
      ((c s : ℂ)⁻¹ •
        (generalizedWeightBlockGenerator A c s : Module.End ℂ (generalizedWeightBlock A c)))
      ((c t : ℂ)⁻¹ •
        (generalizedWeightBlockGenerator A c t : Module.End ℂ (generalizedWeightBlock A c))) := by
    change _ * _ = _ * _
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [h.eq, mul_comm (c s : ℂ)⁻¹ (c t : ℂ)⁻¹]
  simpa only [normalizedGeneratorDifference, coe_normalizedBlockGenerator] using
    (h'.sub_left (Commute.one_left _)).sub_right (Commute.one_right _)

theorem upper_mul_diag {r : ℕ} {M N : Matrix (Fin r) (Fin r) ℂ}
    (hM : M.IsUpperTriangular) (hN : N.IsUpperTriangular) (i : Fin r) :
    (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hM h, zero_mul]
    · rw [hN h, mul_zero]
  · simp

theorem upper_unit_inv {r : ℕ} (g : (Matrix (Fin r) (Fin r) ℂ)ˣ)
    (hg : (g : Matrix (Fin r) (Fin r) ℂ).IsUpperTriangular) :
    ((g⁻¹ : (Matrix (Fin r) (Fin r) ℂ)ˣ) : Matrix (Fin r) (Fin r) ℂ).IsUpperTriangular := by
  let _ := g.invertible
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hg

theorem upper_unit_inv_diag {r : ℕ} (g : (Matrix (Fin r) (Fin r) ℂ)ˣ)
    (a : ℂˣ) (hg : (g : Matrix (Fin r) (Fin r) ℂ).IsUpperTriangular)
    (hd : ∀ i, (g : Matrix (Fin r) (Fin r) ℂ) i i = (a : ℂ)) (i : Fin r) :
    ((g⁻¹ : (Matrix (Fin r) (Fin r) ℂ)ˣ) : Matrix (Fin r) (Fin r) ℂ) i i =
      ((a⁻¹ : ℂˣ) : ℂ) := by
  have hh := upper_mul_diag hg (upper_unit_inv g hg) i
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq, hd i] at hh
  apply (mul_left_cancel₀ a.ne_zero)
  rw [← hh]
  simp

theorem block_action_coordinates (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ)
    (b : Module.Basis (Fin (Module.finrank ℂ (generalizedWeightBlock A c)))
      ℂ (generalizedWeightBlock A c))
    (hb : ∀ (t : Fin d)
      (i j : Fin (Module.finrank ℂ (generalizedWeightBlock A c))),
      j ≤ i → b.repr (normalizedGeneratorDifference A c t (b j)) i = 0)
    (n : Lattice d) :
    (∀ (i j : Fin (Module.finrank ℂ (generalizedWeightBlock A c))),
      j < i → b.repr (generalizedWeightBlockRepresentation A c n (b j)) i = 0) ∧
    (∀ i : Fin (Module.finrank ℂ (generalizedWeightBlock A c)),
      b.repr (generalizedWeightBlockRepresentation A c n (b i)) i =
        (coordinateCharacter c n : ℂ)) := by
  classical
  let r := Module.finrank ℂ (generalizedWeightBlock A c)
  let ρ := generalizedWeightBlockRepresentation A c
  let m : Lattice d →* (Matrix (Fin r) (Fin r) ℂ)ˣ :=
    (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp ρ.asGroupHom
  have hm (k : Lattice d) :
      (m k : Matrix (Fin r) (Fin r) ℂ) = LinearMap.toMatrixAlgEquiv b (ρ k) := rfl
  let S : Subgroup (Lattice d) :=
    { carrier := {k | (m k : Matrix (Fin r) (Fin r) ℂ).IsUpperTriangular ∧
        ∀ i, (m k : Matrix (Fin r) (Fin r) ℂ) i i = (coordinateCharacter c k : ℂ)}
      one_mem' := by
        change (m 1 : Matrix (Fin r) (Fin r) ℂ).IsUpperTriangular ∧
          ∀ i, (m 1 : Matrix (Fin r) (Fin r) ℂ) i i = (coordinateCharacter c 1 : ℂ)
        simp only [map_one, Units.val_one]
        exact ⟨Matrix.blockTriangular_one, fun i => Matrix.one_apply_eq i⟩
      mul_mem' := by
        intro k l hk hl
        constructor
        · simpa only [map_mul, Units.val_mul] using hk.1.mul hl.1
        · intro i
          simp only [map_mul, Units.val_mul]
          rw [upper_mul_diag hk.1 hl.1, hk.2 i, hl.2 i]
      inv_mem' := by
        intro k hk
        constructor
        · simpa only [map_inv] using upper_unit_inv (m k) hk.1
        · intro i
          simpa only [map_inv] using
            upper_unit_inv_diag (m k) (coordinateCharacter c k) hk.1 hk.2 i }
  have hgen (t : Fin d) : generator d t ∈ S := by
    change (m (generator d t) : Matrix (Fin r) (Fin r) ℂ).IsUpperTriangular ∧ _
    have hentry (i j : Fin r) :
        (m (generator d t) : Matrix (Fin r) (Fin r) ℂ) i j =
          (c t : ℂ) * ((if i = j then 1 else 0) +
            b.repr (normalizedGeneratorDifference A c t (b j)) i) := by
      rw [hm, LinearMap.toMatrixAlgEquiv_apply]
      change b.repr
        ((generalizedWeightBlockGenerator A c t :
          Module.End ℂ (generalizedWeightBlock A c)) (b j)) i = _
      rw [generalizedWeightBlockGenerator_eq_smul]
      simp only [LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply,
        map_smul, map_add, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
        Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs <;> simp_all
    constructor
    · intro i j hij
      have hne : i ≠ j := ne_of_gt (show j < i from hij)
      simp [hentry, hb t i j (le_of_lt hij), hne]
    · intro i
      simp [hentry, hb t i i le_rfl]
  have hn : n = ∏ t : Fin d, (generator d t) ^ n.toAdd t := by
    apply Multiplicative.toAdd.injective
    ext t
    simp [generator, toAdd_prod, toAdd_zpow, Finset.sum_apply, Pi.single_apply]
  have hmem : n ∈ S := by
    rw [hn]
    exact S.prod_mem fun t _ => S.zpow_mem (hgen t) _
  constructor
  · intro i j hij
    have h := hmem.1 hij
    simpa only [hm, LinearMap.toMatrixAlgEquiv_apply] using h
  · intro i
    have h := hmem.2 i
    simpa only [hm, LinearMap.toMatrixAlgEquiv_apply] using h

end IntegerLattice.GlobalBlockBasis

open IntegerLattice

/-- A single basis, assembled from the actual generalized-weight blocks,
triangularizes every lattice action with its coordinate-character diagonal. -/
theorem commutingTupleGeneralizedWeightGlobalBasis :
    CommutingTupleGeneralizedWeightGlobalBasisStatement.{u} := by
  classical
  intro d V _ _ _ A
  have hlocal (c : Fin d → ℂˣ) :=
    CommutingNilpotentStrictUpperBasis.commutingNilpotentStrictUpperBasis ℂ
      (generalizedWeightBlock A c) (Fin d) (normalizedGeneratorDifference A c)
      (IntegerLattice.GlobalBlockBasis.normalizedDifference_commute A c)
      (IntegerLattice.GlobalBlockBasis.normalizedDifference_isNilpotent A c)
  choose b hb using hlocal
  obtain ⟨_, hind, htop, _⟩ := commutingTupleGeneralizedWeightDecomposition d V A
  have hsum : DirectSum.IsInternal (generalizedWeightBlock A) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  let B := hsum.collectedBasis b
  have hB (c : Fin d → ℂˣ)
      (j : Fin (Module.finrank ℂ (generalizedWeightBlock A c))) :
      B ⟨c, j⟩ = (b c j : V) := by
    exact congrFun (hsum.collectedBasis_coe b) ⟨c, j⟩
  refine ⟨b, B, hB, hb, ?_, ?_, ?_⟩
  · intro n c c' i j hcc
    rw [hB]
    exact hsum.collectedBasis_repr_of_mem_ne b hcc.symm
      (mapsTo_generalizedWeightBlock A c' n (b c' j).property)
  · intro n c i j hij
    rw [hB]
    rw [hsum.collectedBasis_repr_of_mem b
      (mapsTo_generalizedWeightBlock A c n (b c j).property)]
    exact (IntegerLattice.GlobalBlockBasis.block_action_coordinates A c (b c) (hb c) n).1
      i j hij
  · intro n c i
    rw [hB]
    rw [hsum.collectedBasis_repr_of_mem b
      (mapsTo_generalizedWeightBlock A c n (b c i).property)]
    exact (IntegerLattice.GlobalBlockBasis.block_action_coordinates A c (b c) (hb c) n).2 i

end Langlands
