import Langlands.Cohomology.SupercuspidalRestriction.Statement
import Langlands.Representation.CuspidalSupport.DeterminantUnitStructureProof
import Langlands.Group.GL.OneBlockShape

/-! # The unit-determinant subgroup of GL over a p-adic field -/

noncomputable section

namespace Langlands.Cohomology.SupercuspidalRestriction

open GeneralLinear CuspidalSupport

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{0} p)

local instance : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- The canonical spectral norm and the residue-normalized determinant norm
have the same unit kernel. -/
theorem unitDeterminantSubgroup_eq_determinantNorm_ker (n : ℕ) :
    unitDeterminantSubgroup F n =
      (F.canonicalTopologicalData.determinantNorm n).ker := by
  ext g
  rw [mem_unitDeterminantSubgroup, MonoidHom.mem_ker, ← Units.val_inj,
    ← NNReal.coe_inj,
    F.canonicalTopologicalData.determinantNorm_eq_canonicalNorm_pow_degree]
  let := F.canonicalNormedField
  exact (pow_eq_one_iff_of_nonneg
    (norm_nonneg (GeneralLinear.determinant g : F.Carrier))
    (Module.finrank_pos (R := Padic p) (M := F.Carrier)).ne').symm

/-- Bernstein–Zelevinsky 1976, §3.20: openness, compact central intersection,
and finite index after adjoining the center, for every rank. -/
theorem unitDeterminantSubgroupStatement_proof (n : ℕ) :
    UnitDeterminantSubgroupStatement F n := by
  change IsOpen (unitDeterminantSubgroup F n : Set (GeneralLinear n F.Carrier)) ∧
    IsCompact ((unitDeterminantSubgroup F n ⊓
      Subgroup.center (GeneralLinear n F.Carrier) :
        Subgroup (GeneralLinear n F.Carrier)) : Set (GeneralLinear n F.Carrier)) ∧
    (Subgroup.center (GeneralLinear n F.Carrier) ⊔
      unitDeterminantSubgroup F n).FiniteIndex
  rw [unitDeterminantSubgroup_eq_determinantNorm_ker]
  refine ⟨F.canonicalTopologicalData.isOpen_ker_determinantNorm n, ?_⟩
  cases n with
  | zero =>
      exact ⟨(Set.toFinite _).isCompact, inferInstance⟩
  | succ m =>
      let T := F.canonicalTopologicalData
      let B := LeviAdmissibility.oneBlock (m + 1) (Nat.zero_lt_succ m)
      let : Unique (Fin B.length) := by
        change Unique (Fin 1)
        infer_instance
      let e : B.Levi F.Carrier ≃* GeneralLinear (m + 1) F.Carrier :=
        MulEquiv.piUnique _
      have he : Continuous e := continuous_apply default
      have hker : (determinantUnitSubgroup T B).map e.toMonoidHom =
          (T.determinantNorm (m + 1)).ker := by
        ext g
        constructor
        · rintro ⟨a, ha, rfl⟩
          exact (mem_determinantUnitSubgroup T B a).mp ha default
        · intro hg
          refine ⟨fun _ => g, ?_, rfl⟩
          exact (mem_determinantUnitSubgroup T B _).mpr fun _ => hg
      have hcenter : (Subgroup.center (B.Levi F.Carrier)).map e.toMonoidHom =
          Subgroup.center (GeneralLinear (m + 1) F.Carrier) :=
        Subgroup.map_center_eq e
      constructor
      · have hc := leviDeterminantUnitCentralCompactness F T B
        change IsCompact
          ((determinantUnitSubgroup T B ⊓ Subgroup.center (B.Levi F.Carrier) :
            Subgroup (B.Levi F.Carrier)) : Set (B.Levi F.Carrier)) at hc
        have himage : (determinantUnitSubgroup T B ⊓
            Subgroup.center (B.Levi F.Carrier)).map e.toMonoidHom =
            (T.determinantNorm (m + 1)).ker ⊓
              Subgroup.center (GeneralLinear (m + 1) F.Carrier) := by
          rw [Subgroup.map_inf _ _ _ e.injective, hker, hcenter]
        rw [← himage]
        exact hc.image he
      · have himage : (determinantUnitSubgroup T B ⊔
            Subgroup.center (B.Levi F.Carrier)).map e.toMonoidHom =
            Subgroup.center (GeneralLinear (m + 1) F.Carrier) ⊔
              (T.determinantNorm (m + 1)).ker := by
          rw [Subgroup.map_sup, hker, hcenter, sup_comm]
        have := determinantUnit_sup_center_finiteIndex T B
        rw [← himage]
        exact Subgroup.FiniteIndex.map_of_surjective _ e.surjective

end Langlands.Cohomology.SupercuspidalRestriction
