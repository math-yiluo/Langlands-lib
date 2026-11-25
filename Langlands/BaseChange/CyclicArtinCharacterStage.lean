import Langlands.ClassFieldTheory.Local.NormExistenceProof
import Langlands.ClassFieldTheory.Local.FiniteArtinNorm
import Langlands.ClassFieldTheory.Local.UniverseZero.TypeZeroNormTransferProof
import Langlands.Weil.Representation.ContinuityProof
import Mathlib.RingTheory.RootsOfUnity.Basic

/-! # A common finite abelian stage for the Artin conductor comparison -/

noncomputable section

namespace Langlands.BaseChange

open LocalClassField ClassFieldTheory.Local HarmonicAnalysis
open LocalClassField.FiniteArtinSystemExistence ClassFieldTheory.Local.FiniteArtinSymbol
open scoped IsMulCommutative

universe u v

section Cofinal

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
  (E : Type v) [Field E] [Algebra F.Carrier E] [FiniteDimensional F.Carrier E]
  [IsAbelianGalois F.Carrier E] (T : F.TopologicalData)

/-- A finite-order character and a finite abelian extension can be put in a
common finite abelian stage, with the stage's norms killed by the character. -/
theorem exists_finiteAbelianStage_of_finiteOrder :
    letI := T.topology
    ∀ (χ : Quasicharacter F.Carrier) {m : ℕ}, 0 < m → χ ^ m = 1 →
      ∃ M : FiniteIntermediateExtension F.Carrier,
        IsAbelianGalois F.Carrier M.field ∧
        Nonempty (E →ₐ[F.Carrier] M.field) ∧
        normSubgroup F.Carrier M.field ≤ χ.toMonoidHom.ker := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro χ m hm hχ
  let : NeZero m := ⟨hm.ne'⟩
  let H := χ.toMonoidHom.ker
  have hr : (Set.range χ).Finite := by
    have hroots : (rootsOfUnity m ℂ : Set ℂˣ).Finite :=
      Set.finite_coe_iff.mp (inferInstanceAs (Finite (rootsOfUnity m ℂ)))
    refine hroots.subset ?_
    rintro _ ⟨a, rfl⟩
    exact (mem_rootsOfUnity _ _).mpr (by
      simpa only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.coe_one, Pi.one_apply] using
        DFunLike.congr_fun hχ a)
  let : Finite χ.toMonoidHom.range := hr.to_subtype
  let : Finite (F.Carrierˣ ⧸ H) := Finite.of_injective _
    (QuotientGroup.quotientKerEquivRange χ.toMonoidHom).injective
  let : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let := T.fieldT2
  have hclosed : IsClosed (H : Set F.Carrierˣ) :=
    IsClosed.preimage χ.continuous isClosed_singleton
  have hopen : IsOpen (H : Set F.Carrierˣ) :=
    Weil.open_kernel_of_finite_range_of_closed χ.toMonoidHom hr hclosed
  have hopen' : letI := F.canonicalTopologicalData.topology; IsOpen (H : Set F.Carrierˣ) := by
    have ht : T.topology = F.canonicalTopologicalData.topology :=
      T.topology_eq_canonicalModule.trans F.canonicalTopologicalData.topology_eq_canonicalModule.symm
    exact ht ▸ hopen
  obtain ⟨A, ⟨hAdim, hAb, hA⟩, _⟩ := normSubgroupExistence p F H hopen' inferInstance
  let := hAdim
  let := hAb
  let j : E →ₐ[F.Carrier] AlgebraicClosure F.Carrier := IsAlgClosed.lift
  let L := j.fieldRange
  let : FiniteDimensional F.Carrier L := Module.Finite.equiv j.equivFieldRange.toLinearEquiv
  let : IsAbelianGalois F.Carrier L := IsAbelianGalois.of_algHom j.equivFieldRange.symm.toAlgHom
  let M : FiniteIntermediateExtension F.Carrier := ⟨L ⊔ A, inferInstance⟩
  exact ⟨M, inferInstance, ⟨(IntermediateField.inclusion le_sup_left).comp
    j.equivFieldRange.toAlgHom⟩,
    (normSubgroup_antitone_intermediateField F.Carrier A (L ⊔ A) le_sup_right).trans hA.le⟩

end Cofinal

section Norm

variable {p : ℕ} [Fact p.Prime] (F E : PadicField.{u} p) (M : Type u) [Field M]
  [Algebra F.Carrier E.Carrier] [Algebra F.Carrier M] [Algebra E.Carrier M]
  [IsScalarTower F.Carrier E.Carrier M] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  [FiniteDimensional F.Carrier E.Carrier] [FiniteDimensional F.Carrier M]
  [FiniteDimensional E.Carrier M] [IsAbelianGalois F.Carrier M] [IsAbelianGalois E.Carrier M]

/-- Restricting scalars on the geometric symbol agrees with taking the actual norm. -/
theorem geometricSymbol_norm (a : E.Carrierˣ) :
    geometricSymbol F M (normUnits F.Carrier E.Carrier a) =
      (geometricSymbol E M a).restrictScalars F.Carrier := by
  rw [geometricSymbol_apply, geometricSymbol_apply, ← map_inv]
  have h := abelianizedArtinSymbol_norm F E M a⁻¹
  rw [abelianizedArtinSymbol_eq_of_comm, abelianizedArtinSymbol_eq_of_comm,
    Abelianization.map_of] at h
  exact (UniverseZero.abelianization_of_injective_of_isMulCommutative h).symm

/-- A base unit maps to the relative subgroup exactly when it is an actual norm. -/
theorem comap_relativeGaloisGroup_geometricSymbol :
    (AlgEquiv.restrictScalarsHom (S := E.Carrier) (A := M) F.Carrier).range.comap
      (geometricSymbol F M) = normSubgroup F.Carrier E.Carrier := by
  ext a
  constructor
  · rintro ⟨τ, hτ⟩
    obtain ⟨b, rfl⟩ := geometricSymbol_surjective E M τ
    have hab : geometricSymbol F M (normUnits F.Carrier E.Carrier b) =
        geometricSymbol F M a := (geometricSymbol_norm F E M b).trans hτ
    have hker : a * (normUnits F.Carrier E.Carrier b)⁻¹ ∈ (geometricSymbol F M).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
    rw [ker_geometricSymbol] at hker
    have hmem := normSubgroup_le_of_tower F.Carrier M E.Carrier hker
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using
      (normSubgroup F.Carrier E.Carrier).mul_mem hmem (show normUnits F.Carrier E.Carrier b ∈
        normSubgroup F.Carrier E.Carrier from ⟨b, rfl⟩)
  · rintro ⟨b, rfl⟩
    exact ⟨geometricSymbol E M b, (geometricSymbol_norm F E M b).symm⟩

end Norm

end Langlands.BaseChange
