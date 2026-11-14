import Langlands.Representation.GodementJacquet.SupercuspidalMatrixSupport
import Langlands.AllField.Group.GL.UnramifiedCharacterSupplement
import Langlands.AllField.Representation.CuspidalSupport.DeterminantUnitStructureProof
import Langlands.AllField.Representation.GodementJacquet.SupercuspidalCoefficientTests
import Langlands.AllField.Representation.GodementJacquet.Zeta
/-! # Compact scalar support of actual supercuspidal coefficient spans -/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding determinantNorm_ker_sup_center_finiteIndex exists_centralCharacter_compactScalarSupport hasCompactSupport_determinantUnit_coefficient oneBlockDeterminantUnitHomeomorph
open Langlands.AllField.GodementJacquet

universe uG uF uV

section Coefficients


end Coefficients

section PadicSupport

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.CuspidalSupport hiding AssociatedJacquetFiltrationTheorem NonassociatedJacquetSubquotientsTheorem SingleBlockCuspidalityClause determinantUnitInclusion determinantUnitRestriction determinantUnitSubgroup determinantUnit_sup_center_finiteIndex leviHarishChandraTheorem levi_exists_compact_openSubgroup_subset mem_determinantUnitSubgroup singleBlockCuspidalityClause
open Langlands.AllField.CuspidalSupport

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {n : ℕ}

/-- The GL determinant-unit subgroup has finite index after adjoining the
center, by the published one-block product-Levi result. -/
theorem determinantNorm_ker_sup_center_finiteIndex :
    ((T.determinantNorm (n + 1)).ker ⊔
      Subgroup.center (Langlands.GeneralLinear (n + 1) F)).FiniteIndex := by
  let B := LeviAdmissibility.oneBlock (n + 1) (Nat.zero_lt_succ n)
  let : Unique (Fin B.length) := by
    change Unique (Fin 1)
    infer_instance
  let : NeZero B.length := by
    change NeZero 1
    infer_instance
  let e : B.Levi F ≃* Langlands.GeneralLinear (n + 1) F :=
    MulEquiv.piUnique _
  have hker : (determinantUnitSubgroup T B).map e.toMonoidHom =
      (T.determinantNorm (n + 1)).ker := by
    ext g
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact (mem_determinantUnitSubgroup T B m).mp hm 0
    · intro hg
      refine ⟨fun _ => g, ?_, rfl⟩
      exact (mem_determinantUnitSubgroup T B _).mpr fun _ => hg
  have hmap : (determinantUnitSubgroup T B ⊔
      Subgroup.center (B.Levi F)).map e.toMonoidHom =
      (T.determinantNorm (n + 1)).ker ⊔
        Subgroup.center (Langlands.GeneralLinear (n + 1) F) := by
    rw [Subgroup.map_sup, hker]
    congr 1
    exact Subgroup.map_center_eq e
  have := determinantUnit_sup_center_finiteIndex T B
  rw [← hmap]
  exact Subgroup.FiniteIndex.map_of_surjective _ e.surjective

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Irreducible supercuspidality supplies the actual scalar character and
compact scalar covers for every bi-smooth coefficient, including finite sums. -/
theorem exists_centralCharacter_compactScalarSupport :
    letI := T.topology
    ∀ (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V),
      IsSupercuspidal ρ → ρ.IsIrreducible →
      ∃ χ : Subgroup.center (Langlands.GeneralLinear (n + 1) F) →* ℂˣ,
        (∀ (z : Subgroup.center (Langlands.GeneralLinear (n + 1) F)) (v : V),
          ρ (z : Langlands.GeneralLinear (n + 1) F) v = (χ z : ℂ) • v) ∧
        ∀ f : biSmoothMatrixCoefficients ρ,
          Continuous f.val ∧
          (∀ (z : Subgroup.center (Langlands.GeneralLinear (n + 1) F))
            (g : Langlands.GeneralLinear (n + 1) F),
            f.val (z * g) = (χ z : ℂ) * f.val g) ∧
          ∃ K : Set (Langlands.GeneralLinear (n + 1) F),
            IsCompact K ∧ Function.support f.val ⊆ scalarSaturation K := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  intro ρ hρ hi
  obtain ⟨χ, ⟨_, hχ⟩, _⟩ := admissibleSchur_centralCharacter ρ hρ.1 hi
  have := determinantNorm_ker_sup_center_finiteIndex T (n := n)
  have hsupport := biSmoothMatrixCoefficients_le_compactCentralSupportFunctions
    ρ χ hχ (T.determinantNorm (n + 1)).ker (fun ℓ w =>
      hasCompactSupport_determinantUnit_coefficient T (Nat.zero_lt_succ n)
        ρ hρ w ℓ.val ℓ.property)
  refine ⟨χ, hχ, fun f => ⟨continuous_of_mem_biSmoothMatrixCoefficients ρ _ f.property,
    biSmoothMatrixCoefficients_le_centralCovariantFunctions ρ χ hχ f.property, ?_⟩⟩
  obtain ⟨K, hK, hf⟩ := hsupport f.property
  refine ⟨K, hK, fun g hg => ?_⟩
  obtain ⟨z, k, hk, he⟩ := hf hg
  have hz : (z : Langlands.GeneralLinear (n + 1) F) ∈
      (Matrix.GeneralLinearGroup.scalar (Fin (n + 1))).range := by
    simpa only [Matrix.GeneralLinearGroup.center_eq_range_scalar] using z.property
  obtain ⟨a, ha⟩ := hz
  exact ⟨a, k, hk, he.trans (congrArg (fun x => x * k) ha.symm)⟩

end PadicSupport

end Langlands.AllField.GodementJacquet
