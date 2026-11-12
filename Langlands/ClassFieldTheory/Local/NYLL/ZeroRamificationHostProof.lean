import Langlands.ClassFieldTheory.Local.NYLL.ZeroRamificationHostStatement
import Langlands.ClassFieldTheory.Local.NYLL.SuppliedValuationProof
import Langlands.ClassFieldTheory.Local.NYLL.RelativeIntegerStructureProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.ResidueInertia.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois.KernelProofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing.Proofs

/-! # Zero-depth ramification in terms of supplied local-field data: proof -/

namespace Langlands.LocalClassField.NYLL

open scoped ValuativeRel

universe u

section Supplied

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

/-- The supplied integer ring is the closed unit ball of the supplied discrete
valuation. -/
private theorem mem_integers_iff (x : F.Carrier) :
    x ∈ T.Integers ↔ T.discreteValuation x ≤ 1 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  change ValuativeRel.valuation F.Carrier x ≤ 1 ↔
    e (ValuativeRel.valuation F.Carrier x) ≤ 1
  rw [← map_one e]
  exact e.strictMono.le_iff_le.symm

/-- The maximal ideal of the supplied integer ring is the open unit ball of the
supplied discrete valuation. -/
private theorem mem_maximalIdeal_iff (a : T.Integers) :
    a ∈ IsLocalRing.maximalIdeal T.Integers ↔
      T.discreteValuation (a : F.Carrier) < 1 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  rw [IsLocalRing.mem_maximalIdeal]
  change ¬IsUnit a ↔ T.discreteValuation (a : F.Carrier) < 1
  rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  change ValuativeRel.valuation F.Carrier (a : F.Carrier) < 1 ↔
    e (ValuativeRel.valuation F.Carrier (a : F.Carrier)) < 1
  rw [← map_one e]
  exact e.strictMono.lt_iff_lt.symm

end Supplied

/-- The zeroth upper ramification group of the supplied base realization is
cut out by the residue congruence of any supplied extension realization. -/
theorem zeroUpperRamificationHost : ZeroUpperRamificationHostStatement := by
  intro p _ F E _ _ _ _ TF TE σ
  let := TF.topology
  let := TF.valuativeRel
  let := TF.localField
  let := TE.topology
  let := TE.valuativeRel
  let := TE.localField
  let : Valuation.HasExtension (ValuativeRel.valuation F.Carrier)
      (ValuativeRel.valuation E.Carrier) :=
    suppliedRelativeValuationExtension p F E TF TE
  obtain ⟨hclosure, hfinite⟩ := relativeIntegerStructure p F E TF TE
  have hA : PadicField.TopologicalData.relativeIntegerAlgebra TF TE =
      (Valuation.HasExtension.instAlgebraInteger :
        Algebra 𝒪[F.Carrier] 𝒪[E.Carrier]) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  have hB : PadicField.TopologicalData.relativeIntegerFieldAlgebra (E := E) TF =
      (Algebra.ofSubsemiring 𝒪[F.Carrier] : Algebra 𝒪[F.Carrier] E.Carrier) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  have hclosure' : @IsIntegralClosure 𝒪[E.Carrier] 𝒪[F.Carrier] E.Carrier _ _ _
      (PadicField.TopologicalData.relativeIntegerFieldAlgebra (E := E) TF) _ := hclosure
  have hfinite' : @Module.Finite 𝒪[F.Carrier] 𝒪[E.Carrier] _ _
      (PadicField.TopologicalData.relativeIntegerAlgebra TF TE).toModule := hfinite
  rw [hB] at hclosure'
  rw [hA] at hfinite'
  have : IsIntegralClosure 𝒪[E.Carrier] 𝒪[F.Carrier] E.Carrier := hclosure'
  have : Module.Finite 𝒪[F.Carrier] 𝒪[E.Carrier] := hfinite'
  show σ ∈ Langlands.NYLL.RamificationTheory.LocalField.localUpperRamificationGroup
      F.Carrier E.Carrier 0 ↔ _
  rw [Langlands.NYLL.RamificationTheory.LocalField.localUpperRamificationGroup_zero_eq_residue_ker
      F.Carrier E.Carrier,
    Langlands.NYLL.LocalFieldTheory.galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal
      F.Carrier E.Carrier σ]
  have happly (x : 𝒪[E.Carrier]) :
      (((Langlands.NYLL.LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure
          F.Carrier E.Carrier σ x - x : 𝒪[E.Carrier]) : E.Carrier)) =
        σ (x : E.Carrier) - (x : E.Carrier) := by
    rw [AddSubgroupClass.coe_sub,
      Langlands.NYLL.LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure_apply]
  constructor
  · intro h x hx
    have hx' : x ∈ TE.Integers := (mem_integers_iff TE x).mpr hx
    have hmem := (mem_maximalIdeal_iff TE _).mp (h ⟨x, hx'⟩)
    rw [happly] at hmem
    exact hmem
  · intro h x
    apply (mem_maximalIdeal_iff TE _).mpr
    rw [happly]
    exact h (x : E.Carrier) ((mem_integers_iff TE (x : E.Carrier)).mp x.property)

end Langlands.LocalClassField.NYLL
