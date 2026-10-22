import Langlands.LocalField.Normalization.Proof
import Langlands.LocalField.RelativeIntegers
import Langlands.ClassFieldTheory.Local.UnitNormStatement
import Langlands.ClassFieldTheory.Local.UnitFiltrationTopologyProof
import Langlands.LocalClassField.UnramifiedAlgebraProof
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.LinearAlgebra.FreeModule.PID

/-! Norm surjectivity on every actual unit filtration level in an unramified extension. -/

noncomputable section

namespace Langlands.PadicField.TopologicalData
universe u v
variable {p : ℕ} [Fact p.Prime]
variable {F : PadicField.{u} p} {E : PadicField.{v} p}
variable (T : F.TopologicalData) (S : E.TopologicalData)

private theorem map_maximalIdeal_of_ramificationIndex_eq (f : T.Integers →+* S.Integers)
    (he : T.ramificationIndex = S.ramificationIndex) :
    (IsLocalRing.maximalIdeal T.Integers).map f = IsLocalRing.maximalIdeal S.Integers := by
  let := S.topology
  let := S.valuativeRel
  let := S.localField
  apply pow_left_injective T.ramificationIndex_pos.ne'
  dsimp only
  rw [← Ideal.map_pow, ← T.span_prime_eq_maximalIdeal_pow,
    Ideal.map_span, Set.image_singleton, map_natCast, he,
    S.span_prime_eq_maximalIdeal_pow]

end Langlands.PadicField.TopologicalData


namespace Langlands.PadicField.TopologicalData
universe u v
variable {p : ℕ} [Fact p.Prime]
variable {F : PadicField.{u} p} {E : PadicField.{v} p}
variable [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
variable [FiniteDimensional F.Carrier E.Carrier]
variable (T : F.TopologicalData) (S : E.TopologicalData)

private theorem relativeNormData (f : T.Integers →+* S.Integers)
    (hf : ∀ x, (f x : E.Carrier) = algebraMap F.Carrier E.Carrier (x : F.Carrier)) :
    letI := f.toAlgebra
    Module.Finite T.Integers S.Integers ∧ Module.Free T.Integers S.Integers ∧
      ∀ x : S.Integers, Algebra.norm F.Carrier (x : E.Carrier) =
        (Algebra.norm T.Integers x : F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := S.topology
  let := S.valuativeRel
  let := S.localField
  let A := (ValuativeRel.valuation (Padic p)).integer
  let := T.integerAlgebra
  let := S.integerAlgebra
  let := f.toAlgebra
  let := Algebra.compHom E.Carrier T.Integers.subtype
  let := Algebra.compHom E.Carrier (algebraMap A (Padic p))
  let : IsScalarTower A T.Integers S.Integers := IsScalarTower.of_algebraMap_eq fun x => by
    apply Subtype.ext
    change _ = (f (T.baseIntegerMap x) : E.Carrier)
    rw [hf]
    exact IsScalarTower.algebraMap_apply (Padic p) F.Carrier E.Carrier x.val
  let : IsScalarTower T.Integers F.Carrier E.Carrier :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower T.Integers S.Integers E.Carrier :=
    IsScalarTower.of_algebraMap_eq fun x => (hf x).symm
  let : IsScalarTower A T.Integers E.Carrier := IsScalarTower.of_algebraMap_eq fun x => by
    exact IsScalarTower.algebraMap_apply (Padic p) F.Carrier E.Carrier x.val
  let := T.integers_finite
  let := S.integers_finite
  let : Module.Finite T.Integers S.Integers :=
    Module.Finite.of_restrictScalars_finite A T.Integers S.Integers
  let : Module.IsTorsionFree T.Integers S.Integers :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      intro x y hxy
      apply Subtype.ext
      apply (algebraMap F.Carrier E.Carrier).injective
      change f x = f y at hxy
      rw [← hf, ← hf]
      exact congrArg Subtype.val hxy)
  let : Module.Free T.Integers S.Integers := inferInstance
  refine ⟨inferInstance, inferInstance, ?_⟩
  let := S.integers_isIntegralClosure
  let : IsIntegralClosure S.Integers T.Integers E.Carrier :=
    IsIntegralClosure.tower_top (R := A)
  let := IsIntegralClosure.isLocalization T.Integers F.Carrier E.Carrier S.Integers
  intro x
  exact Algebra.norm_localization T.Integers (nonZeroDivisors T.Integers) x

end Langlands.PadicField.TopologicalData

namespace Langlands.LocalClassField.UnitNormProof
universe u v
variable {p : ℕ} [Fact p.Prime]
variable {F : PadicField.{u} p} {E : PadicField.{v} p}
variable (T : F.TopologicalData) (S : E.TopologicalData)

private theorem congruence_iff (n : ℕ) (x : T.Integersˣ) :
    x ∈ T.congruenceUnits n ↔
      (x : T.Integers) - 1 ∈ IsLocalRing.maximalIdeal T.Integers ^ n := by
  change T.truncatedUnitsReduction n x = 1 ↔ _
  rw [← Units.val_inj]
  change Ideal.Quotient.mk _ (x : T.Integers) = 1 ↔ _
  rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]

variable [Algebra F.Carrier E.Carrier] [FiniteDimensional F.Carrier E.Carrier]
variable [Algebra T.Integers S.Integers]
variable (hn : ∀ x : S.Integers, Algebra.norm F.Carrier (x : E.Carrier) =
  (Algebra.norm T.Integers x : F.Carrier))

include hn

private theorem norm_inclusion (x : S.Integersˣ) :
    normUnits F.Carrier E.Carrier (S.integerUnitsInclusion x) =
      T.integerUnitsInclusion (Units.map (Algebra.norm T.Integers) x) := by
  apply Units.ext
  exact hn x

private theorem preserves
    (hpres : ∀ (n : ℕ) (x : S.Integersˣ),
      (x : S.Integers) - 1 ∈ IsLocalRing.maximalIdeal S.Integers ^ n →
      Algebra.norm T.Integers (x : S.Integers) - 1 ∈
        IsLocalRing.maximalIdeal T.Integers ^ n) :
    ∀ n x, x ∈ S.unitFiltration n →
      normUnits F.Carrier E.Carrier x ∈ T.unitFiltration n := by
  rintro n _ ⟨x, hx, rfl⟩
  refine ⟨Units.map (Algebra.norm T.Integers) x, ?_, (norm_inclusion T S hn x).symm⟩
  exact (congruence_iff T n _).mpr (hpres n x ((congruence_iff S n x).mp hx))

private theorem approximates
    (happrox : ∀ (n : ℕ) (y : T.Integersˣ),
      (y : T.Integers) - 1 ∈ IsLocalRing.maximalIdeal T.Integers ^ n →
      ∃ x : S.Integersˣ,
        (x : S.Integers) - 1 ∈ IsLocalRing.maximalIdeal S.Integers ^ n ∧
        ((y * (Units.map (Algebra.norm T.Integers) x)⁻¹ : T.Integersˣ) : T.Integers) - 1 ∈
          IsLocalRing.maximalIdeal T.Integers ^ (n + 1)) :
    ∀ n y, y ∈ T.unitFiltration n →
      ∃ x, x ∈ S.unitFiltration n ∧
        y * (normUnits F.Carrier E.Carrier x)⁻¹ ∈ T.unitFiltration (n + 1) := by
  rintro n _ ⟨y, hy, rfl⟩
  obtain ⟨x, hx, hxy⟩ := happrox n y ((congruence_iff T n y).mp hy)
  refine ⟨S.integerUnitsInclusion x, ⟨x, (congruence_iff S n x).mpr hx, rfl⟩, ?_⟩
  refine ⟨y * (Units.map (Algebra.norm T.Integers) x)⁻¹,
    (congruence_iff T (n + 1) _).mpr hxy, ?_⟩
  rw [map_mul, map_inv, norm_inclusion T S hn]

end Langlands.LocalClassField.UnitNormProof

namespace Langlands.LocalClassField
universe u v

/-- The actual norm maps every unit filtration level onto its counterpart
in an unramified finite p-adic extension. -/
theorem unramifiedUnitNorms : UnramifiedUnitNorms.{u,v} := by
  intro p hp F E hFE hbase hfinite T S he
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := S.topology
  let := S.valuativeRel
  let := S.localField
  let := T.relativeIntegerAlgebra S
  have hdata := T.relativeNormData S (T.relativeIntegerMap S)
    (T.relativeIntegerMap_coe S)
  let := hdata.1
  let := hdata.2.1
  let := T.finite_residueField
  let := S.finite_residueField
  let : IsLocalHom (algebraMap T.Integers S.Integers) := T.relativeIntegerMap_isLocalHom S
  have hmap : Ideal.map (algebraMap T.Integers S.Integers)
      (IsLocalRing.maximalIdeal T.Integers) = IsLocalRing.maximalIdeal S.Integers :=
    T.map_maximalIdeal_of_ramificationIndex_eq S (T.relativeIntegerMap S) he
  obtain ⟨hpres, happrox⟩ := UnramifiedAlgebra.proof T.Integers S.Integers hmap
  have hp' := UnitNormProof.preserves T S hdata.2.2 hpres
  have ha' := UnitNormProof.approximates T S hdata.2.2 happrox
  exact unitFiltrationCompactLifting.{u,v} p F E T S (localNorm T S) hp' ha'

end Langlands.LocalClassField
