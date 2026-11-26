import Langlands.BaseChange.PadicNormTwistFactorComparison
import Langlands.BaseChange.CuspidalSigmaLiftConductorFromArbitraryTraceEpsilon
import Langlands.BaseChange.CyclicNormDeterminant
import Langlands.LocalField.CharZeroPadicRealization
import Langlands.LocalField.SuppliedPadicExtension

/-!
# The norm-trivial count and the trace conductor formula in characteristic zero

Both statements are transported from the supplied p-adic realizations of the
actual fields, where they are proved by local class field theory and the
trace codifferent.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.BaseChange

open CharZeroLocalField LocalField
open HarmonicAnalysis (UnitaryAdditiveCharacter)

universe u v uV uW

/-- `f·n(ψE) = [E:F]·n(ψF) + f·d` for actual characteristic-zero local fields. -/
theorem traceAdditiveConductorFormula : TraceAdditiveConductorFormulaStatement.{u, v} := by
  intro F _ _ _ _ _ E _ _ _ _ _ _ _ f d hf hd ψF ψE htrace
  let p := residueChar F
  let : Fact p.Prime := ⟨residueChar_prime F⟩
  let : Algebra (Padic p) F := padicAlgebra F
  let : FiniteDimensional (Padic p) F := finiteDimensional F
  let K := padicField F
  let T := topologicalData F
  let : Algebra (Padic p) E := Algebra.compHom E (algebraMap (Padic p) F)
  let : IsScalarTower (Padic p) F E := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (Padic p) E := FiniteDimensional.trans (Padic p) F E
  let L := PadicField.ofField (p := p) E
  let : TopologicalSpace K.Carrier := T.topology
  let : Algebra K.Carrier E := (inferInstance : Algebra F E)
  let : IsScalarTower (Padic p) K.Carrier E := (inferInstance : IsScalarTower (Padic p) F E)
  let : FiniteDimensional K.Carrier E := (inferInstance : FiniteDimensional F E)
  let S : L.TopologicalData := suppliedPadicExtension T E
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F E))
  let : TopologicalSpace L.Carrier := S.topology
  let : Algebra K.Carrier L.Carrier := (inferInstance : Algebra F E)
  let : IsScalarTower (Padic p) K.Carrier L.Carrier := (inferInstance : IsScalarTower (Padic p) F E)
  let : FiniteDimensional K.Carrier L.Carrier := (inferInstance : FiniteDimensional F E)
  let : IsModuleTopology K.Carrier L.Carrier := (inferInstance : IsModuleTopology F E)
  have h := residueDegree_mul_additiveConductor_of_trace T S hf hd ψF ψE htrace
  have hE : (LocalFieldData.ofInstances E).additiveConductor ψE = S.additiveConductor ψE :=
    S.toLocalFieldData_additiveConductor ψE
  have hF : (LocalFieldData.ofInstances F).additiveConductor ψF = T.additiveConductor ψF :=
    T.toLocalFieldData_additiveConductor ψF
  rw [hE, hF]
  exact h

/-- A cyclic extension of degree `l` of an actual characteristic-zero local field
has exactly `l` norm-trivial characters. -/
theorem normTrivialCount : NormTrivialCountStatement.{u, v} := by
  intro F _ _ _ _ _ E _ _ _ _ _ _ σ l hcyc X hX
  let p := residueChar F
  let : Fact p.Prime := ⟨residueChar_prime F⟩
  let : Algebra (Padic p) F := padicAlgebra F
  let : FiniteDimensional (Padic p) F := finiteDimensional F
  let K := padicField F
  let : FiniteDimensional F E := hcyc.1
  let : IsAbelianGalois F E := hcyc.isAbelianGalois
  let : Algebra (Padic p) E := Algebra.compHom E (algebraMap (Padic p) F)
  let : IsScalarTower (Padic p) F E := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (Padic p) E := FiniteDimensional.trans (Padic p) F E
  let L := PadicField.ofField (p := p) E
  let : Algebra K.Carrier L.Carrier := (inferInstance : Algebra F E)
  let : FiniteDimensional K.Carrier L.Carrier := (inferInstance : FiniteDimensional F E)
  let : IsAbelianGalois K.Carrier L.Carrier := (inferInstance : IsAbelianGalois F E)
  exact (card_of_mem_iff_isNormTrivial K L X hX).trans hcyc.2.1

/-- Both premises of the arbitrary-character conductor reduction hold for
actual characteristic-zero local fields. -/
def CharZeroTraceConductorPremisesStatement : Prop :=
  NormTrivialCountStatement.{u, v} ∧ TraceAdditiveConductorFormulaStatement.{u, v}

theorem charZeroTraceConductorPremises : CharZeroTraceConductorPremisesStatement.{u, v} :=
  ⟨normTrivialCount, traceAdditiveConductorFormula⟩

/-- Local epsilon data with any trace-related additive characters imply the exact
conductor formula. -/
def CuspidalSigmaLiftConductorFromArbitraryTraceDataStatement : Prop :=
  CuspidalSigmaLiftArbitraryTraceEpsilonDataStatement.{u, v, uV, uW} →
    CuspidalSigmaLiftConductorStatement.{u, v, uV, uW}

theorem cuspidalSigmaLiftConductorFromArbitraryTraceData :
    CuspidalSigmaLiftConductorFromArbitraryTraceDataStatement.{u, v, uV, uW} :=
  cuspidalSigmaLiftConductorFromArbitraryTraceEpsilon normTrivialCount
    traceAdditiveConductorFormula

end Langlands.BaseChange
