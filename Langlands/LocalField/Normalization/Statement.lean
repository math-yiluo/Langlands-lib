import Langlands.LocalField.Normalization.Definitions
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.Topology.Bases

/-! Complete arithmetic and topology laws for finite p-adic field normalization. -/

namespace Langlands

open scoped WithZero

universe u

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

/-- Arithmetic of the actual residue field and its specified prime-field scalars. -/
def ResidueArithmeticLaws : Prop :=
  CharP T.ResidueField p ∧
  Finite T.ResidueField ∧
  (letI := T.residueAlgebra; FiniteDimensional (ZMod p) T.ResidueField) ∧
  Function.Injective T.residueScalarMap ∧
  0 < T.residueDegree ∧
  1 < T.residueCardinality ∧
  T.residueCardinality = p ^ T.residueDegree

/-- The discrete value group, order convention and absolute ramification index. -/
def DiscreteOrderLaws : Prop :=
  Function.Surjective T.discreteValuation ∧
  T.discreteValuation T.uniformizer = WithZero.exp (-1) ∧
  T.ord 0 = 0 ∧
  T.ord 1 = 0 ∧
  T.ord T.uniformizer = 1 ∧
  (∀ (x y : F.Carrier), x ≠ 0 → y ≠ 0 → T.ord (x * y) = T.ord x + T.ord y) ∧
  (∀ x : F.Carrier, T.ord x⁻¹ = -T.ord x) ∧
  (∀ (x y : F.Carrier), x ≠ 0 → y ≠ 0 → x + y ≠ 0 →
    min (T.ord x) (T.ord y) ≤ T.ord (x + y)) ∧
  (∀ n : ℤ, ∃ x : F.Carrier, x ≠ 0 ∧ T.ord x = n) ∧
  0 < T.ord (p : F.Carrier) ∧
  0 < T.ramificationIndex ∧
  (T.ramificationIndex : ℤ) = T.ord (p : F.Carrier)

/-- Multiplicativity and the nonarchimedean inequality for the residue normalization. -/
def ResidueAbsoluteValueLaws : Prop :=
  T.normalizedAbs 0 = 0 ∧
  T.normalizedAbs 1 = 1 ∧
  (∀ x : F.Carrier, 0 ≤ T.normalizedAbs x) ∧
  (∀ x : F.Carrier, x ≠ 0 → 0 < T.normalizedAbs x) ∧
  (∀ x : F.Carrier, x ≠ 0 →
    T.normalizedAbs x = (T.residueCardinality : ℝ) ^ (-T.ord x)) ∧
  (∀ x y : F.Carrier, T.normalizedAbs (x * y) = T.normalizedAbs x * T.normalizedAbs y) ∧
  (∀ x y : F.Carrier,
    T.normalizedAbs (x + y) ≤ max (T.normalizedAbs x) (T.normalizedAbs y)) ∧
  T.normalizedAbs T.uniformizer = (T.residueCardinality : ℝ) ^ (-1 : ℤ)

/-- The actual integer extension is the integral closure and has the field-extension rank. -/
def IntegralExtensionLaws : Prop :=
  (letI := Algebra.compHom F.Carrier
      (algebraMap (ValuativeRel.valuation (Padic p)).integer (Padic p));
    IsIntegralClosure T.Integers (ValuativeRel.valuation (Padic p)).integer F.Carrier) ∧
  (∀ x : F.Carrier,
    letI := Algebra.compHom F.Carrier
      (algebraMap (ValuativeRel.valuation (Padic p)).integer (Padic p));
    IsIntegral (ValuativeRel.valuation (Padic p)).integer x ↔ x ∈ T.Integers) ∧
  (letI := T.integerAlgebra;
    Module.Finite (ValuativeRel.valuation (Padic p)).integer T.Integers ∧
    Module.Free (ValuativeRel.valuation (Padic p)).integer T.Integers ∧
    Module.finrank (ValuativeRel.valuation (Padic p)).integer T.Integers =
      Module.finrank (Padic p) F.Carrier) ∧
  (∀ x : F.Carrier, T.normalizedAbs x ≤ 1 ↔ x ∈ T.Integers) ∧
  (∀ x : F.Carrier, F.canonicalNorm x ≤ 1 ↔ x ∈ T.Integers)

/-- Ramification is measured by actual maximal-ideal powers, and inertia by actual residue degree. -/
def RamificationDegreeLaws : Prop :=
  Ideal.span {(p : T.Integers)} =
    IsLocalRing.maximalIdeal T.Integers ^ T.ramificationIndex ∧
  (letI := T.integerAlgebra;
    (IsLocalRing.maximalIdeal (ValuativeRel.valuation (Padic p)).integer).map
      (algebraMap (ValuativeRel.valuation (Padic p)).integer T.Integers) =
      IsLocalRing.maximalIdeal T.Integers ^ T.ramificationIndex) ∧
  (letI := T.integerAlgebra;
    (IsLocalRing.maximalIdeal T.Integers).ramificationIdx
      (ValuativeRel.valuation (Padic p)).integer = T.ramificationIndex ∧
    (IsLocalRing.maximalIdeal T.Integers).inertiaDeg
      (ValuativeRel.valuation (Padic p)).integer = T.residueDegree) ∧
  T.ramificationIndex * T.residueDegree = Module.finrank (Padic p) F.Carrier ∧
  0 < Module.finrank (Padic p) F.Carrier

/-- Explicit comparison with the base-extending spectral norm, including zero and degree one. -/
def NormalizedComparisonLaws : Prop :=
  (∀ a : Padic p,
    T.ord (algebraMap (Padic p) F.Carrier a) = (T.ramificationIndex : ℤ) * a.valuation) ∧
  (∀ a : Padic p,
    T.normalizedAbs (algebraMap (Padic p) F.Carrier a) =
      ‖a‖ ^ Module.finrank (Padic p) F.Carrier) ∧
  (∀ x : F.Carrier,
    T.normalizedAbs x = F.canonicalNorm x ^ Module.finrank (Padic p) F.Carrier) ∧
  (Module.finrank (Padic p) F.Carrier = 1 →
    T.ramificationIndex = 1 ∧ T.residueDegree = 1 ∧ T.residueCardinality = p ∧
    ∀ x : F.Carrier, T.normalizedAbs x = F.canonicalNorm x)

/-- Positive-radius absolute-value balls generate the specified and canonical module topologies. -/
def NormalizationTopologyLaws : Prop :=
  T.topology = F.canonicalTopology ∧
  T.topology = (letI := F.canonicalNormedField;
    inferInstance : TopologicalSpace F.Carrier) ∧
  (letI := T.topology;
    TopologicalSpace.IsTopologicalBasis
      {U : Set F.Carrier | ∃ (a : F.Carrier) (ε : ℝ),
        0 < ε ∧ U = {x | T.normalizedAbs (x - a) < ε}}) ∧
  TopologicalSpace.generateFrom
    {U : Set F.Carrier | ∃ (a : F.Carrier) (ε : ℝ),
      0 < ε ∧ U = {x | T.normalizedAbs (x - a) < ε}} = T.topology ∧
  TopologicalSpace.generateFrom
    {U : Set F.Carrier | ∃ (a : F.Carrier) (ε : ℝ),
      0 < ε ∧ U = {x | T.normalizedAbs (x - a) < ε}} = F.canonicalTopology

end PadicField.TopologicalData

/-- Basic arithmetic normalization for every finite p-adic field with specified topology data. -/
def PadicNormalizationBasicStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
    T.ResidueArithmeticLaws ∧ T.DiscreteOrderLaws ∧ T.ResidueAbsoluteValueLaws

/-- Complete arithmetic normalization for every finite p-adic field with specified topology data. -/
def PadicNormalizationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
    T.ResidueArithmeticLaws ∧ T.DiscreteOrderLaws ∧ T.ResidueAbsoluteValueLaws ∧
    T.IntegralExtensionLaws ∧ T.RamificationDegreeLaws ∧ T.NormalizedComparisonLaws ∧
    T.NormalizationTopologyLaws

end Langlands
