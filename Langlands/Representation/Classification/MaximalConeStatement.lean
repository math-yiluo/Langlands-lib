import Langlands.Representation.Exponents.DualJacquetStatement
import Langlands.Representation.Classification.ParabolicConeStatement
import Langlands.Representation.Twist.LeviRealPower

/-!
# Maximal-cone selection of an essentially tempered Jacquet quotient

This proposition spells out the representation-theoretic selection in the
proof of Silberger 1978, Proposition 7.2, in actual GL block coordinates.
-/

namespace Langlands

open GeneralLinear
open scoped BigOperators

universe uF uV

/-- An actual dual exponent admits a maximal consecutive cone coarsening whose
restricted character supports an irreducible quotient of the whole opposite
Jacquet module, tempered after removal of its real determinant character. -/
def GLMaximalConeJacquetQuotientStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ A : Rep.{uV} ℂ (GeneralLinear n F.Carrier),
      Representation.IsIrreducible A.ρ → IsAdmissible A.ρ →
        ∃ (B : BlockShape n) (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
          (r : Fin B.length → ℝ) (C : BlockShape n)
          (q : Fin B.length → Fin C.length) (t : Fin C.length → ℝ)
          (χC : (Fin C.length → F.Carrierˣ) →* ℂˣ)
          (S : Rep.{uV} ℂ (C.Levi F.Carrier)),
          T.IsDualJacquetExponent B A χ ∧ T.IsRealPartOf χ r ∧
          Monotone q ∧ Function.Surjective q ∧
          (∀ j, C.size j = ∑ i ∈ Finset.univ.filter (fun i => q i = j), B.size i) ∧
          StrictAnti t ∧
          (∀ j, (∑ i ∈ Finset.univ.filter (fun i => q i = j), r i) =
            (C.size j : ℝ) * t j) ∧
          (∀ i, (∑ k ∈ Finset.univ.filter (fun k => q k = q i ∧ k ≤ i),
            (r k - (B.size k : ℝ) * t (q i))) ≤ 0) ∧
          B.parabolic F.Carrier ≤ C.parabolic F.Carrier ∧
          B.leviSubgroup F.Carrier ≤ C.leviSubgroup F.Carrier ∧
          (∀ a : Fin C.length → F.Carrierˣ, χC a = χ (a ∘ q)) ∧
          T.IsDualJacquetExponent C A χC ∧
          T.IsRealPartOf χC (fun j => (C.size j : ℝ) * t j) ∧
          Representation.IsIrreducible S.ρ ∧ IsAdmissible S.ρ ∧
          Classification.HasScalarCharacter S.ρ (C.blockScalarLevi F.Carrier) χC ∧
          (∃ f : (CuspidalJacquetMultiplicity.oppositeJacquet T C A).ρ.IntertwiningMap S.ρ,
            Function.Surjective f) ∧
          (letI := T.leviTopologicalGroup C
           let Q := C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)
           ∀ [MeasurableSpace Q] [BorelSpace Q]
             (μ : MeasureTheory.Measure Q) [MeasureTheory.Measure.IsHaarMeasure μ],
             IsTemperedModCenter (T.leviRealPowerTwist C (-t) S.ρ) μ) ∧
          (∀ (B' : BlockShape n) (χ' : (Fin B'.length → F.Carrierˣ) →* ℂˣ)
            (r' : Fin B'.length → ℝ) (C' : BlockShape n)
            (q' : Fin B'.length → Fin C'.length) (t' : Fin C'.length → ℝ),
            T.IsDualJacquetExponent B' A χ' → T.IsRealPartOf χ' r' →
            Monotone q' → Function.Surjective q' →
            (∀ j, C'.size j =
              ∑ i ∈ Finset.univ.filter (fun i => q' i = j), B'.size i) →
            StrictAnti t' →
            (∀ j, (∑ i ∈ Finset.univ.filter (fun i => q' i = j), r' i) =
              (C'.size j : ℝ) * t' j) →
            (∀ i, (∑ k ∈ Finset.univ.filter (fun k => q' k = q' i ∧ k ≤ i),
              (r' k - (B'.size k : ℝ) * t' (q' i))) ≤ 0) →
            C'.length ≤ C.length)

end Langlands
