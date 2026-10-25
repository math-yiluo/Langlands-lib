import Langlands.Representation.Exponents.DualJacquetStatement
import Langlands.Representation.Classification.ParabolicConeStatement
import Langlands.Representation.Twist.LeviRealPower

/-!
# Maximal-cone selection of an essentially tempered Jacquet quotient

This proposition uses dominance of positive parts, following Konno 2003,
Lemmas 3.3–3.4 and Theorem 3.5(i). It corrects the block-cardinality selection
previously transcribed from Silberger 1978, Proposition 7.2.
-/

namespace Langlands

open GeneralLinear
open scoped BigOperators

universe uF uV

/-- Strict dominance of block positive parts in standard GL coordinates.
The first vector dominates the second: totals agree, every prefix sum is at
least as large, and some prefix sum is strictly larger. The endpoints are
included, so the order retains the common central value. -/
def GLBlockPositivePartStrictlyDominates {n : ℕ}
    (C₁ : BlockShape n) (t₁ : Fin C₁.length → ℝ)
    (C₂ : BlockShape n) (t₂ : Fin C₂.length → ℝ) : Prop :=
  let Λ₁ : Fin n → ℝ := fun i => t₁ ((C₁.indexEquiv.symm i).1)
  let Λ₂ : Fin n → ℝ := fun i => t₂ ((C₂.indexEquiv.symm i).1)
  (∑ i, Λ₁ i) = (∑ i, Λ₂ i) ∧
    (∀ k : Fin (n + 1),
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k.val), Λ₂ i) ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k.val), Λ₁ i) ∧
    ∃ k : Fin (n + 1),
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k.val), Λ₂ i) <
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k.val), Λ₁ i

/-- An actual dual exponent admits a dominance-maximal consecutive cone coarsening whose
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
            ¬ GLBlockPositivePartStrictlyDominates C' t' C t)

end Langlands
