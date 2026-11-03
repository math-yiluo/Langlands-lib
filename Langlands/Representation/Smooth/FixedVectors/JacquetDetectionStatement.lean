import Langlands.Representation.Smooth.FixedVectors.CompactRestrictionDetectionStatement
import Langlands.Representation.Jacquet.SmoothTwist
import Langlands.Representation.Jacquet.IwahoriContraction

/-! # Detecting fixed vectors through actual Jacquet subquotients -/

set_option autoImplicit false

namespace Langlands

universe uG uV uI

/-- Internal composition of fixed-vector generation, compact-restriction
detection, compact-open exactness and the weak Jacquet lemma. All structural
and finite compact-restriction inputs remain explicit. -/
def JacquetSubquotientFixedVectorDetectionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (N M Nbar : Subgroup G) (hMN : M ≤ Subgroup.normalizer N),
    IsClosed (M : Set G) →
    (∀ s : Finset N, ∃ L : OpenSubgroup N,
      IsCompact (L : Set N) ∧ ∀ n ∈ s, n ∈ L) →
    ∀ (K : OpenSubgroup G) (K₀ : Subgroup G),
      IsCompact (K : Set G) →
      K₀ ≤ Subgroup.normalizer K.toSubgroup →
      (∀ x : G, ∃ m ∈ M, ∃ n ∈ N, ∃ k ∈ K₀, x = m * n * k) →
      ∀ (g : G), Jacquet.IsIwahoriContraction K N M Nbar g →
      ∀ (H : Subgroup M) [H.Normal]
        [T2Space H] [LocallyCompactSpace H] [TotallyDisconnectedSpace H]
        [MeasurableSpace H] [BorelSpace H]
        (μ : MeasureTheory.Measure H) [μ.IsHaarMeasure],
        K.toSubgroup.comap M.subtype ≤ H →
        ∀ (A D : SmoothRep.{0, uG, uV} ℂ G),
          FiniteDimensional ℂ (fixedVectors A.representation K.toSubgroup) →
          (∀ S : Subrepresentation A.representation,
            fixedVectors A.representation K.toSubgroup ≤ S.toSubmodule → S = ⊤) →
          SmoothRep.IsSubquotient D A →
          let JD := SmoothRep.of (Jacquet.action D.representation N M hMN)
            (Jacquet.isSmooth_action D.representation N M hMN D.isSmooth)
          ∀ (E : SmoothRep.{0, uG, uV} ℂ M)
            (ι : Type uI) [Fintype ι] [Nonempty ι]
            (V : ι → Subrepresentation (SmoothRep.restrictSubgroup H E).representation),
            (∀ i, Representation.IsIrreducible (V i).toRepresentation) →
            (∀ i, HasCompactSmoothDualCoefficients (V i).toRepresentation) →
            (⨆ i, (V i).toSubmodule) = ⊤ →
            SmoothRep.IsSubquotient E JD →
            ∃ v : D, v ∈ fixedVectors D.representation K.toSubgroup ∧ v ≠ 0

end Langlands
