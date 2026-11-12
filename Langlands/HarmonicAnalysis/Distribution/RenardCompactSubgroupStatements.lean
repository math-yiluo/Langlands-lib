import Langlands.HarmonicAnalysis.Distribution.CompactSubgroup
import Langlands.HarmonicAnalysis.Distribution.Convolution
import Langlands.HarmonicAnalysis.GroupAction

/-! # Renard II.3.11: normalized compact-subgroup formulas -/

noncomputable section

open MeasureTheory
open scoped Pointwise

namespace Langlands.HarmonicAnalysis.Distribution.RenardCompactSubgroup

universe uG

/-- The defining integral on all locally constant functions, using the existing
extended pairing rather than an arbitrary extension of a distribution. -/
def ExtendedIntegralStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (K : Subgroup G) (hK : IsCompact (K : Set G)) (f : LocallyConstant G ℂ),
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    letI : MeasurableSpace K := borel K
    letI : BorelSpace K := ⟨rfl⟩
    compactSupportPairing (compactSubgroupHaar K hK) f =
      ∫ k : K, f k.val ∂(Measure.haarMeasure ⊤)

/-- The explicit convolution has the support, invariance and normalization in
the Lemma; every compact distribution with those properties equals it. -/
def DoubleCosetUniquenessStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (K L : Subgroup G) (hK : IsCompact (K : Set G))
    (hL : IsCompact (L : Set G)) (g : G),
    let A := convolution (convolution (compactSubgroupHaar K hK) (compactDirac g))
      (compactSubgroupHaar L hL)
    support (A : Distribution G) ⊆ (K : Set G) * {g} * (L : Set G) ∧
      (∀ k : K, GroupAction.leftDistributions k.val (A : Distribution G) = A) ∧
      (∀ l : L, GroupAction.rightDistributions l.val (A : Distribution G) = A) ∧
      compactSupportPairing A 1 = 1 ∧
      ∀ T : compactlySupported (X := G),
        support (T : Distribution G) ⊆ (K : Set G) * {g} * (L : Set G) →
        (∀ k : K, GroupAction.leftDistributions k.val (T : Distribution G) = T) →
        (∀ l : L, GroupAction.rightDistributions l.val (T : Distribution G) = T) →
        compactSupportPairing T 1 = 1 → T = A

/-- Proposition (i), including both orders of convolution. The set product is
required to be the underlying set of the supplied compact subgroup. -/
def ProductStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (K L M : Subgroup G) (hK : IsCompact (K : Set G))
    (hL : IsCompact (L : Set G)) (hM : IsCompact (M : Set G)),
    (M : Set G) = (K : Set G) * (L : Set G) →
    compactSubgroupHaar M hM = convolution (compactSubgroupHaar K hK)
      (compactSubgroupHaar L hL) ∧
    compactSubgroupHaar M hM = convolution (compactSubgroupHaar L hL)
      (compactSubgroupHaar K hK)

/-- Proposition (ii), on the actual image of K under Mathlib conjugation. -/
def ConjugationStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (K : Subgroup G) (hK : IsCompact (K : Set G)) (g : G),
    ∃ hKg : IsCompact ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G),
      convolution (convolution (compactDirac g) (compactSubgroupHaar K hK))
        (compactDirac g⁻¹) = compactSubgroupHaar (K.map (MulAut.conj g).toMonoidHom) hKg

/-- The stated idempotence and absorption consequences for arbitrary compact
subgroups, including subgroups that are not open. -/
def IdempotenceAbsorptionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G],
    (∀ (K : Subgroup G) (hK : IsCompact (K : Set G)),
      convolution (compactSubgroupHaar K hK) (compactSubgroupHaar K hK) =
        compactSubgroupHaar K hK) ∧
    ∀ (K L : Subgroup G) (hK : IsCompact (K : Set G)) (hL : IsCompact (L : Set G)),
      K ≤ L →
      convolution (compactSubgroupHaar K hK) (compactSubgroupHaar L hL) =
        compactSubgroupHaar L hL ∧
      convolution (compactSubgroupHaar L hL) (compactSubgroupHaar K hK) =
        compactSubgroupHaar L hL

def Statements : Prop :=
  ExtendedIntegralStatement.{uG} ∧ DoubleCosetUniquenessStatement.{uG} ∧
    ProductStatement.{uG} ∧ ConjugationStatement.{uG} ∧
    IdempotenceAbsorptionStatement.{uG}

end Langlands.HarmonicAnalysis.Distribution.RenardCompactSubgroup
