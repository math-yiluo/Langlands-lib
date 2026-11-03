import Langlands.Representation.Aubert.General.JacquetAdmissibility
import Langlands.Representation.Exponents.Central

/-! # Strict normalized Jacquet exponents bound compact compression -/

namespace Langlands

universe uG uV

/-- Under explicit Iwahori contraction data, strict full-center exponents
of the actual normalized Jacquet module bound every eigenvalue of compact
compression after multiplication by the actual inverse half modulus. -/
def NormalizedJacquetCompressionSpectrumStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
    [NonarchimedeanGroup G] (N M Nbar : Subgroup G)
    (hN : IsClosed (N : Set G)) (hMN : M ≤ Subgroup.normalizer N),
    Jacquet.HasIwahoriContractionBasis N M Nbar →
    ∀ (A : SmoothRep.{0, uG, uV} ℂ G) (hA : A.IsAdmissible)
      (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
      (z : Subgroup.center M),
      Jacquet.IsIwahoriContraction K N M Nbar ((z : M) : G) →
      (∀ χ : Subgroup.center M →* ℂˣ,
        IsCentralExponent
          ((Aubert.General.normalizedJacquetFunctor N M hN hMN).obj A).representation χ →
        ‖(χ z : ℂ)‖ < 1) →
      ∀ (μ : ℂ) (x : fixedVectors A.representation K.toSubgroup),
        x ≠ 0 →
        Jacquet.compressedAction A.representation hA.1 K hK ((z : M) : G) x = μ • x →
        ‖(HaarModulus.closedInverseHalfCharacter N hN M hMN (z : M) : ℂ) * μ‖ < 1

end Langlands
