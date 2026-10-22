import Langlands.Geometry.Analytic.RationalLocalization.Definitions

/-! # Spectrum-image criterion for factorization through rational quotients -/

universe u

namespace Langlands.Analytic.RationalFactorization

/-- Among presented strict affinoid test algebras, containment of the
contravariant spectrum image characterizes unique bounded factorization
through the actual rational quotient. -/
def FactorizationStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PresentedStrictAffinoidAlgebra K) (m : ℕ) (g : P) (f : Fin m → P),
    RationalLocalization.GeneratesUnitIdeal K P m g f →
    ∀ (Q : PresentedStrictAffinoidAlgebra K) (φ : BoundedAlgHom K P Q),
      (∀ x : BanachSpectrum Q,
        BanachSpectrum.comap φ.toBoundedRingHom x ∈
          RationalLocalization.locus K P m g f) ↔
      ∃! ψ : BoundedAlgHom K (RationalLocalization.algebra K P m g f) Q,
        ψ.comp (RationalLocalization.baseMap K P m g f) = φ

end Langlands.Analytic.RationalFactorization
