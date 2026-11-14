import Langlands.Automorphic.Unramified.CuspidalSpectralRigidityStatement
import Langlands.Automorphic.Unramified.IsobaricWeakTransfer

/-! # The isobaric invariance step in Harris's Proposition 4.8 -/

noncomputable section

universe uV

namespace Langlands.Global.Harris

open Langlands.Automorphic Langlands.Automorphic.Unramified Langlands.Unramified

/-- Constituent rigidity upgrades equality of supplied Euler systems to
Galois invariance of the actual isobaric multiset. -/
def Proposition48IsobaricInvarianceStatement : Prop :=
  CuspidalSpectralRigidityStatement.{0, uV} →
    ∀ (F K : Type) [Field F] [Field K] [NumberField K] [Algebra F K]
      [CompactSpace (AdeleQuotient K)] (σ : K ≃ₐ[F] K) (D : IsobaricData K)
      (s : SpectralSystem (FinitePlace K) D.rank)
      (t : SpectralSystem (FinitePlace K) (D.galoisConj σ).rank),
      D.HasSpectralSystem.{0, uV} s →
      (D.galoisConj σ).HasSpectralSystem.{0, uV} t →
      s.SameEulerPolynomials t → D.IsGaloisStable σ

end Langlands.Global.Harris
