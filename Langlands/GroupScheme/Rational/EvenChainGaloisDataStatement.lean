import Langlands.GroupScheme.Rational.EvenChainPatternProducts
import Langlands.GroupScheme.Rational.QuasiSplitPinningOrbitPairs
import Langlands.GroupScheme.GaloisPointRational

/-! # Statement: Galois-stable even-path pattern products for pairing-compatible pinnings -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- For pairing-compatible pinning data over a finite Galois extension, there are even-path
data, ordered middle-out, whose set of pattern products is stable under the Galois action on
rational points of the base change (Steinberg 1965, 9.3, 9.4 and the proof of 9.7 e)). -/
def EvenChainGaloisDataStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom],
    letI : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom :=
      inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k K)))
    ∀ D : PairingCompatiblePinningData k K G,
      ∃ (J : Type u) (_ : Fintype J) (C : D.pinning.EvenChainData J) (r q : ℕ)
        (o : Fin r ≃ J) (e : Fin q ≃ C.Rest),
        C.IsMiddleOut e ∧
          ∀ (σ : K ≃ₐ[k] K) (g : rationalPoints (GaloisPointComparison.baseChanged k K G)),
            g ∈ C.patternSet D.rootMaps
                (SplitPinning.canonicalSimpleReflectionRepresentatives D.rootMaps) o e →
              GaloisPointComparison.rationalConjugate k K G σ g ∈ C.patternSet D.rootMaps
                (SplitPinning.canonicalSimpleReflectionRepresentatives D.rootMaps) o e

end Langlands.GroupScheme
