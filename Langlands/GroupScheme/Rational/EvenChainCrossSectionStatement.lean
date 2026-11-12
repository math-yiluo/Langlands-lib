import Langlands.GroupScheme.Rational.EvenChainPatternProducts
import Langlands.GroupScheme.Rational.ClassFunctions
import Langlands.GroupScheme.SimplyConnected.Basic

/-! # Statement: the split even-path cross-section of the canonical class quotient -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- For a simply connected group with a supplied split pinning over an arbitrary field, every
rational point of the canonical class-function quotient is the image of exactly one rational
point in the set of pattern products of any supplied even-path data, ordered middle-out
(Steinberg 1965, 9.11–9.19, for the actual canonical quotient). -/
def SplitEvenChainCrossSectionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : SplitPinning G), IsSimplyConnected G →
    ∀ (x : p.NormalizedSimpleRootParametrizations) (J : Type u) [Fintype J]
      (C : p.EvenChainData J) (r q : ℕ) (o : Fin r ≃ J) (e : Fin q ≃ C.Rest),
      C.IsMiddleOut e →
      ∀ w : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ ClassFunctions.quotient G,
        ∃! g : rationalPoints G,
          g ∈ C.patternSet x (SplitPinning.canonicalSimpleReflectionRepresentatives x) o e ∧
            g ≫ ClassFunctions.rho G = w

end Langlands.GroupScheme
