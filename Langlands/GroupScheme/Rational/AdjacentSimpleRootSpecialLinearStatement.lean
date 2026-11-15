import Langlands.GroupScheme.Rational.OrthogonalOrbitSpecialLinear
import Langlands.GroupScheme.SpecialLinearTernaryPresentation

/-! # Ternary special linear homomorphisms at adjacent simple roots: statement -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Ternary `SL` at an `A₂` pair of simple roots.** Let `p` be a split pinning of a group
scheme `G` over a field `k`, with normalized simple-root parametrizations `x`, and let `a, b`
be simple roots with `⟨a, b^∨⟩ = ⟨b, a^∨⟩ = -1`. Then some homomorphism
`φ : SL₃(k) →* G(k)` restricts, on the upper-left block copy of `SL₂(k)` (indices `0, 1`), to
the rank-one homomorphism `rootSL2 x a` of `a` and, on the lower-right block copy (indices
`1, 2`), to the rank-one homomorphism `rootSL2 x b` of `b`. -/
def AdjacentSimpleRootSpecialLinearStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : SplitPinning G) (x : p.NormalizedSimpleRootParametrizations) (a b : p.base.support),
    p.rootDatum.pairing a b = -1 → p.rootDatum.pairing b a = -1 →
      ∃ φ : Matrix.SpecialLinearGroup (Fin 3) k →* rationalPoints G,
        φ.comp SpecialLinear.TernaryPresentation.left = SplitPinning.rootSL2 x a ∧
          φ.comp SpecialLinear.TernaryPresentation.right = SplitPinning.rootSL2 x b

end Langlands.GroupScheme
