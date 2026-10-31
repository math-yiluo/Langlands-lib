import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Langlands.AlgebraicGeometry.Modules.Tensor
import Langlands.AlgebraicGeometry.Picard.LineBundle
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Algebra.DirectSum.Module

/-! # Coherent Künneth over a field for external tensor products of line bundles -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

open Langlands.AlgebraicGeometry.Picard

/-- Over a field `K`, let `X` and `Y` be smooth proper `K`-schemes, `P = X ×_K Y` their
chosen categorical product in `Over (Spec K)` with projections `p₁`, `p₂`, and let `L`, `M`
be line bundles on `X` and `Y`. In every degree `n` there is a `K`-linear isomorphism
`Hⁿ(P, p₁^* L ⊗ p₂^* M) ≅ ⨁_{a + b = n} Hᵃ(X, L) ⊗_K Hᵇ(Y, M)`, where each `H` is the
actual right-derived `K`-module cohomology `DerivedSections.relativeCohomology` along the
structure morphism. This proposition is a statement target, not a proof. -/
def CoherentFieldExternalTensorKunnethStatement : Prop :=
  ∀ (K : Type u) [Field K] (X Y : Over (Spec (CommRingCat.of K)))
    [Smooth X.hom] [IsProper X.hom] [Smooth Y.hom] [IsProper Y.hom]
    (L : LineBundle X.left) (M : LineBundle Y.left) (n : ℕ),
      let P : Over (Spec (CommRingCat.of K)) := X ⨯ Y
      Nonempty ((DerivedSections.relativeCohomology P.hom n).obj
          (Langlands.Scheme.Modules.tensorObj
            ((AlgebraicGeometry.Scheme.Modules.pullback (Limits.prod.fst : P ⟶ X).left).obj L.obj)
            ((AlgebraicGeometry.Scheme.Modules.pullback (Limits.prod.snd : P ⟶ Y).left).obj
              M.obj)) ≅
        ModuleCat.of K (DirectSum {ab : ℕ × ℕ // ab.1 + ab.2 = n} fun ab =>
          TensorProduct K ((DerivedSections.relativeCohomology X.hom ab.1.1).obj L.obj)
            ((DerivedSections.relativeCohomology Y.hom ab.1.2).obj M.obj)))

end Langlands.AlgebraicGeometry.Modules
