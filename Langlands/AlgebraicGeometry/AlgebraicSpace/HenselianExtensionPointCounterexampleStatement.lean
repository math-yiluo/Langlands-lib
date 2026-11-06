import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianExtensionPointEmbeddingStatement
import Mathlib.FieldTheory.Separable
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# The closed-embedding property fails without separated open covers

Conrad's Example 5.13: over a complete non-archimedean field `K` with a separable quadratic
extension `K'`, there is a quasi-separated algebraic space locally of finite type whose
diagonal is an affine immersion, for which the image of `X(K)` in `X_{K'}(K')` is not closed.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Conrad's Example 5.13 (printed p.20): let `K` be a field complete for a nontrivial
non-archimedean absolute value and `K'/K` a separable quadratic extension. There is a
quasi-separated algebraic space `X` locally of finite type over `Spec K`, whose diagonal is
representable with every represented projection an affine immersion, such that the image of
the map `X(K) → X_{K'}(K')` is not closed for the étale-chart topology over `K'`. -/
def HenselianExtensionPointNotClosedStatement : Prop :=
  ∀ (K K' : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [NontriviallyNormedField K'] [NormedAlgebra K K'],
    Module.finrank K K' = 2 → Algebra.IsSeparable K K' →
    ∃ X : AlgebraicSpace (Spec (CommRingCat.of K)),
      IsQuasiSeparatedLocallyFiniteType K X ∧
      (MorphismProperty.inverseImage
          (@_root_.AlgebraicGeometry.IsImmersion.{u} ⊓ @_root_.AlgebraicGeometry.IsAffineHom.{u})
          (Over.forget _)).relative (schemeYoneda _) (diag X.presheaf) ∧
      ¬ @IsClosed _ (etaleChartTopology K' (baseChange (Spec.algebraMap K K') X))
        (Set.range fun x : RingPoints K X K =>
          (baseChangeRingPointsEquiv K K' K' X).symm (RingPoints.changeRing (Algebra.ofId K K') x))

end Langlands.AlgebraicGeometry.AlgebraicSpace
