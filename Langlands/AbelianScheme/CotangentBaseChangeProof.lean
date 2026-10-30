import Langlands.AbelianScheme.CotangentBaseChangeStatement
import Langlands.AlgebraicGeometry.RelativeDifferentialsBaseChangeIsIso

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- The canonical cotangent comparison is invertible for arbitrary base change. -/
theorem cotangentBaseChangeIsIso (S : AlgebraicGeometry.Scheme.{u}) :
    CotangentBaseChangeIsIsoStatement S := by
  intro T b G
  have hdiff : IsIso (Langlands.Scheme.relativeDifferentialsBaseChangeMap G.X.hom b) :=
    Langlands.Scheme.relativeDifferentialsBaseChangeIsIso S G.X.left T G.X.hom b
  exact ((cotangentBaseChangePullbackIso b G).app
      (Langlands.Scheme.relativeDifferentials G.X.hom) ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback ((baseChange b).obj G).identitySection).mapIso
      (asIso (Langlands.Scheme.relativeDifferentialsBaseChangeMap G.X.hom b))).isIso_hom

end Langlands.GroupScheme
