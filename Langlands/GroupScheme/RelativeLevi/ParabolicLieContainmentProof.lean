import Langlands.GroupScheme.RelativeLevi.ParabolicLieContainmentStatement
import Langlands.GroupScheme.RelativeLevi.FieldLieContainment
import Langlands.GroupScheme.RelativeLevi.TorusContainment

/-! # Parabolic Lie containment spreads to a Zariski neighbourhood -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- Containment of parabolic tangent submodules at one residue fibre spreads
to containment of the subgroup functors on a neighbourhood of that point. -/
theorem relativeParabolicLieContainment :
    RelativeParabolicLieContainmentStatement.{u} := by
  intro S G P Q i j T t s hG hi hj hT _ ht hTP hTQ hlie
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let b := S.fromSpecResidueField s
  let : IsAffineHom ((baseChange b).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom b))
  have hTPs : SubgroupFunctor.range ((baseChange b).map t) ≤
      SubgroupFunctor.range ((baseChange b).map i) := by
    simpa only [SubgroupFunctor.range_baseChangeHom] using
      SubgroupFunctor.baseChange_mono b hTP
  have hTQs : SubgroupFunctor.range ((baseChange b).map t) ≤
      SubgroupFunctor.range ((baseChange b).map j) := by
    simpa only [SubgroupFunctor.range_baseChangeHom] using
      SubgroupFunctor.baseChange_mono b hTQ
  have hs : SubgroupFunctor.range ((baseChange b).map j) ≤
      SubgroupFunctor.range ((baseChange b).map i) :=
    RelativeLevi.parabolic_range_le_of_lie_le
      (T := (CommGroupScheme.baseChange b).obj T)
      (hG.isConnectedReductive_residueFiber s)
      ((baseChange b).map i) ((baseChange b).map j)
      (hi.residueFiber s) (hj.residueFiber s)
      ((baseChange b).map t) (ht s) hTPs hTQs hlie
  exact RelativeLevi.exists_open_range_le_of_torus_residueFiber
    hG i j hi hj T t hT ht s hTP hTQ hs

end Langlands.GroupScheme
