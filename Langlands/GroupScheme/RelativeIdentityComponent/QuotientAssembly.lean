import Langlands.GroupScheme.RelativeIdentityComponent.SmoothNormalityProof
import Langlands.GroupScheme.HomogeneousQuotientGroup
import Langlands.GroupScheme.OpenSubgroupQuotientEtale

/-! # Group structure on supplied identity-component quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeIdentityComponent

variable {S : Scheme.{u}} {G H : GroupScheme S} [Smooth G.X.hom]
  {i : H ⟶ G} (hi : IsRelativeIdentityComponent G i)
  (D : HomogeneousQuotientFromEmbedding.HomogeneousQuotient i)

/-- The quotient group on a supplied actual homogeneous quotient by the
relative identity component. -/
abbrev homogeneousQuotientGroupScheme : GroupScheme S :=
  D.groupScheme (smoothNormality S G inferInstance H i hi)

/-- The supplied homogeneous projection as a quotient homomorphism. -/
def homogeneousQuotientProjection : G ⟶ homogeneousQuotientGroupScheme hi D :=
  D.groupProjection (smoothNormality S G inferInstance H i hi)

/-- The underlying map is the supplied homogeneous projection. -/
theorem homogeneousQuotientProjection_hom :
    (homogeneousQuotientProjection hi D).hom.hom = D.projection := rfl

/-- The quotient homomorphism has the required fppf geometry and kernel. -/
theorem homogeneousQuotientProjection_isFppfQuotient :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i)
      (homogeneousQuotientProjection hi D) :=
  D.groupProjection_isFppfQuotient (smoothNormality S G inferInstance H i hi)

/-- The quotient group is étale over the base. -/
theorem homogeneousQuotientGroupScheme_etale :
    Etale (homogeneousQuotientGroupScheme hi D).X.hom := by
  let : IsOpenImmersion i.hom.hom.left := hi.isOpenImmersion
  let : Smooth D.projection.left := D.smooth_projection
  let : Surjective D.projection.left := D.surjective_projection
  exact etale_of_open_subgroup_quotient i hi.isOpenImmersion D.projection D.fibers

include hi D in
/-- A supplied homogeneous quotient by the relative identity component
has all the group-quotient geometry required by the clopen theorem. -/
theorem exists_etale_fppfQuotient_of_homogeneousQuotient :
    ∃ (E : GroupScheme S) (q : G ⟶ E),
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q ∧
        Etale E.X.hom ∧ IsSeparated E.X.hom ∧ QuasiCompact E.X.hom :=
  ⟨homogeneousQuotientGroupScheme hi D, homogeneousQuotientProjection hi D,
    homogeneousQuotientProjection_isFppfQuotient hi D,
    homogeneousQuotientGroupScheme_etale hi D, D.separated, D.quasiCompact⟩

end Langlands.GroupScheme.RelativeIdentityComponent
