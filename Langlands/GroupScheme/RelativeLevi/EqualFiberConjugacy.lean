import Langlands.GroupScheme.Dynamic.CompatiblePresentations
import Langlands.GroupScheme.Dynamic.FieldPointConjugacy

/-! # Etale conjugacy of relative parabolics with equal residue fibres -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G P Q : GroupScheme S}

/-- Relative parabolics with equal residue-fibre subgroup ranges are
conjugate on an etale neighbourhood containing the given point. -/
def relativeParabolicConjugacyOfEqualResidue
    (i : P ⟶ G) (j : Q ⟶ G) (hG : IsReductive G)
    (hi : IsRelativeParabolicSubgroup i) (hj : IsRelativeParabolicSubgroup j)
    (s : S)
    (heq : SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map i) =
      SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map j)) :
    Dynamic.EtaleSubgroupConjugacyData i j s := by
  let C := Dynamic.compatiblePresentations i j hG hi hj s heq
  let hGU := hG.baseChange C.projection
  let : Smooth ((baseChange C.projection).obj G).X.hom := hGU.smooth
  let : IsAffineHom ((baseChange C.projection).obj G).X.hom := hGU.isAffineHom
  let : Etale C.projection := C.etale
  let d := Dynamic.etaleConjugacyOfFieldPointPresentations
    ((baseChange C.projection).map i) ((baseChange C.projection).map j)
    C.leftCocharacter C.rightCocharacter C.leftPresents C.rightPresents
    C.point C.compatible
  have hpoint : C.projection (C.point (IsLocalRing.closedPoint (S.residueField s))) = s := by
    change (C.point ≫ C.projection) _ = s
    rw [C.point_projection, Scheme.fromSpecResidueField_apply]
  exact hpoint ▸ Dynamic.EtaleSubgroupConjugacyData.comp C.projection i j
    (C.point (IsLocalRing.closedPoint (S.residueField s))) d

end Langlands.GroupScheme
