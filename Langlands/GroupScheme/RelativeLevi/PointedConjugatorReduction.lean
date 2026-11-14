import Langlands.GroupScheme.PointedEtaleLift
import Langlands.GroupScheme.Descent.Data
import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport

/-! # Removing a prescribed residue-field conjugator -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G P Q : GroupScheme S} {s : S}
  {g₀ : Over.mk (𝟙 (Spec (S.residueField s))) ⟶
    ((baseChange (S.fromSpecResidueField s)).obj G).X}

namespace PointedEtaleGroupPointData

variable (d : PointedEtaleGroupPointData G s g₀)

/-- The lift recovers the original point under the actual iterated-pullback comparison. -/
theorem point_pullbackComparison :
    baseChangeBasePoint d.residuePoint ((baseChange d.projection).obj G) d.point ≫
        (Descent.pullbackComparison d.projection d.residuePoint
          (S.fromSpecResidueField s) d.residue_over G).hom.hom.hom = g₀ := by
  apply (baseChangeBasePointsEquiv (S.fromSpecResidueField s) G).injective
  apply Over.OverMorphism.ext
  rw [baseChangeBasePointsEquiv_left, baseChangeBasePointsEquiv_left]
  change ((baseChangeBasePoint d.residuePoint ((baseChange d.projection).obj G)
      d.point).left ≫
    (Descent.pullbackComparison d.projection d.residuePoint
      (S.fromSpecResidueField s) d.residue_over G).hom.hom.hom.left) ≫
      pullback.fst G.X.hom (S.fromSpecResidueField s) = _
  rw [Category.assoc, Descent.pullbackComparison_hom_fst, ← Category.assoc,
    baseChangeBasePoint_fst]
  exact d.recovers.trans (baseChangeBasePointsEquiv_left _ _ _)

/-- Inner conjugation by the lift specializes to inner conjugation by the given point. -/
theorem innerIso_pullbackComparison :
    (baseChange d.residuePoint).map
        (((baseChange d.projection).obj G).innerIso d.point).hom ≫
      (Descent.pullbackComparison d.projection d.residuePoint
        (S.fromSpecResidueField s) d.residue_over G).hom =
    (Descent.pullbackComparison d.projection d.residuePoint
        (S.fromSpecResidueField s) d.residue_over G).hom ≫
      (((baseChange (S.fromSpecResidueField s)).obj G).innerIso g₀).hom := by
  rw [baseChange_innerIso_hom, innerIso_hom_comp, d.point_pullbackComparison]

/-- After lifting the prescribed conjugator, the two conjugated families have equal
all-test subgroup ranges over the chosen residue-field point of the neighbourhood. -/
theorem range_baseChange_conjugated_eq (i : P ⟶ G) (j : Q ⟶ G)
    (h : SubgroupFunctor.range
      ((baseChange (S.fromSpecResidueField s)).map i ≫
        (((baseChange (S.fromSpecResidueField s)).obj G).innerIso g₀).hom) =
      SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map j)) :
    SubgroupFunctor.range ((baseChange d.residuePoint).map
      ((baseChange d.projection).map i ≫
        (((baseChange d.projection).obj G).innerIso d.point).hom)) =
      SubgroupFunctor.range
        ((baseChange d.residuePoint).map ((baseChange d.projection).map j)) := by
  apply (SubgroupFunctor.range_comp_iso_eq_iff _ _
    (Descent.pullbackComparison d.projection d.residuePoint
      (S.fromSpecResidueField s) d.residue_over G)).mp
  rw [Functor.map_comp, Category.assoc, d.innerIso_pullbackComparison,
    ← Category.assoc, Descent.pullbackComparison_naturality,
    Category.assoc, Descent.pullbackComparison_naturality,
    SubgroupFunctor.range_iso_comp, SubgroupFunctor.range_iso_comp]
  exact h

end PointedEtaleGroupPointData

/-- A pointed étale lift of a conjugator, with the equality of the two specialized
subgroup ranges retained over the supplied residue-field point. -/
structure PointedEtaleConjugatorData (i : P ⟶ G) (j : Q ⟶ G)
    (g₀ : Over.mk (𝟙 (Spec (S.residueField s))) ⟶
      ((baseChange (S.fromSpecResidueField s)).obj G).X)
    extends PointedEtaleGroupPointData G s g₀ where
  ranges_eq :
    SubgroupFunctor.range ((baseChange residuePoint).map
      ((baseChange projection).map i ≫
        (((baseChange projection).obj G).innerIso point).hom)) =
      SubgroupFunctor.range
        ((baseChange residuePoint).map ((baseChange projection).map j))

/-- Lift a prescribed residue-field conjugator of a smooth group and retain
its exact specialized equal-range condition. -/
def pointedEtaleConjugator [Smooth G.X.hom] (i : P ⟶ G) (j : Q ⟶ G)
    (g₀ : Over.mk (𝟙 (Spec (S.residueField s))) ⟶
      ((baseChange (S.fromSpecResidueField s)).obj G).X)
    (h : SubgroupFunctor.range
      ((baseChange (S.fromSpecResidueField s)).map i ≫
        (((baseChange (S.fromSpecResidueField s)).obj G).innerIso g₀).hom) =
      SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map j)) :
    PointedEtaleConjugatorData i j g₀ := by
  let d := pointedEtaleGroupPoint G s g₀
  exact
    { toPointedEtaleGroupPointData := d
      ranges_eq := d.range_baseChange_conjugated_eq i j h }

end Langlands.GroupScheme
