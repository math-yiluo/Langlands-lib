import Langlands.GroupScheme.RelativeLevi.ParabolicEtaleConjugacyStatement
import Langlands.GroupScheme.RelativeLevi.PointedConjugatorReduction
import Langlands.GroupScheme.RelativeLevi.EqualFiberConjugacy
import Langlands.GroupScheme.InnerAutomorphismHom

/-! # Etale-local conjugacy of relative parabolic subgroup schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace Dynamic

variable {S : Scheme.{u}} {G P Q : GroupScheme S}

/-- Compose a fixed initial conjugator with an etale-local conjugator of the
resulting subgroup inclusion. -/
def EtaleSubgroupConjugacyData.preconjugate
    (i : P ⟶ G) (j : Q ⟶ G) (s : S)
    (g : Over.mk (𝟙 S) ⟶ G.X)
    (d : EtaleSubgroupConjugacyData (i ≫ (G.innerIso g).hom) j s) :
    EtaleSubgroupConjugacyData i j s := by
  refine ⟨d.neighbourhood, d.projection, d.etale, d.point, d.point_over,
    d.conjugator * baseChangeBasePoint d.projection G g, ?_⟩
  rw [innerIso_mul_hom, ← baseChange_innerIso_hom, ← Category.assoc,
    ← Functor.map_comp]
  exact d.conjugates

end Dynamic

/-- Relative parabolic subgroup schemes conjugate over the residue field at a
point are conjugate on an etale neighbourhood containing that point. -/
theorem relativeParabolicEtaleLocalConjugacyStatement :
    RelativeParabolicEtaleLocalConjugacyStatement.{u} := by
  intro S G P Q i j s hG hi hj hconj
  obtain ⟨g₀, hg₀⟩ := hconj
  let : Smooth G.X.hom := hG.smooth
  let d := pointedEtaleConjugator i j g₀ hg₀
  let GU := (baseChange d.projection).obj G
  let iU := (baseChange d.projection).map i
  let jU := (baseChange d.projection).map j
  let i' := iU ≫ (GU.innerIso d.point).hom
  have hGU : IsReductive GU := hG.baseChange d.projection
  have hi' : IsRelativeParabolicSubgroup i' :=
    (hi.baseChange hG d.projection).comp_iso (GU.innerIso d.point)
  have hjU : IsRelativeParabolicSubgroup jU := hj.baseChange hG d.projection
  let : Mono i'.hom.hom := hi'.mono
  let : Mono jU.hom.hom := hjU.mono
  let x := d.residuePoint (IsLocalRing.closedPoint (S.residueField s))
  have heq := SubgroupFunctor.range_eq_residue_of_fieldPoint
    i' jU d.residuePoint d.ranges_eq
  let c := relativeParabolicConjugacyOfEqualResidue i' jU hGU hi' hjU x heq
  let c' := Dynamic.EtaleSubgroupConjugacyData.preconjugate iU jU x d.point c
  let : Etale d.projection := d.etale
  let c'' := Dynamic.EtaleSubgroupConjugacyData.comp d.projection i j x c'
  have hx : d.projection x = s := by
    change (d.residuePoint ≫ d.projection) _ = s
    rw [d.residue_over, Scheme.fromSpecResidueField_apply]
  refine ⟨c''.neighbourhood, c''.projection, c''.etale,
    ⟨c''.point, c''.point_over.trans hx⟩, c''.conjugator, c''.conjugates⟩

end Langlands.GroupScheme
