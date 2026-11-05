import Langlands.GroupScheme.Reductive.CentralTorusSurjectivityStatement
import Langlands.GroupScheme.Reductive.CentralTorusSemisimpleQuotientStatement
import Langlands.GroupScheme.Reductive.CentralTorusProductSection
import Langlands.GroupScheme.Derived.PerfectQuotientImage
import Langlands.GroupScheme.Derived.SemisimplePerfectStatement
import Langlands.GroupScheme.SmoothNormalQuotient
import Langlands.GroupScheme.AffineQuotientProof
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.Torus.CentralMaximalBaseChangeReduction

/-! # Reduction of central-torus surjectivity to a semisimple quotient and perfectness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option linter.defProp false in
/-- A closed central torus with semisimple quotients, together with perfectness of
semisimple groups, gives a closed central torus that multiplies with the derived subgroup
onto the whole group. -/
def reductiveCentralTorusSurjectivity_of_semisimpleQuotient
    (hS : ReductiveCentralTorusSemisimpleQuotientStatement.{u})
    (hP : SemisimplePerfectStatement.{u}) :
    ReductiveCentralTorusSurjectivityStatement.{u} := by
  intro k _ G D d hG hd
  obtain ⟨Z, j, hZaff, hZlft, hZtor, hjcl, hjc, hquot⟩ := hS k G hG
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : ConnectedSpace G.X.left := hG.connectedSpace
  let Q := SmoothNormalQuotient.ofClosedNormal j hjcl hZtor.smooth hjc.range_isNormal
  have : LocallyOfFiniteType Q.quotient.X.hom := Q.locallyOfFiniteType
  have : QuasiCompact Q.quotient.X.hom := Q.quasiCompact
  have : IsSeparated Q.quotient.X.hom := Q.separated
  have : Smooth Q.projection.hom.hom.left := Q.smooth_projection
  have : Surjective Q.projection.hom.hom.left := Q.surjective_projection
  have : QuasiCompact Q.projection.hom.hom.left := Q.quasiCompact_projection
  have : IsAffineHom Q.quotient.X.hom :=
    affineGroupSchemeQuotient k G Q.quotient Q.projection
  have hQ : IsSemisimple Q.quotient :=
    hquot Q.quotient Q.projection Q.isFppfQuotient inferInstance inferInstance
  have hA := hd.surjective_comp_of_derivedSubgroup_eq_top Q.projection (hP k Q.quotient hQ)
  exact ⟨Z, j, hZaff, hZlft, hZtor, hjcl, hjc,
    surjective_subgroupProductMap_of_isFppfQuotient j d Q.projection Q.isFppfQuotient hA.surj⟩

end Langlands.GroupScheme
