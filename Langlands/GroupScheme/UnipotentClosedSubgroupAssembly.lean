import Langlands.GroupScheme.UnipotentClosedSubgroupStatement
import Langlands.GroupScheme.CoalgebraUnipotence.Statements
import Langlands.GroupScheme.UnipotentMatrixCriterion.Statement
import Langlands.GroupScheme.AffineCorepresented
import Langlands.GroupScheme.CorepresentedComultiplication
import Langlands.GroupScheme.Chevalley.CoordinateRestriction
import Langlands.GroupScheme.Rational.SplitUnipotentTransport

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open CoalgebraUnipotence

/-- Assemble the closed-subgroup theorem from the three matrix/coalgebra criteria. -/
theorem unipotentClosedSubgroup_of_matrixCriteria
    (hbridge : UnipotentMatrixCriterion.CorepresentedMatrixUnipotenceStatement.{u})
    (hcriterion : MatrixUnipotenceConilpotenceStatement.{u, u})
    (hquotient : ConilpotenceQuotientStatement.{u, u, u}) :
    UnipotentClosedSubgroupStatement.{u} := by
  intro k _ H _ _ W w hw hH
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let : IsClosedImmersion w.hom.hom.left := hw
  let : IsAffine W.X.left := isAffine_of_isAffineHom w.hom.hom.left
  let eH := AffineCoordinates.groupSchemeIso H
  let eW := AffineCoordinates.groupSchemeIso W
  let φ := eW.hom ≫ w ≫ eH.inv
  have : IsIso eW.hom.hom.hom.left :=
    inferInstanceAs (IsIso (((Grp.forget _) ⋙ Over.forget _).mapIso eW).hom)
  have : IsIso eH.inv.hom.hom.left :=
    inferInstanceAs (IsIso (((Grp.forget _) ⋙ Over.forget _).mapIso eH).inv)
  have hc : IsClosedSubgroup φ := by
    change IsClosedImmersion
      (eW.hom.hom.hom.left ≫ w.hom.hom.left ≫ eH.inv.hom.hom.left)
    infer_instance
  let cH := AffineCoordinates.corepresentation H
  let cW := AffineCoordinates.corepresentation W
  let α := Corepresented.pointsTrans cW cH φ
  have hc' : IsClosedSubgroup (Corepresented.groupSchemeMap cW cH α) := by
    simpa only [α, Corepresented.groupSchemeMap_pointsTrans] using hc
  let := AffineLinearEmbedding.bialgebra cH
  let := AffineLinearEmbedding.bialgebra cW
  have hmH : IsMatrixUnipotent k (AffineCoordinates.algebra H) :=
    (hbridge k _ _ cH).mp (IsUnipotent.of_iso eH hH)
  have hnH : IsLocallyConilpotent k (AffineCoordinates.algebra H) :=
    (hcriterion k (AffineCoordinates.algebra H)).mp hmH
  let q := Chevalley.coordinateRestrictionBialgHom cH cW α
  have hq : Function.Surjective q :=
    Chevalley.coordinateRestriction_surjective cH cW α hc'
  have hnW : IsLocallyConilpotent k (AffineCoordinates.algebra W) :=
    hquotient k (AffineCoordinates.algebra H) (AffineCoordinates.algebra W) q hq hnH
  have hmW : IsMatrixUnipotent k (AffineCoordinates.algebra W) :=
    (hcriterion k (AffineCoordinates.algebra W)).mpr hnW
  have huW : IsUnipotent (Corepresented.groupScheme (AffineCoordinates.functor W) cW) :=
    (hbridge k _ _ cW).mpr hmW
  exact IsUnipotent.of_iso eW.symm huW

end Langlands.GroupScheme
