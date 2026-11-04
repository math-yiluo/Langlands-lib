import Langlands.GroupScheme.Rational.ParabolicRadicalTorusLeviStatement
import Langlands.GroupScheme.Rational.ParabolicGeometricSolvableRadicalExistsStatement
import Langlands.GroupScheme.Rational.ParabolicRadicalTorusCentralizerLeviStatement
import Langlands.GroupScheme.Rational.GeometricRadicalTorusIntersection
import Langlands.GroupScheme.Rational.LeviRadicalIntersectionCenter

/-! # Assembly of the adapted rational Levi from structural inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The six named structural propositions suffice for the unchanged adapted
rational Levi target; none is asserted by this reduction. -/
def ParabolicRadicalTorusLeviReductionStatement : Prop :=
  ParabolicGeometricSolvableRadicalExistsStatement.{u} →
  MaximalRankRadicalTorusIntersectionStatement.{u} →
  MaximalTorusBaseChangeStatement.{u} →
  BorelContainingSubgroupConnectedStatement.{u} →
  ParabolicRadicalTorusCentralizerLeviStatement.{u} →
  MaximalTorusCentralizerStatement.{u} →
  ParabolicRadicalTorusLeviStatement.{u}

/-- Construct the actual radical, intersection, centralizer Levi and canonical
largest-central-subtorus factor from the six explicit structural inputs. -/
theorem parabolicRadicalTorusLevi_of_structural_inputs :
    ParabolicRadicalTorusLeviReductionStatement.{u} := by
  intro hrad hintersection hbase hconnected hlevi hself k _ G hG P j hj T t ht f hfactor
  obtain ⟨R, r, hr⟩ := hrad k G hG P j hj
  obtain ⟨S, sT, sR, hsT, hsR, hcomp, hrange⟩ :=
    hj.exists_radicalTorusIntersection_of_structural_inputs
      hintersection hbase hconnected hG j t ht f hfactor r hr
  obtain ⟨L, l, hl, hcentralizer⟩ := hlevi k G hG P j hj R r hr S sR hsR
  have hSambient : sR ≫ r ≫ j = sT ≫ t := by
    rw [← Category.assoc, ← hcomp, Category.assoc, hfactor]
  rw [hSambient] at hcentralizer
  obtain ⟨sL, hsL, hlargest⟩ :=
    hl.radicalIntersectionCenter hj.isClosedSubgroup ht.2.1 hfactor
      hr.1 hsR.1 hsT hrange hcentralizer (hself k G hG T t ht)
  exact ⟨R, r, hr, S, sT, sR, hsT, hsR, hcomp, hrange,
    L, l, sL, hl, hcentralizer, hsL, hlargest⟩

end Langlands.GroupScheme
