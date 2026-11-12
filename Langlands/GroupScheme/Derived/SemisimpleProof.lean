import Langlands.GroupScheme.Derived.SemisimpleStatement
import Langlands.GroupScheme.Derived.SemisimpleReduction
import Langlands.GroupScheme.Derived.MaximalTorusIntersectionReduction
import Langlands.GroupScheme.Derived.CentralIntersectionProof
import Langlands.GroupScheme.Reductive.CentralDerivedProductProof

/-! # Proof: actual derived subgroups of connected reductive groups are semisimple -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every actual inclusion exhibiting the scheme-theoretic derived subgroup of a connected
reductive field group has a semisimple source. -/
theorem derivedSubgroupSemisimple : DerivedSubgroupSemisimpleStatement.{u} := by
  intro k _ G D d hG hd
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨Z, E, i, e, -, -, -, -, hi, he, hepi⟩ := reductiveCentralDerivedProduct k G hG
  obtain ⟨C, c, hcc, hc, hfin⟩ := derivedCentralIntersectionFiniteness k G E e hG he
  exact ⟨hd.isConnectedReductive hG,
    hd.hasFiniteCenter_of_centralProduct i e hi he C c hcc hc hfin⟩

end Langlands.GroupScheme
