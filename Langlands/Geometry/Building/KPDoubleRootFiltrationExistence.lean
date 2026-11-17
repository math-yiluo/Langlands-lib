import Langlands.Geometry.Building.KPMoyPrasadDoubleRootStatement
import Langlands.Geometry.Building.KPRationalMoyPrasadFamily
import Langlands.Geometry.Building.KPUnramifiedMoyPrasadComparison
import Langlands.Geometry.Building.KPLocalMoyPrasadGroupPropertiesProof
import Langlands.Geometry.Building.KPUnramifiedComparisonFieldStatements
import Langlands.Geometry.Building.SpecialTorusExistenceProof
import Langlands.Geometry.Building.UnramifiedValuationDescentProof
import Langlands.Geometry.Building.KPUnramifiedComparisonRootFieldProof
import Langlands.Geometry.Building.KPUnramifiedComparisonLeviFieldProof
import Langlands.Geometry.Building.KPUnramifiedComparisonZeroFieldProof
import Langlands.Geometry.Building.KPUnramifiedComparisonOpenProof

/-!
# Existence of a double-root friendly filtration of `Z(F)` (Kaletha–Prasad §9.8)

This module proves `CentralizerFiltrationDoubleRootExistenceStatement`. For every
nonarchimedean local field `F`, every affine group scheme `G` over `F` and every parahoric
building datum `P` satisfying the apartment axioms, there is a filtration of `Z(F)` that
satisfies the filtration axioms, is open, and is double-root commutator friendly. The
filtration is the restriction to `Z(F)` of the Moy–Prasad groups `G(K)_{x,r}` over the
maximal unramified extension `K = F^ur` (Kaletha–Prasad §9.8). The proof only assembles
published results.
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- **Existence of a double-root friendly KP §9.8 filtration of `Z(F)`.** Every parahoric
building datum satisfying the apartment axioms has a centralizer filtration that satisfies the
filtration axioms, is open and is double-root commutator friendly.

The comparison with the building over `K = F^ur` comes from
`unramifiedComparisonExistence_of_fields`, whose six inputs are published proofs. The
glue `unramifiedRationalMoyPrasad_of_unramifiedComparison`, together with the proof of the
`K`-level Moy–Prasad properties, turns it into a rational Moy–Prasad family. The reduction
`exists_doubleRootFriendly_filtration_of_rationalMoyPrasadFamily` then gives the
filtration. -/
theorem centralizerFiltrationDoubleRootExistence :
    CentralizerFiltrationDoubleRootExistenceStatement.{u} := by
  have hC : UnramifiedComparisonExistenceStatement.{u} :=
    unramifiedComparisonExistence_of_fields specialTorusExistence unramifiedValuationDescent
      unramifiedComparisonRootField unramifiedComparisonLeviField
      unramifiedComparisonZeroField unramifiedComparisonOpenField
  have h3 : UnramifiedRationalMoyPrasadStatement.{u} :=
    unramifiedRationalMoyPrasad_of_unramifiedComparison
      MaximalUnramified.localMoyPrasadGroupProperties hC
  intro F _ _ _ _ G _ P hP
  obtain ⟨_B, _hZ, _e, hQ⟩ := h3 F G P hP
  exact P.exists_doubleRootFriendly_filtration_of_rationalMoyPrasadFamily hP hQ

end Langlands.Geometry.Building
