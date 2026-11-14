import Langlands.Global.AdelicRankOneGaloisOrbitHeight
import Langlands.Global.AdelicGaloisOverlapMatching
import Langlands.Global.AdelicSplitFundamentalSetFromCover
import Langlands.Global.AdelicSplitSiegelOverlapProof
import Langlands.Global.AdelicGaloisOverlapMatchingProof
import Langlands.Global.AdelicGaloisTwistSubgroupProof

/-! # The rank-one parabolic rational-orbit height bound

See the paired Markdown file for the statement, provenance and proof. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGaloisUnit AdelicSiegelFactors

/-- Springer's §3.6 assembly: the split fundamental-set theorem, the split overlap
estimate, the twisted overlap matching over a Galois splitting field and the Galois
twisting of a split Borel pair give the rank-one rational-orbit height bound. -/
theorem rankOneParabolicRationalOrbitHeightBound_of_springerInputs
    (hF : SplitAdelicFundamentalSetStatement.{u}) (hO : SplitSiegelOverlapStatement.{u})
    (hM : SplitGaloisOverlapMatchingStatement.{u}) (hT : GaloisBorelTwistingStatement.{u}) :
    RankOneParabolicRationalOrbitHeightBoundStatement.{u} := by
  intro F _ _ G _ _ hG TF iF hiF νF hνF αF hαF n ρ j hstab
  let _ : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨D, ν, hν, htw⟩ := hT F G hG
  let _ : NumberField D.carrier := NumberField.of_module_finite F D.carrier
  exact hasUniformNormOneRationalOrbitHeightBound_of_twistedOverlapMatching F D.carrier G hG
    iF hiF νF hνF αF hαF ρ j hstab D.torus D.inclusion (D.isConnectedReductive hG)
    (D.isMaximalTorus.isMaximalSplitTorus D.isSplitTorus) ν hν D.isMaximalTorus
    (hM hF hO F G hG D ν hν htw)

/-- The same assembly with the two split inputs discharged by their published proofs:
Springer's split fundamental-set theorem and the split overlap estimate. -/
theorem rankOneParabolicRationalOrbitHeightBound_of_galoisInputs
    (hM : SplitGaloisOverlapMatchingStatement.{u}) (hT : GaloisBorelTwistingStatement.{u}) :
    RankOneParabolicRationalOrbitHeightBoundStatement.{u} :=
  rankOneParabolicRationalOrbitHeightBound_of_springerInputs splitAdelicFundamentalSet
    splitSiegelOverlap hM hT

/-- **The rank-one parabolic rational-orbit height bound** (Springer 1994, §3.6): for a
connected reductive group of semisimple `F`-rank one over a number field and a matrix
representation with a coordinate line whose exact stabilizer is the minimal standard
parabolic, the orbit height of that line is uniformly bounded on `G(𝔸_F)¹` after a rational
right translate. The two Galois inputs are discharged by their published proofs: Springer's
§3.5 overlap matching and the §3.4 Galois twisting of a split Borel pair. -/
theorem rankOneParabolicRationalOrbitHeightBound :
    RankOneParabolicRationalOrbitHeightBoundStatement.{u} :=
  rankOneParabolicRationalOrbitHeightBound_of_galoisInputs splitGaloisOverlapMatching
    (galoisBorelTwisting_of galoisTwistNormOne galoisTwistSubgroup)

end Langlands.Global.RepresentationGrowth
