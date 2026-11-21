import Langlands.GroupScheme.HomScheme.AffineFiberArtinian
import Langlands.GroupScheme.HomScheme.AffineFiberTorusAdicLimitsProof
import Langlands.GroupScheme.HomScheme.AffineFiberTorusCentralizerOverTests
import Langlands.GroupScheme.HomScheme.AffineFiberTorusModuliAssembly
import Langlands.GroupScheme.HomScheme.TorusCentralizerJetRepresentability

/-! # Smooth torus-subgroup representability with affine residue fibres -/

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

open SubgroupFunctor

theorem smoothAffineFiberTorusSubgroupRepresentability :
    SmoothAffineFiberTorusSubgroupRepresentabilityStatement.{u} := by
  apply smoothAffineFiberTorusSubgroupRepresentability_of_moduliInputs
  intro A _ _ G _ _ _ _ hG
  let S := Spec (CommRingCat.of A)
  have hA := isAffineHom_artinianPullback_of_residueFibers S G hG
  refine ⟨hA, affineFiberTorusAdicLimits G hG, ?_⟩
  obtain ⟨M, H, c, hM, hc, hH, hconn, hF, hRep⟩ :=
    noetherianAffineFibrewiseTorusCentralizersRepresentable (CommRingCat.of A) G hG
  have hU (U : Over S) (F : SubgroupFunctor ((baseChange U.hom).obj G)) (hF' : IsAdmissible F) :
      ∃! a : U ⟶ M, evaluate c a = F.centralizer := by
    obtain ⟨T, t, ht, hT, hrep⟩ := hF'
    obtain ⟨K, j, hj, hK, hconnK, hFK, hEq⟩ :=
      affineFiberTorusCentralizerOverTests A G hG U T t ht hT
    simpa only [hEq, hrep.2] using hRep U K j hj hK hconnK hFK
  exact ⟨⟨M, H, c, hc, smooth_of_torusCentralizerParameter S G hA M H c hc hF hU,
    hH, hconn, hU⟩⟩

end Langlands.GroupScheme.TorusSubgroupModuli
