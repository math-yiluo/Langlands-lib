import Langlands.AbelianScheme.LieRankStatement
import Langlands.AlgebraicGeometry.SmoothDifferentialsFiniteLocalBasisRank
import Langlands.AlgebraicGeometry.PullbackFiniteLocalBasisRankProof
import Langlands.AlgebraicGeometry.ModuleDualFiniteLocalBasis

/-! # Local freeness and relative-dimension rank of abelian-scheme Lie modules -/

universe u

namespace Langlands.AbelianScheme

/-- The actual Lie module is finite locally free, with rank equal to each specified
geometric relative dimension. -/
theorem lieLocalFreenessRank
    {S : AlgebraicGeometry.Scheme.{u}} (A : AbelianScheme S) :
    LieLocalFreenessRankStatement A := by
  have hΩ := Langlands.Scheme.smoothDifferentialsFiniteLocalBasisRank A.X.left S A.X.hom
  have hCotangent := Langlands.Scheme.Modules.pullbackFiniteLocalBasisRank
    S A.X.left (Langlands.GroupScheme.identitySection A.toGrp)
    (Langlands.Scheme.relativeDifferentials A.X.hom)
  have hLie := Langlands.Scheme.Modules.dualFiniteLocalBasisRank
    S (Langlands.GroupScheme.cotangentAtIdentity A.toGrp)
  constructor
  · obtain ⟨q, hq, hfinite⟩ := hLie.1 (hCotangent.1 (hΩ.1 A.smooth))
    exact ⟨{ exists_isLocallyFreeData := ⟨q, hq⟩ },
      { exists_localGeneratorsData := ⟨q, hfinite⟩ }⟩
  · intro g hg
    exact hLie.2 g (hCotangent.2 g (hΩ.2 g hg))

end Langlands.AbelianScheme
