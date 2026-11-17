import Langlands.GroupScheme.Absolute.TorusCentralizerNormalizerStatement
import Langlands.GroupScheme.Cartan.StructureProof
import Langlands.GroupScheme.Torus.ConnectedCentralizerNormalizer
import Langlands.GroupScheme.Torus.CentralizerConnected
import Langlands.GroupScheme.Torus.SplitReflection
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof

/-! # The identity component of a maximal-torus centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

/-- The identity component of a maximal-torus centralizer is smooth, nilpotent,
and the identity component of its normalizer. -/
theorem torusCentralizerNormalizer : TorusCentralizerNormalizerStatement.{u} := by
  intro k _ _ G _ _ _ T j hj C c hc hC hCZ hmax
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨D, d, hd, hrep⟩ := exists_isCartanSubgroup_of_isMaximalTorus hj
  have hD : ConnectedSpace D.X.left := hd.connectedSpace
  have hdC : SubgroupFunctor.range d ≤ SubgroupFunctor.range c :=
    hmax D d hd.1 hD (le_of_eq hrep.2)
  have heq : SubgroupFunctor.range c = torusCentralizer j := by
    apply le_antisymm hCZ
    rw [← hrep.2]
    exact hdC
  have hcCartan : IsCartanSubgroup c := ⟨hc, T, j, hj, heq⟩
  have hstructure := cartanStructure k G C c hcCartan
  refine ⟨hstructure.1, hstructure.2.2, ?_⟩
  intro H h hh hH hn
  have : IsClosedImmersion h.hom.hom.left := hh
  have : IsAffine H.X.left := isAffine_of_isAffineHom h.hom.hom.left
  let : ConnectedSpace H.X.left := hH
  have hT : IsSplitTorus T.toGrp :=
    IsTorus.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting hj.1
  have hjC : SubgroupFunctor.range j ≤ SubgroupFunctor.range c := by
    rw [heq]
    exact range_le_torusCentralizer j
  have hz := range_le_torusCentralizer_of_connected_normalizer_splitTorus
    j hT (SubgroupFunctor.range c) hjC hCZ h hn
  rw [heq]
  exact hz

end Langlands.GroupScheme
