import Langlands.GroupScheme.Reductive.CenterMultiplicativeTypeStatement
import Langlands.GroupScheme.Reductive.NormalCenterCentralizerReduction
import Langlands.GroupScheme.Torus.MultiplicativeTypeSubgroups

/-! # Full-center multiplicative type from maximal-torus self-centralization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Algebraically closed maximal-torus self-centralization implies the full
reductive-center multiplicative-type proposition over every field. -/
def CenterMultiplicativeTypeCentralizerReductionStatement : Prop :=
  AlgClosedMaximalTorusCentralizerStatement.{u} → CenterMultiplicativeTypeStatement.{u}

/-- Embed the full center in a split torus after algebraic closure, then use
the actual diagonalizable closed-subgroup presentation as splitting data. -/
theorem centerMultiplicativeTypeCentralizerReduction :
    CenterMultiplicativeTypeCentralizerReductionStatement.{u} := by
  intro hCentralizer k _ G Z z hG hz
  let K := AlgebraicClosure k
  let b := toAlgebraicClosure k
  let GK := (GroupScheme.baseChange b).obj G
  let ZK := (GroupScheme.baseChange b).obj Z
  let zK := (GroupScheme.baseChange b).map z
  have hGK : IsConnectedReductive GK := hG.baseChange_toAlgebraicClosure
  have hzK : IsSchemeTheoreticCenter zK :=
    schemeTheoreticCenterBaseChangeStatement k K G Z z hG hz
  obtain ⟨T, t, hT, ht, hc⟩ :=
    exists_splitTorus_containing_center_of_algClosedMaximalTorusCentralizer
      hCentralizer GK hGK
  let : IsClosedImmersion t.hom.hom.left := ht
  let : Mono t.hom.hom := Over.mono_of_mono_left _
  have htrep : (SubgroupFunctor.range t).IsRepresentedBy t := ⟨inferInstance, rfl⟩
  let j := htrep.factorHom zK (hzK.2 ▸ hc)
  have hj : IsClosedSubgroup j := IsClosedSubgroup.of_comp ht (by
    rw [SubgroupFunctor.IsRepresentedBy.factorHom_comp]
    exact hzK.1)
  obtain ⟨Λ, hΛ, hfg, ⟨e⟩⟩ :=
    exists_diagonalizableIso_of_isClosedSubgroup_splitTorus hT j hj
  exact ⟨K, inferInstance, inferInstance, Λ, hΛ, hfg, ⟨e⟩⟩

end Langlands.GroupScheme
