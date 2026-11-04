import Langlands.Representation.Aubert.General.DynamicUnipotentHaarDeterminantStatement
import Langlands.Representation.Aubert.General.DynamicUnipotentVectorFiltrationProof
import Langlands.Analysis.Local.VectorFiltrationHaarModulusProof
import Langlands.BruhatTits.Unipotent.CompactOpenContainmentProof

/-! # Haar scaling on a rational dynamic unipotent subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

/-- The Haar modulus of actual forward conjugation is the absolute value of the
actual Lie determinant, with the complete scope of the published statement. -/
theorem dynamicUnipotentHaarDeterminant : DynamicUnipotentHaarDeterminantStatement.{u} := by
  intro k _ _ _ _ G hG _ _ _ χ Z U iZ iU hZ hU _ _ d c hUc m hm
  have : IsAffineHom G.X.hom := hG.isAffineHom
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  obtain ⟨N, F, n, q, L, hF0, hFN, hFle, hFg, hqmul, hqker, hqc, hqo, hqs, hqL, hdet⟩ :=
    dynamicUnipotentVectorFiltration k G hG χ hZ hU c m
  have hcover : ∀ x : (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)),
      ∃ K : OpenSubgroup ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _))),
        IsCompact (K : Set ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))) ∧ x ∈ K := by
    intro x
    obtain ⟨K, hK, hxK⟩ := BruhatTits.dynamicUnipotentCompactOpenContainment k G hG χ
      {x} (isCompact_singleton)
    exact ⟨K, hK, hxK (Set.mem_singleton x)⟩
  rw [Langlands.HaarModulus.VectorFiltration.vectorFiltrationHaarModulus k
    _ hUc hcover ⟨m ≫ iZ.hom.hom, hm⟩ N F hF0 hFN hFle hFg
    n q hqmul hqker hqc hqo hqs L hqL]
  rw [← map_prod, hdet]

end Langlands.Aubert.General.RationalPointFamily
