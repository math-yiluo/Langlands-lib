import Langlands.Representation.Plancherel.RationalNormKernelRemarksStatements
import Langlands.Representation.CuspidalSupport.RationalNormKernelCentralFiniteIndex

/-! # Proof of Renard V.2.6: if the centre is compact, then `⁰G = G(F)` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

/-- Renard V.2.6, Proposition: if the centre of `G(F)` is compact, then `⁰G = G(F)`. -/
theorem rationalNormKernelCompactCenter : RationalNormKernelCompactCenterStatement.{u} := by
  intro F _ _ _ _ G hG hZ
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  have hle : Subgroup.center (GroupScheme.rationalPoints G) ≤ rationalCommonNormKernel G :=
    compactSubgroup_le_rationalCommonNormKernel G _ hZ
  have hfin : (rationalCommonNormKernel G).FiniteIndex := by
    have := CuspidalSupport.rationalCommonNormKernel_sup_center_finiteIndex F G hG
    rwa [sup_eq_left.mpr hle] at this
  rw [eq_top_iff]
  intro g _
  have hn : (rationalCommonNormKernel G).index ≠ 0 := hfin.index_ne_zero
  have hpow : g ^ (rationalCommonNormKernel G).index ∈ rationalCommonNormKernel G :=
    Subgroup.pow_index_mem _ g
  rw [mem_rationalCommonNormKernel_iff_valuation] at hpow ⊢
  intro χ
  have h := hpow χ
  rw [map_pow, toAdd_pow, AddMonoidHom.nsmul_apply, smul_eq_zero] at h
  exact h.resolve_left hn

end Langlands.Plancherel
