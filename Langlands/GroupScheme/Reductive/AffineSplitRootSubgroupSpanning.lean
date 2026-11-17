import Langlands.GroupScheme.Reductive.AffineSplitRootSubgroupSpanningStatement
import Langlands.GroupScheme.Reductive.AffineSplitPositiveBorel
import Langlands.GroupScheme.Reductive.AffineSplitClosedRootSubgroup
import Langlands.GroupScheme.Reductive.LocalSplitFlatBigCell

/-! # Subgroups directly spanned by root groups over an affine base -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open LocalSplitCell

/-- **Subgroups directly spanned by root groups over an affine base** (Conrad, *Reductive
group schemes* (2014), Theorem 5.1.13, Proposition 5.1.14 and Proposition 5.1.16(1)): the open
big cell, the closed subgroup `T ⋉ U_{Φ⁺}`, the closed subgroups `U_Ψ` directly spanned by the
root groups of a closed set `Ψ` with `Ψ ∩ -Ψ = ∅`, and the commutator relations. -/
theorem affineSplitRootSubgroupSpanning : AffineSplitRootSubgroupSpanningStatement.{u} := by
  intro R _ G _ hG I _ i hi hmax J P hP u hv
  refine ⟨fun b m n neg pos => ?_, fun b n pos => ?_, fun Ψ hcl hopp => ?_,
    fun a c hca hcna n e => ?_⟩
  · exact LocalSplitBigCell.isOpenImmersion_cellMap hG hmax hP b u hv neg pos
  · exact exists_closedSubgroup_torus_positive hG hi hmax hP hv b n pos
  · exact exists_closedRootSubgroup hG hmax hP hv Ψ hcl hopp
  · exact exists_commutator_orderedProduct hG hmax hP hv a c hca hcna n e

end Langlands.GroupScheme
