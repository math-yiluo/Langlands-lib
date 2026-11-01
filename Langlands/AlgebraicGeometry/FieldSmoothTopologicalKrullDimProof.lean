import Mathlib.AlgebraicGeometry.Properties
import Langlands.AlgebraicGeometry.FieldSmoothClosedPointStalkDimensionProof
import Langlands.AlgebraicGeometry.FieldSmoothTopologicalKrullDimStatement

/-!
# The dimension of a quasi-compact smooth scheme over a field is at most its relative dimension

On a quasi-compact scheme, every irreducible closed subset `T` contains a closed point `c`,
and the coheight of `T` in the poset of irreducible closed subsets is at most that of
`{c}`, which is the Krull dimension of the stalk at `c`. At a closed point of a scheme smooth of
relative dimension `g` over a field, that stalk has dimension `g` by the Library's
`fieldSmoothClosedPointStalkDimension`.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Order

namespace Langlands.AlgebraicGeometry

namespace FieldSmoothTopologicalKrullDim

/-- On a quasi-compact scheme whose stalks at closed points have dimension at most `g`, the
underlying space has dimension at most `g`. -/
theorem topologicalKrullDim_le_of_stalk (X : Scheme.{u}) [CompactSpace X] (g : ℕ)
    (h : ∀ x : X, IsClosed ({x} : Set X) → ringKrullDim (X.presheaf.stalk x) ≤ g) :
    topologicalKrullDim X ≤ g := by
  rw [topologicalKrullDim, krullDim_eq_iSup_coheight]
  refine iSup_le fun T => ?_
  obtain ⟨c, hcT, hc⟩ := T.isClosed.exists_closed_singleton T.isIrreducible.nonempty
  let C : IrreducibleCloseds X := ⟨{c}, isIrreducible_singleton, hc⟩
  have hCT : C ≤ T := Set.singleton_subset_iff.2 hcT
  have h1 : coheight T ≤ coheight C := coheight_anti hCT
  have h2 : coheight C = coheight c := by
    have hC : C = (irreducibleSetEquivPoints (α := X)).symm c :=
      IrreducibleCloseds.ext (by
        change ({c} : Set X) = closure {c}
        exact hc.closure_eq.symm)
    rw [hC]
    exact coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm c
  have h3 := h c hc
  rw [ringKrullDim_stalk_eq_coheight] at h3
  calc (coheight T : WithBot ℕ∞) ≤ coheight C := by exact_mod_cast h1
    _ = coheight c := by rw [h2]
    _ ≤ g := h3

end FieldSmoothTopologicalKrullDim

/-- A quasi-compact scheme smooth of relative dimension `g` over a field has topological Krull
dimension at most `g`. -/
theorem fieldSmoothTopologicalKrullDim : FieldSmoothTopologicalKrullDimStatement.{u} := by
  intro k _ X f g hf _
  exact FieldSmoothTopologicalKrullDim.topologicalKrullDim_le_of_stalk X g
    (fun x hx => (fieldSmoothClosedPointStalkDimension k X f g hf x hx).le)

end Langlands.AlgebraicGeometry
