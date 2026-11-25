/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Group schemes over a field are separated

Let `G` be a group scheme over a field `k`. The unit section
`e : Spec k ⟶ G` is a closed immersion, being a section of `G ⟶ Spec k` (Mathlib's
`AlgebraicGeometry.isClosedImmersion_of_comp_eq_id`). The shear automorphism
`(g, h) ↦ (g, g⁻¹ h)` of `G ×_k G` carries the diagonal of `G` to the base change
`G ⟶ G ×_k G`, `g ↦ (g, e)`, of `e`, so the diagonal is a closed immersion and `G` is separated
over `k` (Stacks 047L).

## Main statements

- `AlgebraicGeometry.GrpObj.isSeparated_hom`: a group scheme over a field is separated.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- **Group schemes over a field are separated.** A group scheme `G` over a field `k` is
separated over `k`: the shear automorphism `(g, h) ↦ (g, g⁻¹ h)` of `G ×_k G`
carries the diagonal to the base change of the unit section, which is a closed immersion. -/
@[stacks 047L]
instance GrpObj.isSeparated_hom (G : Over (Spec (.of k))) [GrpObj G] : IsSeparated G.hom := by
  have he : IsClosedImmersion η[G].left :=
    isClosedImmersion_of_comp_eq_id G.hom _ (Over.w η[G])
  have hdiag : lift (𝟙 G) (𝟙 G) =
      ((ρ_ G).inv ≫ G ◁ η[G]) ≫ (CategoryTheory.GrpObj.shearIso G).hom := by
    ext <;> simp [MonObj.comp_mul, ← Hom.one_def]
  have hw : IsClosedImmersion (G ◁ η[G]).left := by
    rw [Over.whiskerLeft_left]
    exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
      (MorphismProperty.id_mem _ _) he (by simp) (by simp)
  refine ⟨?_⟩
  have : Limits.pullback.diagonal G.hom = (lift (𝟙 G) (𝟙 G)).left := by
    ext <;> simp
  rw [this, hdiag, Over.comp_left, Over.comp_left]
  infer_instance

end AlgebraicGeometry
