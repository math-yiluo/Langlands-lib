/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Standard.StandardChartFrames
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.SixFunctors.OverlapUnitNormalization
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.SixFunctors.TransitionDegreeSeparation
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineTwist

/-! # Classification of invertible modules on the projective line

The family `O` denotes any choice of twists with the standard generators and relation
`g₀ = t^{-d} g₁`, encoded by `ProjectiveLine.TwistData`. Uniqueness is asserted only
for the integer degree; the isomorphism of module sheaves is merely inhabited.

## References

* Stacks Project, Tag 0BXJ, specialized to dimension one
  over a field
* Stacks Project, Tag 0BXJ, for `n = 1` and `R = k`
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveLine

open ProjectiveSpace Scheme.Modules

private theorem nonempty_twistData_of_invertible (k : Type u) [Field k]
    (L : (ProjectiveLine (Spec (.of k))).Modules) [Scheme.Modules.IsInvertible L] :
    ∃ d : ℤ, Nonempty (TwistData (Spec (.of k)) d L) := by
  obtain ⟨g₀, h₀⟩ := exists_standardChart_frames k L ⟨0⟩
  obtain ⟨g₁, h₁⟩ := exists_standardChart_frames k L ⟨1⟩
  obtain ⟨v, hv⟩ := (h₁.map inf_le_right).exists_unit_smul_eq (h₀.map inf_le_left)
  obtain ⟨d, a, ha⟩ := exists_normalized_overlap_unit k v
  refine ⟨d, ⟨{ g₀ := a.val • g₀
                g₁ := g₁
                bijective_smul_g₀ := h₀.units_smul a
                bijective_smul_g₁ := h₁
                map_g₀ := ?_ }⟩⟩
  rw [map_smul, hv, smul_smul]
  exact congrArg (fun r ↦ r • L.presheaf.map (homOfLE inf_le_right).op g₁)
    (congrArg Units.val ha)

private theorem eq_degree_of_twistData (k : Type u) [Field k]
    {L M : (ProjectiveLine (Spec (.of k))).Modules} {d e : ℤ}
    (D : TwistData (Spec (.of k)) d L) (E : TwistData (Spec (.of k)) e M)
    (φ : L ≅ M) : d = e := by
  obtain ⟨a, ha⟩ :=
    (D.isFreeGenerator_gen 0).exists_unit_smul_eq ((E.isFreeGenerator_gen 0).app_hom φ.symm)
  obtain ⟨b, hb⟩ :=
    (D.isFreeGenerator_gen 1).exists_unit_smul_eq ((E.isFreeGenerator_gen 1).app_hom φ.symm)
  apply eq_degree_of_chart_units k d e a b
  apply Units.ext
  apply ((D.isFreeGenerator_gen 1).map inf_le_right).smul_left_injective
  simp only [TwistData.gen] at ha hb ⊢
  change (_ * _) • _ = (_ * _) • _
  rw [mul_smul, mul_smul, ← D.map_g₀]
  change (ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE inf_le_left).op a.val •
      L.presheaf.map (homOfLE inf_le_left).op D.g₀ =
    (transitionUnit (ULift.{u} (Fin 2)) (Spec (.of k)) e ⟨0⟩ ⟨1⟩).val •
      ((ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE inf_le_right).op b.val •
        L.presheaf.map (homOfLE inf_le_right).op D.g₁)
  rw [← map_smul, ← map_smul]
  change L.presheaf.map (homOfLE inf_le_left).op (a.val • D.g₀) =
    _ • L.presheaf.map (homOfLE inf_le_right).op (b.val • D.g₁)
  rw [← ha, ← hb, ← Hom.app_presheaf_map, ← Hom.app_presheaf_map,
    ← Hom.app_smul, ← E.map_g₀]

/-- Every invertible module on the projective line over a field is isomorphic to a
unique integer twist. The chosen twists `O d` have the standard transition convention
specified by `TwistData`; neither their generators nor the isomorphism is claimed unique. -/
theorem existsUnique_degree_of_isInvertible (k : Type u) [Field k]
    (O : ℤ → (ProjectiveLine (Spec (CommRingCat.of k))).Modules)
    (hO : ∀ d : ℤ, Nonempty (TwistData (Spec (CommRingCat.of k)) d (O d)))
    (L : (ProjectiveLine (Spec (CommRingCat.of k))).Modules)
    [Scheme.Modules.IsInvertible L] :
    ∃! d : ℤ, Nonempty (L ≅ O d) := by
  obtain ⟨d, ⟨D⟩⟩ := nonempty_twistData_of_invertible k L
  obtain ⟨E⟩ := hO d
  obtain ⟨φ, _⟩ := D.existsUnique_iso E
  refine ⟨d, ⟨φ⟩, ?_⟩
  rintro e ⟨ψ⟩
  obtain ⟨F⟩ := hO e
  exact (eq_degree_of_twistData k E F (φ.symm ≪≫ ψ)).symm

end AlgebraicGeometry.ProjectiveLine
