/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Irreducible

/-!
# The projective line over a field is geometrically irreducible

The projective line `ℙ¹_k` over a field is connected and has a rational point, hence it is
geometrically connected; being smooth, it is geometrically irreducible. Consequently every
nonempty open subscheme of `ℙ¹_k` is a smooth geometrically connected curve over `k`.

## Main statements

- `AlgebraicGeometry.ProjectiveLine.geometricallyIrreducible`: `ℙ¹_k ⟶ Spec k` is geometrically
  irreducible.
- `AlgebraicGeometry.ProjectiveLine.geometricallyIrreducible_of_isOpenImmersion` and
  `AlgebraicGeometry.ProjectiveLine.smoothOfRelativeDimension_one_of_isOpenImmersion`: a nonempty
  open subscheme of `ℙ¹_k` is geometrically irreducible and smooth of relative dimension one
  over `k`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveLine

variable (k : Type u) [Field k]

/-- The projective line over a field is geometrically irreducible: it is connected with a
rational point, hence geometrically connected, and smooth. -/
instance geometricallyIrreducible :
    GeometricallyIrreducible (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) := by
  have hs : Ideal.span (Set.range (fun _ : ULift.{u} (Fin 2) ↦
      (1 : Γ(Spec (.of k), ⊤)))) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨⟨0⟩, rfl⟩) isUnit_one
  have : GeometricallyConnected (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) :=
    GeometricallyConnected.of_connectedSpace_of_section _
      (ProjectiveSpace.homOfSections (𝟙 _) _ hs)
      (ProjectiveSpace.homOfSections_over (𝟙 _) _ hs)
  have := SmoothOfRelativeDimension.smooth 1 (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  exact GeometricallyIrreducible.of_smooth_of_geometricallyConnected _

variable {k} {C : Scheme.{u}} (c : C ⟶ ProjectiveLine (Spec (.of k))) [IsOpenImmersion c]

/-- A nonempty open subscheme of the projective line over a field is geometrically
irreducible. -/
theorem geometricallyIrreducible_of_isOpenImmersion [Nonempty C] :
    GeometricallyIrreducible (c ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) :=
  GeometricallyIrreducible.comp_of_isOpenImmersion c _

/-- An open subscheme of the projective line over a field is smooth of relative dimension one. -/
theorem smoothOfRelativeDimension_one_of_isOpenImmersion :
    SmoothOfRelativeDimension 1 (c ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) := by
  rw [show 1 = 0 + 1 from rfl]
  infer_instance

end AlgebraicGeometry.ProjectiveLine
