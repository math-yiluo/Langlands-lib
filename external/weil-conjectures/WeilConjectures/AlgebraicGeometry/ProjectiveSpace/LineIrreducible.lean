/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineGeometricallyIrreducible
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth

/-!
# The projective line over a field is geometrically irreducible

The base change of `ℙ¹_k` to a field `K` is `ℙ¹_K`, which is integral. Hence `ℙ¹_k` is
geometrically irreducible over `k`, and so is every nonempty open subscheme of it; in particular
the geometric fiber `W ⊗_k k̄` of a nonempty open `W ⊆ ℙ¹_k` is irreducible.

## Main statements

- `AlgebraicGeometry.ProjectiveLine.geometricallyIrreducible`: `ℙ¹_k` is geometrically
  irreducible over `k`.
- `AlgebraicGeometry.ProjectiveLine.irreducibleSpace_geometricFiber_opens`: the geometric fiber of
  a nonempty open subscheme of `ℙ¹_k` is irreducible.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProjectiveLine

variable (k : Type u) [Field k]

/-- A nonempty open subscheme of the projective line over a field is geometrically
irreducible. -/
theorem geometricallyIrreducible_opens (W : (ProjectiveLine (Spec (.of k))).Opens)
    (hW : (W : Set (ProjectiveLine (Spec (.of k)))).Nonempty) :
    GeometricallyIrreducible (W.ι ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) := by
  have : Surjective (W.ι ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) := by
    refine ⟨fun y ↦ ?_⟩
    obtain ⟨x, hx⟩ := hW
    refine ⟨⟨x, hx⟩, Subsingleton.elim (α := Spec (.of k)) _ _⟩
  infer_instance

/-- The geometric fiber of a nonempty open subscheme of the projective line over a field is
irreducible. -/
theorem irreducibleSpace_geometricFiber_opens (W : (ProjectiveLine (Spec (.of k))).Opens)
    (hW : (W : Set (ProjectiveLine (Spec (.of k)))).Nonempty) :
    IrreducibleSpace (W.ι ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).geometricFiber := by
  have := geometricallyIrreducible_opens k W hW
  have : UniversallyOpen (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) := by
    have := SmoothOfRelativeDimension.smooth 1 (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
    infer_instance
  have : UniversallyOpen (W.ι ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) := inferInstance
  have : IrreducibleSpace (Scheme.specAlgebraicClosure k).left :=
    inferInstanceAs (IrreducibleSpace (Spec (.of (AlgebraicClosure k))))
  exact inferInstanceAs (IrreducibleSpace ↥(pullback (C := Scheme.{u})
    (W.ι ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) (Scheme.specAlgebraicClosure k).hom))

end AlgebraicGeometry.ProjectiveLine
