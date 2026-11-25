/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius

/-!
# Points and irreducibility of the geometric fiber

The geometric fiber `X = X₀ ×_k k̄` of a scheme `X₀` over a field `k` surjects onto `X₀`, being
the base change of the surjection `Spec k̄ ⟶ Spec k`; and it is irreducible when `X₀` is
geometrically irreducible and universally open over `k`, for instance smooth.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.geometricFiberProj_surjective`: every point of `X₀` lies under a
  point of the geometric fiber.
- `AlgebraicGeometry.Scheme.Hom.irreducibleSpace_geometricFiber`: the geometric fiber of a
  geometrically irreducible, universally open scheme is irreducible.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Every point of `X₀` lies under a point of the geometric fiber `X₀ ×_k k̄`: the projection is
the base change of `Spec k̄ ⟶ Spec k`, which is surjective. -/
lemma geometricFiberProj_surjective (x : X) : ∃ y, f.geometricFiberProj.base y = x := by
  obtain ⟨p, hp, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f)
    (g := (Scheme.specAlgebraicClosure k).hom) x (IsLocalRing.closedPoint (AlgebraicClosure k))
    (Subsingleton.elim _ _)
  exact ⟨p, hp⟩

/-- The geometric fiber of a geometrically irreducible, universally open `k`-scheme is
irreducible. -/
lemma irreducibleSpace_geometricFiber [GeometricallyIrreducible f] [UniversallyOpen f] :
    IrreducibleSpace f.geometricFiber := by
  have : IrreducibleSpace (Scheme.specAlgebraicClosure k).left :=
    inferInstanceAs (IrreducibleSpace (Spec (CommRingCat.of (AlgebraicClosure k))))
  exact GeometricallyIrreducible.irreducibleSpace
    (pullback.snd f (Scheme.specAlgebraicClosure k).hom)
    (pullback.snd f (Scheme.specAlgebraicClosure k).hom).isOpenMap

end AlgebraicGeometry.Scheme.Hom
