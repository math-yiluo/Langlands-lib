/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Projective morphisms

The canonical projectivity definitions and properness API are kept before direct-image
cohomology, so Chow constructions used in the latter can import them without a cycle.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section Projective

variable {X S : Scheme.{u}}

/-- A morphism `f: X ⟶ S` is *H-projective* (or *relatively projective*) if it factors as a
closed immersion `i: X ⟶ ℙ(n; S)` into a projective space over `S`, for some finite type of
homogeneous coordinates `n`, followed by the structure morphism of `ℙ(n; S)`.
-/
class IsHProjective (f : X ⟶ S) : Prop where
  exists_isClosedImmersion :
    ∃ (n : Type u) (_ : Finite n) (i : X ⟶ ℙ(n; S)), IsClosedImmersion i ∧ i ≫ ℙ(n; S) ↘ S = f

/-- A morphism `f: X ⟶ S` is *projective* if it is H-projective and quasi-compact. A scheme over
a field `k` is projective over `k` if its structure morphism is projective.
-/
class IsProjective (f : X ⟶ S) : Prop extends IsHProjective f, QuasiCompact f

/-- **H-projective morphisms are proper**, being the composite of a closed immersion and the
proper structure morphism of a projective space. -/
instance (priority := 100) IsHProjective.isProper (f : X ⟶ S) [IsHProjective f] :
    IsProper f := by
  obtain ⟨n, _, i, _, rfl⟩ := IsHProjective.exists_isClosedImmersion (f := f)
  infer_instance

/-- An H-projective morphism is projective, being proper and hence quasi-compact.

This is not an instance, since together with the parent projection
`AlgebraicGeometry.IsProjective.toIsHProjective` it would form an instance cycle. -/
theorem IsHProjective.isProjective (f : X ⟶ S) [IsHProjective f] : IsProjective f where

end Projective

end AlgebraicGeometry
