/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

/-!
# Weakly étale universal homeomorphisms

We show that a morphism between weakly étale `S`-schemes is weakly étale, and that a weakly
étale universal homeomorphism is an isomorphism. The latter is the key input showing that the
absolute Frobenius acts trivially on the small pro-étale site.

## Main statements

- `AlgebraicGeometry.WeaklyEtale.of_comp_eq`: an `S`-morphism between weakly étale `S`-schemes
  is weakly étale.
- `AlgebraicGeometry.WeaklyEtale.isIso_of_isUniversalHomeomorphism`: a weakly étale universal
  homeomorphism is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeaklyEtale

variable {U V S : Scheme.{u}}

/-- Morphisms between weakly etale objects.
Let `u: U ⟶ S` and `v: V ⟶ S` be weakly étale. Every `S`-morphism `f: U ⟶ V` is weakly
étale: its composite with the weakly étale `v` is the weakly étale `u` (Stacks 0951,
`AlgebraicGeometry.WeaklyEtale.of_comp`). -/
theorem of_comp_eq (u : U ⟶ S) (v : V ⟶ S) [WeaklyEtale u] [WeaklyEtale v] (f : U ⟶ V)
    (h : f ≫ v = u) : WeaklyEtale f := by
  subst h
  exact of_comp f v

/-- The diagonal of a weakly étale universally injective quasi-separated morphism is an
isomorphism: it is a flat surjective quasi-compact monomorphism. -/
theorem isIso_diagonal_of_universallyInjective (f : V ⟶ S) [WeaklyEtale f]
    [UniversallyInjective f] [QuasiSeparated f] : IsIso (pullback.diagonal f) := by
  have : Surjective (pullback.diagonal f) :=
    ((tfae_universallyInjective f).out 1 4).1 ‹UniversallyInjective f›
  exact Flat.isIso_of_surjective_of_mono _

/-- A weakly etale universal
homeomorphism is an isomorphism. Let `f: V ⟶ W` be weakly étale and a universal homeomorphism. Then
`f` is an isomorphism: its diagonal is a flat surjective closed immersion, hence an isomorphism, so
`f` is a flat surjective quasi-compact monomorphism, hence an isomorphism. -/
theorem isIso_of_isUniversalHomeomorphism (f : V ⟶ S) [WeaklyEtale f]
    [IsUniversalHomeomorphism f] : IsIso f := by
  have := isIso_diagonal_of_universallyInjective f
  have : Mono f := (pullback.isIso_diagonal_iff f).1 inferInstance
  exact Flat.isIso_of_surjective_of_mono f

end AlgebraicGeometry.WeaklyEtale
