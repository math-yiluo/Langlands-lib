/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Extensions of free modules are free

In a short exact sequence `0 → M → N → P → 0` of modules with `M` and `P` free, the module `N`
is free (`Module.Free.of_exact`): the sequence splits since `P` is projective.
-/

@[expose] public section

/-- In a short exact sequence `0 → M → N → P → 0` of modules over a ring with `M` and `P` free,
the module `N` is free, since the sequence splits. -/
theorem Module.Free.of_exact {R M N P : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] [Module.Free R M]
    [Module.Free R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P} (hfg : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) : Module.Free R N := by
  obtain ⟨l, hl⟩ := Module.projective_lifting_property g LinearMap.id hg
  obtain ⟨e, -, -⟩ := hfg.splitSurjectiveEquiv hf ⟨l, hl⟩
  exact Module.Free.of_equiv e.symm
