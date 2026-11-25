/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Higher right derived functors of exact functors

Source: Stacks Project, Derived Categories, Lemma 13.16.9, Tag 015F, part (5)
(blueprint: lem-sc-exact-functor-higher-derived-vanishing).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- An exact additive functor between abelian categories with enough injectives has zero
higher right derived functors: `R^{q+1} v (M) = 0` for every `q : ℕ`, i.e. `R^q v (M) = 0`
for every integer `q > 0`, in the natural-number indexing of `Functor.rightDerived`.

Source: Stacks Project, Derived Categories, Lemma 13.16.9, Tag 015F, part (5)
(blueprint: lem-sc-exact-functor-higher-derived-vanishing).

Proof: Exactness implies left exactness and additivity, so choose an injective resolution
`M → I` as in [def-sp-left-exact-additive] and [def-sp-injective-resolutions]. Its cohomology
vanishes in every positive degree. The exact-functor cohomology comparison
[lem-weil-pbc-exact-functor-complex-cohomology] identifies `H^q(v(I))` with `v(H^q(I))`.
This is zero, since `H^q(I)` is zero and an additive functor preserves zero objects.
Finally, [def-sp-left-exact-additive] identifies `R^q v(M)` with `H^q(v(I))`, giving the
claimed vanishing. -/
theorem isZero_rightDerived_obj_of_exact
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] [EnoughInjectives A] [EnoughInjectives B]
    (v : A ⥤ B) [v.Additive] [PreservesFiniteLimits v] [PreservesFiniteColimits v]
    (M : A) (q : ℕ) : IsZero ((v.rightDerived (q + 1)).obj M) := by
  let I : InjectiveResolution M := Classical.choice (HasInjectiveResolution.out (Z := M))
  refine IsZero.of_iso ?_ (I.isoRightDerivedObj v (q + 1))
  exact (v.map_isZero (I.cocomplex_exactAt_succ q).isZero_homology).of_iso
    ((I.cocomplex.sc (q + 1)).mapHomologyIso v)

end CategoryTheory.Functor
