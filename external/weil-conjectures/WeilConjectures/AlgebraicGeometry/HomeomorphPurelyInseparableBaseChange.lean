/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra

/-!
# Base change along a purely inseparable field extension

Source: blueprint `sec-picard-framework/sk-thm-picard-rr/lem-pc-homeo-pure-insep.md`
(blueprint: lem-pc-homeo-pure-insep); Stacks Project, Tags 0BR5 and 04DF.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Base change of a `k`-scheme along a purely inseparable field extension `K/k` induces
 a homeomorphism on the underlying topological spaces.
Source: Stacks Project, Tags 0BR5 and 04DF (blueprint: lem-pc-homeo-pure-insep).

Proof:
1. The map `π : Spec K ⟶ Spec k` induced by `algebraMap k K`
   (def-weil-affine-spectrum) is integral, universally injective and surjective because
   `K/k` is purely inseparable (lem-pc-spec-pure-insep-integral-radicial-surjective).
2. Such a morphism is a universal homeomorphism by Stacks, Tag 04DF
   (lem-pc-integral-radicial-surjective-universal-homeomorphism). Thus every base change
   of `π` is a homeomorphism on underlying spaces (def-weil-universal-homeomorphism).
3. Apply this to the structure morphism `X ↘ Spec k` (def-weil-scheme-over-base).
   By def-pc-base-change and def-pc-fibre-product, `X_K` is the pullback of this
   structure morphism and `π`, and its canonical map to `X` is `pullback.fst`.
   This is the projection in step 2, using symmetry of the two pullback factors. -/
theorem isHomeomorph_baseChange_of_isPurelyInseparable
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsPurelyInseparable k K]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] :
    IsHomeomorph
      (pullback.fst (X ↘ Spec (CommRingCat.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base := by
  exact (pullback.fst (X ↘ Spec (CommRingCat.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))).isHomeomorph

end AlgebraicGeometry
