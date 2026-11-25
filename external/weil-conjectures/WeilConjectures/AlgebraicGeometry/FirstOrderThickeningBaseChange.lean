/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Thickening
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Base change of a first order thickening

Source: Stacks Project, More on Morphisms, Lemma 37.2.4 (Tag 09ZU), and
Schemes, Lemma 26.17.6 (Tag 01JU), part (1)
(blueprint: lem-weil-pbc-first-order-thickening-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Base change of a first order thickening is a first order thickening, with ideal
`i.ker.comap p`, the extended ideal of def-nagata-extended-ideal. The two projections
commute with `p` and `i`, giving a morphism of thickenings (Stacks Project, Tags 09ZU,
01JU (1), and 04EX (5)).

Proof:
1. The closed immersion component of the hypothesis gives a local instance.
   Closed immersions are stable under base change, so the first projection is
   a closed immersion.
2. Mathlib's `Scheme.IdealSheafData.ker_fst_of_isClosedImmersion` identifies its
   kernel with `i.ker.comap p`.
3. The proved source-library `Scheme.IdealSheafData.comap_pow` identifies the
   square of this extended ideal with `(i.ker ^ 2).comap p`. The hypothesis
   makes this `⊥.comap p`, which is `⊥` by `Scheme.IdealSheafData.comap_bot`.
4. The closed immersion and square-zero kernel give the first order thickening.
   The defining pullback equation supplies the required commuting square.

(blueprint: lem-weil-pbc-first-order-thickening-base-change). -/
theorem IsFirstOrderThickening.baseChange {W W' Z' : Scheme.{u}}
    (i : W ⟶ W') (p : Z' ⟶ W') (hi : IsFirstOrderThickening i) :
    IsFirstOrderThickening (pullback.fst p i) ∧
      (pullback.fst p i).ker = i.ker.comap p ∧
      (i.ker.comap p) ^ 2 = ⊥ ∧
      pullback.fst p i ≫ p = pullback.snd p i ≫ i := by
  let : IsClosedImmersion i := hi.1
  have hker := Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i p
  have hsq : (i.ker.comap p) ^ 2 = ⊥ := by
    rw [← Scheme.IdealSheafData.comap_pow, hi.2, Scheme.IdealSheafData.comap_bot]
  exact ⟨⟨inferInstance, by rw [hker]; exact hsq⟩, hker, hsq, pullback.condition⟩

end AlgebraicGeometry
