/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.BaseChangeDimension

/-!
# A uniform bound on the dimensions of the fibres of a finite-type morphism

Let `b : Y ⟶ S` be a morphism of schemes over a field `k` with `Y` quasi-compact and locally of
finite type over `k`. Then the dimensions of the fibres `Y ×_S Spec Ω` of `b` over all points
`Spec Ω ⟶ S` with values in fields are bounded: the fibre embeds into `Y ×_k Spec Ω` (the map
`pullback.mapDesc` is an immersion), whose dimension is bounded independently of `Ω` by
`AlgebraicGeometry.exists_topologicalKrullDim_le_of_isPullback`.

## Main statements

- `AlgebraicGeometry.exists_topologicalKrullDim_pullback_le`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Uniformly bounded fibre dimension.** For morphisms `b : Y ⟶ S` and `aS : S ⟶ Spec k`,
`k` a field, with `b ≫ aS` quasi-compact and locally of finite type, there is `d` such that
every fibre `Y ×_S Spec Ω` of `b` over a point `s : Spec Ω ⟶ S`, `Ω` a field, has dimension at
most `d`. -/
lemma exists_topologicalKrullDim_pullback_le {k : Type u} [Field k] {Y S : Scheme.{u}}
    (aS : S ⟶ Spec (.of k)) (b : Y ⟶ S) [LocallyOfFiniteType (b ≫ aS)] [QuasiCompact (b ≫ aS)] :
    ∃ d : ℕ, ∀ (Ω : Type u) [Field Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback b s : Scheme.{u}) ≤ (d : WithBot ℕ∞) := by
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_le_of_isPullback (b ≫ aS)
  refine ⟨n, fun Ω _ s ↦ ?_⟩
  exact (pullback.mapDesc b s aS).isEmbedding.isInducing.topologicalKrullDim_le.trans
    (hn Ω (s ≫ aS) _ _ (IsPullback.of_hasPullback (b ≫ aS) (s ≫ aS)))

end AlgebraicGeometry
