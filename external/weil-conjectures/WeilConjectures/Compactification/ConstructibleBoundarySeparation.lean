/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.BoundaryPreparation
public import WeilConjectures.Topology.ConstructibleIsRetrocompact

/-!

# Separation of constructible closed subsets by an admissible blow-up

Two disjoint constructible closed subsets of a quasi-compact open `U` of a qcqs scheme `X`
acquire disjoint closures after a `U`-admissible blow-up of `X` (Stacks Project Tag 0F3V).

## Implementation details

This is `AlgebraicGeometry.exists_admissibleBlowup_disjoint_closures`, which asks instead
that the complements of the closed subsets be quasi-compact: a constructible subset of the
quasi-compact space `U` is retrocompact, so the complement of a constructible closed subset
is quasi-compact.

-/

@[expose] public section

universe u

open Topology

namespace AlgebraicGeometry

variable {X : Scheme.{u}} {U : X.Opens}

/-- **Separation of closures** (Stacks Project Tag 0F3V): if `X` is qcqs, `U ⊆ X` is a
quasi-compact open and `T₁, T₂ ⊆ U` are disjoint constructible closed subsets, then there is a
`U`-admissible blow-up `b : X' ⟶ X` such that the closures of `b⁻¹(T₁)` and `b⁻¹(T₂)` in `X'`
are disjoint. -/
theorem exists_admissibleBlowup_disjoint_closures_of_isConstructible
    [CompactSpace X] [QuasiSeparatedSpace X] (hU : IsCompact (U : Set X))
    {T₁ T₂ : Set U.toScheme} (hT₁ : IsClosed T₁) (hT₂ : IsClosed T₂)
    (hc₁ : IsConstructible T₁) (hc₂ : IsConstructible T₂) (hdisj : Disjoint T₁ T₂) :
    ∃ B : IsAdmissible X U,
      Disjoint (closure (B.I.blowupMap ⁻¹' (U.ι '' T₁)))
        (closure (B.I.blowupMap ⁻¹' (U.ι '' T₂))) := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  exact exists_admissibleBlowup_disjoint_closures hU hT₁ hT₂
    (isConstructible_compl.mpr hc₁).isRetrocompact.isCompact
    (isConstructible_compl.mpr hc₂).isRetrocompact.isCompact hdisj

end AlgebraicGeometry
