/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StageCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.EtaleCohomologyStageContinuity

/-! # Continuity applied to certified stage comparisons

Source: Stacks Project, Tag 09YQ, and colimit universal properties.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Stage continuity makes every certified comparison bijective.

Source: Stacks Project, Tag 09YQ, universal property of its comparison.
(blueprint: lem-weil-pbc-stage-cohomology-comparison-bijective).

Proof: For the system constructor apply continuity at its specified stage.
The colimit universal property identifies the comparison with an isomorphism.
Isomorphisms are bijective; composition and products preserve bijectivity.
No Mayer--Vietoris exactness or middle comparison is used here. -/
theorem StageCohomologyComparison.bijective
    {allowed : Scheme.{u} → Prop}
    (hC : ∀ S, allowed S → EtaleCohomologyStageContinuity S)
    {A B : AddCommGrpCat.{u + 1}} {v : A ⟶ B}
    (hv : StageCohomologyComparison allowed v) : Function.Bijective v := by
  induction hv with
  | iso e =>
      exact (ConcreteCategory.isIso_iff_bijective e.hom).1 inferInstance
  | comp hf hg ihf ihg =>
      exact ihg.comp ihf
  | prod hf hg ihf ihg =>
      exact ihf.prodMap ihg
  | system D c hc F φ hid hcomp G eG hG L hL p H eH hH B eB hB S hS i₀ e =>
      have hcol := (hC S hS).holds D c hc F φ hid hcomp G eG hG L hL p
        H eH hH B eB hB i₀ ⟨e⟩
      have : IsIso (colimit.desc H B) :=
        ((colimit.isColimit H).nonempty_isColimit_iff_isIso_desc).1 hcol
      exact (ConcreteCategory.isIso_iff_bijective (colimit.desc H B)).1 inferInstance

end AlgebraicGeometry.Etale
