/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Proper morphisms descend along fpqc covering families

Source: Stacks Project, Descent, Tag 02L1, `lemma-descending-property-proper`
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Properness descends along an fpqc covering family.

Source: Stacks Project, Descent, Tag 02L1, `lemma-descending-property-proper`
(auxiliary; not a blueprint node).

Proof: properness is Zariski local on the target and stable under base change.
The source-library instance
`isProper_descendsAlong_surjective_inf_flat_inf_quasiCompact` supplies descent
along a single surjective flat quasi-compact morphism. Generate the fpqc covering
sieve from the given covering presieve and apply
`Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology` to the canonical pullback
squares and the proper second projections. This works for arbitrary index universes;
the generic descent theorem also handles the empty cover of the empty scheme.
-/
theorem isProper_of_fpqc_cover {X S : Scheme.{u}} (f : X ⟶ S) {I : Type v}
    (S' : I → Scheme.{u}) (g : ∀ i, S' i ⟶ S)
    (hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)
    (h : ∀ i, IsProper (pullback.snd f (g i))) : IsProper f := by
  exact Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology (P := @IsProper)
    (Precoverage.generate_mem_toGrothendieck hg) f
    (fun i ↦ pullback.fst f (g i)) (fun i ↦ pullback.snd f (g i))
    (fun i ↦ IsPullback.of_hasPullback f (g i)) h

end AlgebraicGeometry
