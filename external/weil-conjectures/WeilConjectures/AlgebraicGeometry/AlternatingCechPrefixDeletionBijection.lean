/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSortingOperators
import WeilConjectures.AlgebraicGeometry.PrefixDeletionExistence
import WeilConjectures.AlgebraicGeometry.PrefixDeletionRestrictions

/-!
# The unsigned prefix-deletion correspondence

Source: Stacks Project, Tag 01FM, equation-first-homotopy (Tag 01FN), omitted
verification, prefix-deletion part.
(blueprint: lem-pc-alternating-cech-prefix-deletion-bijection)
-/

@[expose] public section

set_option autoImplicit false

universe v

namespace AlgebraicGeometry.Scheme

/-- Valid outgoing prefix-deletion indices, with the original order of summation.
Source: Stacks 01FM, equation-first-homotopy.
(blueprint: lem-pc-alternating-cech-prefix-deletion-bijection) -/
abbrev CechPrefixOutgoing {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) :=
  {x : Equiv.Perm (Fin (p + 2)) × Fin (p + 2) ×
      Equiv.Perm (Fin (p + 2)) × Fin (p + 3) //
    (cechStableSort t x.1 ∧ cechPartialSort x.1 x.2.2.1 x.2.1) ∧
      x.2.2.2.val < x.2.1.val}

/-- Valid incoming faces whose omitted label precedes the remaining junction.
Source: Stacks 01FM, equation-first-homotopy.
(blueprint: lem-pc-alternating-cech-prefix-deletion-bijection) -/
abbrev CechPrefixIncoming {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) :=
  {y : Fin (p + 2) × Equiv.Perm (Fin (p + 1)) × Fin (p + 1) ×
      Equiv.Perm (Fin (p + 1)) //
    (cechStableSort (t ∘ y.1.succAbove) y.2.1 ∧
      cechPartialSort y.2.1 y.2.2.2 y.2.2.1) ∧
    (t y.1 < t (y.1.succAbove (y.2.1 y.2.2.1)) ∨
      (t y.1 = t (y.1.succAbove (y.2.1 y.2.2.1)) ∧
        y.1 < y.1.succAbove (y.2.1 y.2.2.1)))}

/-- Prefix deletion is an unsigned bijection, identifying both smaller
permutations with restrictions of the larger ones.

Source: Stacks 01FM, equation-first-homotopy (01FN), omitted verification;
the prefix labelled-deletion argument of the parent node.

Proof: For an outgoing index (σ,a,τ,r), r<a implies r<p+2. Put j=σ(r)=τ(r).
Delete position r and label j from σ and τ, renumbering all remaining labels by
j.succAbove, and put b=a-1. Stable sorting is preserved because the increasing
renumbering preserves the tie-breaking order on labels. The restricted τ agrees
with the restricted σ before b and remains increasing from b onward, so it is the
partial sort with prefix b. Since r<a, the omitted pair (t(j),j) precedes the
remaining junction pair.
Conversely, for an incoming (j,σ',b,τ'), insert j at its rank r in the stable order
of the full label set. The before condition says r≤b, hence r<b+1. Insert j into
both smaller permutations at position r and set a=b+1. Their prefixes agree,
and increasing tails and stable sorting are preserved. Deletion and insertion
are inverse, since the stable rank is unique and increasing renumbering is
injective. This includes b=0 and b=p, and repeated t-values are resolved by the
original labels; for an empty I there is no input t.
No signs or sums occur in this correspondence.
(blueprint: lem-pc-alternating-cech-prefix-deletion-bijection) -/
theorem cechPrefixDeletionBijection {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) :
    ∃ e : CechPrefixOutgoing p t ≃ CechPrefixIncoming p t, ∀ x,
      let y := e x
      x.1.2.1.val = y.1.2.2.1.val + 1 ∧
      ∃ hr : x.1.2.2.2.val < p + 2,
        x.1.2.2.1 ⟨x.1.2.2.2.val, hr⟩ = y.1.1 ∧
        (∀ k : Fin (p + 1),
          x.1.1 ((⟨x.1.2.2.2.val, hr⟩ : Fin (p + 2)).succAbove k) =
            y.1.1.succAbove (y.1.2.1 k)) ∧
        (∀ k : Fin (p + 1),
          x.1.2.2.1 ((⟨x.1.2.2.2.val, hr⟩ : Fin (p + 2)).succAbove k) =
            y.1.1.succAbove (y.1.2.2.2 k)) := by
  obtain ⟨e, he⟩ := prefixDeletionExistence p t
  refine ⟨e, ?_⟩
  intro x
  let y := e x
  obtain ⟨ha, ⟨hr₀, hb⟩⟩ := he x
  obtain ⟨hr, hσ, hτ⟩ := prefixDeletionRestrictions p t e he x
  have hb' : x.1.2.2.1 ⟨x.1.2.2.2.val, hr⟩ = y.1.1 := by
    simpa using hb
  exact ⟨ha, hr, hb', hσ, hτ⟩

end AlgebraicGeometry.Scheme
