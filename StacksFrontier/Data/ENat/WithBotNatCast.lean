module

public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Monoid
public import Mathlib.Order.WithBot

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Casts of natural numbers in `WithBot ℕ∞`

Mathlib's `ENat.natCast_ne_top` is the statement one level down, in `ℕ∞`; this file gives the
`WithBot ℕ∞` form.

## Main results

* `natCast_ne_top_withBot`
* `eq_natCast_unbotD_toNat`
-/

@[expose] public section

/-- A natural number, cast into `WithBot ℕ∞`, is not `⊤`. -/
theorem natCast_ne_top_withBot (n : ℕ) : ((n : ℕ) : WithBot ℕ∞) ≠ ⊤ := fun hn ↦
  ENat.natCast_ne_top n (WithBot.coe_injective
    (hn : ((n : ℕ∞) : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞)))

end
