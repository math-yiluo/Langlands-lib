# Noetherianity of adic completions: statement

Module: `Langlands.CommutativeAlgebra.AdicCompletionNoetherianStatement`.

Author: Worker 5181, for Task 5570, requested by Workers 100 and 116 on
Task 5157.

The proposition `Langlands.CommutativeAlgebra.AdicCompletionNoetherianStatement.{u}`
is stated here, not proved. It asserts that, for every commutative ring
`R : Type u` with `IsNoetherianRing R` and every ideal `I : Ideal R`, the ring
`AdicCompletion I R` is Noetherian, i.e. `IsNoetherianRing (AdicCompletion I R)`
holds.

The universe `u` is an arbitrary universe parameter of the definition. There is
no hypothesis on `R` besides commutativity and Noetherianity, and none on `I`.
In particular there is no locality, domain, reducedness, finite-type,
properness or maximality assumption. The zero ideal and the unit ideal are
included. For the unit ideal the completion is the zero ring.

## The completion

`AdicCompletion I R` is Mathlib's actual adic completion of `R`, viewed as a
module over itself, from `Mathlib.RingTheory.AdicCompletion.Basic`. Its elements
are the families `f n ∈ R ⧸ (I ^ n • ⊤)`, indexed by `n : ℕ`, that are compatible
under the canonical maps `R ⧸ (I ^ n • ⊤) → R ⧸ (I ^ m • ⊤)` for `m ≤ n`. For
the module `R` itself, the submodule `I ^ n • ⊤` is the ideal `I ^ n`, so this is
the inverse limit `lim R/I^n`. The ring structure is the `CommRing` instance
of `Mathlib.RingTheory.AdicCompletion.Algebra`, which multiplies families
componentwise as a subring of `∀ n, R ⧸ (I ^ n • ⊤)`. This module imports only that file
and `Mathlib.RingTheory.Noetherian.Basic`, for `IsNoetherianRing`.

## Source correspondence

The source is the Stacks Project, registered as
`stacks-noetherian-completion-2026-11-11` (HTML snapshots retrieved
11 November 2026). In `0316.html`, Algebra, Section 10.97, Lemma 10.97.6
(Tag 0316) reads: "Let R be a Noetherian ring. Let I be an ideal of R. The
completion R^∧ of R with respect to I is Noetherian."

- In the Stacks Project, "ring" means commutative ring with identity; this is
  the binder `[CommRing R] [IsNoetherianRing R]`.
- "Let I be an ideal of R" is the arbitrary `I : Ideal R`.
- The completion of `R` with respect to `I` is Stacks' `R^∧ = lim R/I^n`
  (the convention `M^∧ = lim M/I^nM` is used throughout Section 10.97, e.g. in
  the proof of Lemma 10.97.1 in `0BNH.html`), which is `AdicCompletion I R` as
  described above.
- "is Noetherian" is `IsNoetherianRing (AdicCompletion I R)`.

The section snapshot `0BNH.html` retains the full Section 10.97 and its five
comments; they concern other lemmas of the section and do not change this
statement. `05GH.html`, Lemma 10.97.5, is a stronger criterion (finitely
generated `I` with Noetherian `R/I`) and is not formalized here.

## Proof status

This module does not prove the proposition and assumes nothing. A proof is a
separate successor. The current Library already contains the theorem
`AdicCompletion.isNoetherianRing_of_isNoetherianRing` in module
`Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing`,
whose type for `{R : Type u}` and `(I : Ideal R)` is the body of this
proposition. It is not imported here.
