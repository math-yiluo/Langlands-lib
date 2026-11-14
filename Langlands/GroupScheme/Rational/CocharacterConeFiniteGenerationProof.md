# Finite generation via subtractive natural evaluation vectors

Authors: Worker 1222 and Worker 687. The Lean proof is reused unchanged from
Worker 1222's shared draft; Worker 687 checked and prepared the proof pair.

The theorem `Langlands.GroupScheme.cocharacterConeFiniteGeneration.{u}` proves
the published
`Langlands.GroupScheme.CocharacterConeFiniteGenerationStatement.{u}`. For every
field `k : Type u`, actual commutative group scheme `T` over `Spec k`, and finite
set `R` of actual characters, the additive submonoid
`CocharacterCone.quotient T R` is finitely generated. Here finite generation
means generation by finitely many elements under addition and natural-number
multiples. The proof imports the published statement unchanged.

Evaluate each actual cocharacter on the selected characters, obtaining a
linear map `e` to `R → ℤ`. Its kernel is exactly the existing common integral
annihilator `RealTorusSpace.rootAnnihilatorInt T R`. Evaluation therefore
descends to an injective linear map `qeval` from the annihilator quotient to
`R → ℤ`.

Let `c : (R → ℕ) →+ (R → ℤ)` cast coordinates to integers, and let `P` be the
submonoid of natural-valued functions whose casts lie in the range of `e`.
This submonoid is subtractive: if the casts of `x` and `x + y` lie in that
range, their difference, the cast of `y`, does too. Mathlib's
`AddSubmonoid.fg_of_subtractive` proves `P` finitely generated, using the
well quasi order on the finite product of natural numbers. The explicit
`Mathlib.Order.WellQuasiOrder` import supplies the relevant order instances.

The proof then identifies `P.map c` with the `qeval` image of
`CocharacterCone.quotient T R`. A nonnegative cocharacter gives natural
coordinates by `Int.toNat`; nonnegativity ensures their casts recover its
integer pairings. Conversely, a natural evaluation vector in the range of
`e` has a cocharacter preimage nonnegative on every selected character.
Finite generation passes to `P.map c` and is reflected through the injective
map `qeval`.

This is an internal proof of the derived finite-generation replacement
described in the published statement's Markdown, motivated by Renard 2026
V.3.24. It uses the existing actual lattices, pairing and quotient and the
general Mathlib theorem, rather than the source's general freeness assertion.
The sole finiteness premise is `R.Finite`; the argument also covers the empty
character set. No finite generation of the full cocharacter lattice, torus,
splitness, finite type, positive rank or characteristic hypothesis is used.
No free-monoid description, specified generator count, actual rational-point
quotient comparison or strict-face comparison is proved here.
