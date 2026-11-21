# Central simple representatives of prescribed local degree and invariant

Let `K` be a nonarchimedean local field, let `n` be positive, and let
`x : denominatorSubgroup n` be a class in `ℚ/ℤ` annihilated by `n`.
`Langlands.ClassFieldTheory.Local.csaOfInvariant K hn x` is a central simple
`K`-algebra of dimension `n * n` with local Brauer invariant `x`.
The algebra and the field share a universe, as required by the current
Brauer quotient. Its opposite has local invariant `-x`.

The construction uses the inverse of the published `localBrauerInvariant`
to take a Brauer class and chooses an algebra in that class. A
Wedderburn–Artin presentation gives a central division algebra in the
same class. The published `addOrderOf_localDivisionClass` identifies
its reduced degree `d` with the additive order of the class. Since `n`
annihilates `x`, injectivity of the invariant makes `d` divide `n`.
Positive-size matrices of size `n / d` over the division algebra give the
stated dimension and preserve its class. The operation on the opposite
uses `classOf_opposite` and additivity of the invariant.

This is an internal construction from the Library's matrix-stable Brauer
group, local invariant, and local division degree theorem. At a finite
CM completion, the published local-field structure allows the construction
to be applied with `x = denominatorEquiv n hn a` for a residue `a : ZMod n`.
This gives the degree and signed invariants needed for the two factors of
a split-place unitary pair.
