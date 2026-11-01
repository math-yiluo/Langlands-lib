# Character twists and the actual Aubert operator

This is a derived internal construction from the published exact smooth
Grothendieck-group twist, actual normalized parabolic character-twist
equivalences, alternating operator, and determinant-one lemma for block
unipotent radicals in `Classification/SupercuspidalTwist`. It
transcribes no additional original-literature assertion.

For every prime `p`, every supplied `F : PadicField p` and
`T : F.TopologicalData`, `characterTwistK0` is the existing exact
finite-length smooth Grothendieck-group twist specialized to the actual
`GL_n(F)`. `leviCharacterTwistK0` uses the literal restriction of the same
smooth character along the actual block-diagonal Levi embedding. Both retain
the saturated carrier universe `max uF uV`, with independent field and
representation universes. Characters have complex unit values and open kernel.

`normalizedJacquetK0_characterTwist` and
`normalizedInductionK0_characterTwist` are equalities of integer-linear maps
on the existing exact quotients. They assume that the ambient character is
trivial on the actual upper block unipotent radical. The proof compares the
maps on every genuine finite-length smooth object, uses the published
finite-length preservation and generator formulas, and identifies the output
classes through the published actual representation equivalences. For Jacquet
this is the quotient map preserving the class of each vector; for induction
it multiplies a function at `x` by the ambient character at `x`. The full
positive modulus and positive induction half-modulus are unchanged, with
inverse half-modulus on Jacquet and right translation on inducing functions.
The quotient imposes all actual short exact relations, including nonsplit
ones; no finite-dimensional replacement or splitting is used.

`alternatingOperator_characterTwist` assumes this radical condition for every
ordered block shape of the given rank. Its proof expands the actual
unadjusted alternating operator with coefficients
`(-1 : ℤ) ^ (n - B.length)`, distributes the integer-linear twist across the
finite sum and scalar multiplication, and applies the two preceding map
identities to each summand. It is an equality on all virtual classes and
includes rank zero.

The imported `BlockShape.determinant_eq_one_of_mem_unipotentSubgroup` proves
that every actual upper block radical element has determinant one. Its
published proof in `Classification/SupercuspidalTwist` reindexes the matrix
by block coordinates and applies Mathlib's block-triangular determinant
formula to its identity diagonal blocks. The lemma works over any
commutative ring, in every rank; this module reuses it.

`determinantSmoothCharacter` pulls any open-kernel complex unit character of
`Fˣ` back along the actual continuous determinant of `GL_n(F)`. Continuity
gives the open kernel. `determinantSmoothCharacter_radical` uses the preceding
determinant-one lemma to prove radical triviality for every block shape.
Consequently `alternatingOperator_determinantTwist` proves unconditional
commutation for every such determinant character, on the full exact
finite-length smooth Grothendieck group, in every rank.

The construction assumes no admissibility, irreducibility, cuspidality,
positivity, or theorem of classification. It does not prove the analytic
segment classification, an identification of segment heads under Aubert
duality, or either analytic square-integrability implication.
