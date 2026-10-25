# Refined induction and coarse real-character twists

`Langlands.refinedLeviRealTwist` proves the exact proposition
`Langlands.RefinedLeviRealTwistStatement` with independent field, fine-carrier
and quotient-carrier universes `uF`, `uV` and `uW`. It treats every ordered
block shape and refinement, including rank zero, arbitrary fine representations,
and arbitrary real parameter families. The proof uses the actual smooth induced
functions and actual intertwiners appearing in that proposition.

For a coarse shape `B`, refinement `S`, fine representation `ω`, fine parameter
`v₀` and coarse parameter `t`, write `I₀` and `Iₜ` for
`innerInduced T B S (fineTwist T B S ω v₀ 0)` and
`innerInduced T B S (fineTwist T B S ω v₀ t)`. The fine determinant exponent is
`-v₀(k) + t(parent(k))`; setting `t` to zero preserves the negative fine twist.

The theorem first identifies the restriction of the coarse determinant
character to the refined parabolic with the fine determinant character whose
parameter at `k` is `t(parent(k))`. It then constructs one representation
equivalence `E` from the coarse character twist of `I₀` to `Iₜ`. For every
induced function `f` and coarse Levi element `m`, evaluation of `E f` is
evaluation of `f` multiplied by the coarse character at `m`. Evaluation of
`E.symm f` uses the inverse character at that same element.

For every specified surjective intertwiner `q₀ : I₀ → π`, the theorem supplies
a surjective intertwiner `qₜ : Iₜ → twistₜ π` whose underlying function is
exactly `q₀ ∘ E.symm`. The choice of `E` precedes the quantifiers over `π`
and `q₀`; the same equivalence transports every such map.

The private determinant helper reindexes an actual parabolic matrix into
block coordinates, uses its block triangularity, and applies
`Matrix.BlockTriangular.det_fintype`. An explicit equivalence identifies each
diagonal submatrix with the corresponding Levi-projection matrix. This proves
equality in the units of the coefficient ring by the product of the actual
diagonal-block determinants.

Applying the normalized absolute-value and real-power monoid homomorphisms to
this determinant identity gives the real-character restriction on each coarse
block. `Fintype.prod_sigma` combines the nested block products, and
`BlockShape.flattenBlockEquiv` reindexes them by the flattened block set.
`flattenedLeviEquiv_symm_component` identifies the actual matrix coordinates.
The size-transport helper eliminates the corresponding `finCongr` reindexing
by equality elimination. This establishes the first conjunct without any
positive-rank assumption.

For the equivalence, the proof packages the coarse character as an
`Induction.SmoothCharacter`, using its published open-kernel theorem. Let
`σ₀` and `σₜ` be the inflated fine inducing actions at parameters zero and `t`,
each twisted by the same positive refined half-modulus. Action extensionality,
the character restriction just proved, and `leviRealPowerCharacter_add` show
that `σₜ` is the restriction of the coarse character times `σ₀`.
Commutativity of complex scalar multiplication moves this character past
the unchanged half-modulus.

The published `Induction.smoothInductionTwistEquiv` now gives character
multiplication on the actual smooth functions. The proof composes it with
`Induction.smoothInducedEquiv` applied to
`equivOfRepresentationEq` for the inducing-action identity. This latter
equivalence is the identity on the underlying inducing carrier, so both
evaluation formulas are definitional equalities. The generic construction
preserves the actual uniform open right stabilizers using the character's
open kernel and therefore needs no smoothness premise on the arbitrary fine
representation.

Finally, `twistIntertwining` twists the specified `q₀` without changing its
underlying linear map. Composing with `E.symm.toIntertwiningMap` produces `qₜ`.
Surjectivity is the composition of the given surjectivity of `q₀` with the
surjectivity of the inverse linear equivalence. The stated underlying-function
formula is again definitional.

This is a derived specialization of character compatibility with induction
in Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), Section 1.8(a), printed p.444, Proposition 1.9(f), printed p.445,
and the ordered GL Levi conventions of Section 2.2, printed p.446. The retained
source is registered as `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The explicit determinant coordinates, evaluation equations, arbitrary-input
and rank-zero scope, and specified-map formula are derived internal details.
The proof follows the construction above rather than assuming the source's
abstract compatibility result.

The implementation retains right translation, positive half-modulus covariance
and the residue-normalized `q^(-valuation)` absolute value of the imported
constructions. It proves character restriction and transport of a supplied
quotient. It supplies no support existence, reciprocity, multiplicity comparison,
supported recovery, arbitrary-tempered reflection or classification theorem.
