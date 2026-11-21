# Conditional auxiliary determinant untwisting for Harris Proposition 4.8

`Langlands.Global.Harris.proposition48AuxiliaryParityUntwistReduction` proves
[`Proposition48AuxiliaryParityUntwistReductionStatement`](HarrisProposition48ParityReductionStatement.md)
with independent local field and presentation carrier universes `uF` and `uV`.
It assumes the three determinant-twist compatibilities in the statement. This
is an internal reduction for the auxiliary place in Harris's Proposition 4.8
([Harris 1998](https://arxiv.org/abs/math/9611226), pp. 201–203), not a proof
of those compatibilities or of Proposition 4.8 itself. The determinant twist
uses the convention of [Henniart 2000](https://doi.org/10.1007/s002229900033),
§2.2, p. 444.

Choose an actual irreducible cuspidal representative `T` of the supplied
corrected class `c` using `IsoClass.exists_representative`. Set
`S = T.heckeDeterminantTwist ν⁻¹`. The private comparison lemma takes the
inverse of the actual linear equivalence from `T` to this twist. To check
the inverse is the required forward determinant multiple, write an arbitrary
vector of the twisted space as the image of a vector of `T` under the
equivalence. At each adelic group element `g`, the evaluation formula for
the twist shows that multiplying this image by `ν(det g)` cancels the
factor `ν⁻¹(det g)`. These values are complex units, so the product is one.
Equality of the continuous functions proves the specified
`OperatorRealization.IsDeterminantMultiple` from `S` to `T`.

- **Weak induction.** Use `isWeakAutomorphicInductionOf_iff` to obtain a
  presentation of `T` whose spectral system is weakly induced from
  `Q.correctedCharacter ν`. Apply the weak induction premise to that
  presentation and `ν⁻¹`. The resulting inducing character is
  `(ξ · (ν ∘ N)) · (ν⁻¹ ∘ N)`, with `N` the same actual idele-class
  norm in both pullbacks. Evaluate at each idele class to cancel the two
  factors and get `ξ`. The twisted presentation witnesses the weak induction
  of `ξ` at `S`.
- **Conjugate self-duality.** The supplied normalization gives
  `ν.complexConj = ν⁻¹` by extensionality, so `HeckeCharacter.complexConj_inv`
  gives the conjugate-inverse equation for `ν⁻¹`. Use the class-to-realization
  equivalence for conjugate self-duality, apply the transfer to `T.realization`,
  and return to the class of `S`.
- **Auxiliary supercuspidality.** Use `hasSupercuspidalComponent_iff` to
  obtain a presentation of `T` with a supercuspidal component at `Q.Ps.v`.
  This presentation need not be the one used for weak induction. Its actual
  `ν⁻¹` twist has a supercuspidal component there by the third premise.

The four corrected solution properties hold at `T` because its class is
`c`; in particular, regular algebraicity is carried over for `T` only.
No primary-place transport or regular algebraicity of `S` is needed.
