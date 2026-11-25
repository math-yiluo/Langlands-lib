# Duality and factor invariance for real standard modules

Module: `Langlands.Global.RankinSelberg.RealStandardPairingPremises` (namespace
`Langlands.Global.RankinSelbergGlobal`).

This module states two local statements about the real standard modules of `GL_n(ℝ)`: D
(duality) and U (factor invariance). **Neither is proved in this module**; both are `Prop`-valued
definitions, so that separate proofs can name them. The Library proves D as
`realStandardDualPairing` (module `RealStandardDualPairingProof`) and U as
`realStandardIntertwinerPairL` (module `RealStandardIntertwinerPairLProof`). Together,
D and U imply the local pairing premise of the real-place contragredient pair-factor statement
(see "Use" below). The module imports only Library modules.

## Notation

`I(ds) = realStandardKFinite n ds` (an abbreviation in `Langlands.Automorphic`) is the space of
`O(n)`-finite vectors of the Library's real standard module `realStandardModule n ds` of the
list `ds : List RealBlock`. A `RealBlock` is a real character block (`.character`, rank `1`) or
the real induction of a complex character (`.induced`, rank `2`); `realRank ds` is the sum of
the ranks. `realStandardRep n ds` is right translation by
`O(n) = Matrix.unitaryGroup (Fin n) ℝ`, and `realStandardLie n ds` is the right-derivative
action of `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`. These form the Library's `(𝔤, K)`-module structure
(`Langlands.Representation.Archimedean.RealStandardModuleGKModule`). `IsIrreducibleGKModule` is
the Library's irreducibility: the space is nonzero and the only subspaces stable under both
actions are `⊥` and `⊤`.

`RealLocalJacquet.dualBlock` (module `Langlands.Global.RankinSelberg.RealLocalWhittakerModel`)
replaces the inducing character of each block by its inverse. A character block `χ` becomes
`χ⁻¹`, with the same parity and the exponent negated. An induced block with complex character
data of weight `m` and exponent `t` becomes the one with weight `-m` and exponent `-t`.

`IsRealStandardIntertwiner n ρ π es T` (module
`Langlands.Representation.Archimedean.RealGenericParameterReduction`) says that the linear map
`T` out of `I(es)` carries right translation by each `k ∈ O(n)` to `ρ k` and the right
derivative along each real matrix `X` to `π (1 ⊗ X)`. `realPairLFactor xs ys` (module
`Langlands.LocalFactor.ArchimedeanPairFactor`) is the pair `L`-factor of two lists of real
blocks, the `L`-factor `realLFactor` of the list `realPairBlocks xs ys` of tensor products of
blocks. It is a `ReciprocalEntire`, whose field `denominator` is the entire function `1/L(s)`.

## Statements

### `RealStandardDualPairingStatement` (D, duality; entry declaration)

For every `n` and every list `ds` of real blocks with `realRank ds = n` whose module `I(ds)` is
irreducible, there is a `ℂ`-bilinear form `Q : I(ds) → I(ds.map dualBlock) → ℂ` with

- `Q (realStandardRep n ds k f) (realStandardRep n (ds.map dualBlock) k h) = Q f h` for every
  `k ∈ O(n)`;
- `Q (realStandardLie n ds (1 ⊗ X) f) h + Q f (realStandardLie n (ds.map dualBlock) (1 ⊗ X) h) = 0`
  for every real matrix `X`;
- for every nonzero `h ∈ I(ds.map dualBlock)` some `f ∈ I(ds)` with `Q f h ≠ 0`.

Only the real directions `1 ⊗ X` are required; since both Lie actions are `ℂ`-linear, they give
`Q (realStandardLie n ds Y f) h + Q f (realStandardLie n (ds.map dualBlock) Y h) = 0` for every
`Y ∈ ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`.

The first two clauses are written out in the same form and order as the predicate
`IsRealStandardInvariantPairing n ds (ds.map dualBlock) Q` of the module
`Langlands.Global.RankinSelberg.RealPlaceContragredientPremises`, so they are definitionally that
predicate. The clauses are written out here, and this module does not import
`RealPlaceContragredientPremises`.

Only the second module is required to be separated by `Q`. With `I(ds)` irreducible, the left
kernel `{f | ∀ h, Q f h = 0}` of a nonzero invariant form is automatically zero (it is stable
under both actions, by the two invariance clauses, and is not all of `I(ds)`), but nothing in
the hypotheses forces the right kernel to be zero, so the third clause is a real requirement.
The irreducibility hypothesis makes D weaker than the general duality theorem, which holds
without it.

### `RealStandardIntertwinerPairLStatement` (U, factor invariance)

For every `n` and all lists `es`, `es'` of real blocks with `realRank es = n` and
`realRank es' = n` whose modules `I(es)` and `I(es')` are irreducible, every nonzero linear map
`T : I(es) → I(es')` with
`IsRealStandardIntertwiner n (realStandardRep n es') (realStandardLie n es') es T`, and every
list `xs` of real blocks:

- `(realPairLFactor es xs).denominator = (realPairLFactor es' xs).denominator`, and
- `(realPairLFactor xs es).denominator = (realPairLFactor xs es').denominator`.

The conclusion is equality of pair `L`-factors against every partner, in both slots, not a
permutation of blocks. A permutation statement would be false, because real block lists are not
unique (see the consistency checks).

## Why D and U hold (standard theory, not proved here)

D. In Knapp 1986, Chapter VII, §1, pp. 167–169, the induced representation
`U(S, σ, ν) = ind_{MAN}^G(σ ⊗ exp ν ⊗ 1)` is normalized by `ρ`: its functions satisfy
`F(xman) = e^{-(ν+ρ) log a} σ(m)^{-1} F(x)`, with squared norm `‖F‖² = ∫_K |F(k)|² dk` (7.2)
and compact picture (7.3a). If `F` is in the space of `σ ⊗ exp ν` and `F'` in that of the contragredient
`σ^c ⊗ exp(-ν)`, the function `x ↦ ⟨F(x), F'(x)⟩` transforms on the right under `MAN` by
`e^{-2ρ log a}`, and the integral formula (7.4) of §2, item (2), p. 170, shows that
`∫_K ⟨F(k), F'(k)⟩ dk` is invariant under simultaneous translation by `G`. This pairing
identifies the `K`-finite contragredient of the induced representation from `σ ⊗ exp ν` with the
induced representation from its contragredient; Knapp does not state this identification as a
numbered result on these pages, so this step is our derivation from (7.4). Knapp states
Chapter VII for linear connected reductive groups; Knapp 1994, p. 400, (2.4), uses "unitary
induction as in [14, Chapter VII]" (reference [14] is Knapp 1986) for `GL_n(ℝ)` itself. The
double induction formula (7.5), pp. 170–171, gives induction in stages. The contragredient of
the building block of Knapp 1994, (2.2), p. 400, with a given character is the building block
with the inverse character, which in the Library is `dualBlock`. So the `K`-finite dual of
`I(ds)` is isomorphic to `I(ds.map dualBlock)`, and transporting the evaluation pairing gives
`Q`.

For induced blocks the plain integral over `O(n)` of the product of the two functions is not
invariant. The Library places the block of weight `m` and exponent `t` at two positions with
characters `sgn^(|m|+1) |·|^(t+|m|/2)` and `|·|^(t-|m|/2)` (`realInducedFirstCharacter`,
`realInducedSecondCharacter`). For the dual block, of weight `-m` and exponent `-t`, they are
`sgn^(|m|+1) |·|^(-t+|m|/2)` and `|·|^(-t-|m|/2)`. The product of the first characters is
`|·|^|m|`, which is not `1` unless `m = 0`. A proof of D for induced blocks has to compose the
pairing with an intertwining operator or build it through induction in stages.

U. By Knapp 1994, Theorem 1(c), p. 400, irreducible Langlands quotients are equivalent only if
their lists of building blocks agree up to order, and by (3.4) and Theorem 2, p. 403, equivalent
ones correspond to the same semisimple representation of the Weil group `W_ℝ`. Reordering the
blocks does not change the composition factors of the induced representation, so an irreducible
`I(es)` is isomorphic to the Langlands quotient attached to the blocks of `es` (after replacing
an induced block of weight `0`, which is not a building block, by its two character blocks; see
the consistency checks). A nonzero intertwiner between irreducible modules is an isomorphism, so
the two lists have isomorphic Weil-group representations. `realPairLFactor` multiplies the
`L`-factors of the tensor products of the blocks, with the block factors of Knapp 1994, (3.6),
p. 404. With the Library's normalization `Γ_ℂ(s) = 2(2π)^{-s}Γ(s)` (Mathlib's
`Complex.Gammaℂ`) one has `Γ_ℝ(s)Γ_ℝ(s+1) = Γ_ℂ(s)`, so the pair `L`-factor depends only on the
isomorphism classes of the two Weil-group representations. This gives both equalities.

## Consistency checks

- **Ranks.** `RealLocalJacquet.realRank_map_dualBlock` gives
  `realRank (ds.map dualBlock) = realRank ds`, so both modules of D are spaces of functions on
  the same `GL_n(ℝ)`.
- **Character blocks.** For `ds = cs.map RealBlock.character`, the list `ds.map dualBlock` is
  `(cs.map RealCharacterData.inverse).map RealBlock.character`, whose position characters are
  pointwise inverse to those of `ds`. The Library's `RealPrincipalSeriesDualityStatement`
  (module `Langlands.Representation.Archimedean.RealPrincipalSeriesQuotientReduction`, proved
  as `realPrincipalSeriesDuality` in
  `Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof`) gives for such lists,
  without irreducibility, a pairing
  with the three properties of D, stated through right translations and right derivatives of
  the underlying functions rather than through `realStandardRep` and `realStandardLie`. So D
  agrees with the Library in the principal-series case; its content lies in induced blocks.
- **Non-uniqueness of block lists.** An induced block of weight `0` and exponent `t` has
  position characters `sgn |·|^t` and `|·|^t` and no Fourier condition, so it gives the same
  module as the two character blocks `sgn |·|^t` and `|·|^t`, and the same factor
  `Γ_ℂ(s+t) = Γ_ℝ(s+t+1) Γ_ℝ(s+t)`. Induced blocks of weights `m` and `-m` with the same exponent
  give the same subspace of functions (the position characters and the Fourier condition use
  only `|m|`). When that module is irreducible (for instance for `n = 2` and `m ≠ 0`), the
  identity map of functions is a nonzero intertwiner between the modules of two lists that are
  not permutations of each other, so a permutation conclusion would fail. U requires equal pair
  factors here, and the Library's formulas give them: against any block, the tensor products
  (`RealBlock.tensor`, with `ComplexCharacterData.mul`, `conj` and `twistReal`) of the two
  blocks have, up to order, the same exponents and the same `|weight|` for their induced
  blocks, and the factor of an induced block depends only on its exponent and `|weight|`.
- **U is not about infinitesimal characters.** For `GL_2(ℝ)`, the module of the character
  blocks `|·|` and `sgn` (an irreducible principal series) and the module of the induced block
  of weight `1` and exponent `1/2` (the functions of the principal series of `|·|` and `1`
  whose weight-`0` Fourier coefficient along the rotations vanishes, a discrete series up to
  twist) are both irreducible and have the same infinitesimal character `(1, 0)`. Their
  `L`-factors differ: `Γ_ℝ(s+1)²` against `Γ_ℂ(s+1) = Γ_ℝ(s+1) Γ_ℝ(s+2)`, so their pair factors
  against the trivial character block differ. U therefore predicts that no nonzero intertwiner
  exists between them, in agreement with Knapp 1994, Theorem 2, since they correspond to the
  non-isomorphic Weil-group representations `|·| ⊕ sgn` and the induction of the character
  `z ↦ (z/|z|) |z|` of `ℂ^×`.

## Use

The module `Langlands.Global.RankinSelberg.RealStandardPairingReduction` (not part of this
module) proves that D and U imply `RealStandardPairingPairLStatement`, the local premise
(module `RealPlaceContragredientPremises`) in the reduction of the real-place contragredient
pair-factor statement `RealPlaceContragredientPairLStatement` (module
`RealPlaceContragredientReduction`). In that proof, D identifies `I(ds.map dualBlock)` with
the `O(n)`-finite dual of an irreducible `I(ds)`, and U is applied to the resulting nonzero
intertwiner from the module of the contragredient's parameter.

Related Library material for later proofs: the `GL_n(ℂ)` analogue of the uniqueness behind U is
`ComplexLanglandsQuotientUniqueStatement`, proved as `complexLanglandsQuotientUnique` in
`Langlands.Representation.Archimedean.ComplexLanglandsQuotientUniqueProof`. The independence of
real factor presentations on the Weil side is the Library statement
`Langlands.LocalFactor.RealFactorPresentationIndependenceStatement`, which has no proof in the
Library.

## Provenance and status

Both statements are internal and derived: they split the local pairing premise
`RealStandardPairingPairLStatement` into a duality statement and a classification statement,
stated with the Library's actual modules. They rest on the literature below; neither is proved
in this module.

- A. W. Knapp, *Local Langlands correspondence: the archimedean case*, in: Motives, Proc.
  Sympos. Pure Math. 55, Part 2 (1994), 393–410 (project source `knapp-1994-archimedean-llc`;
  PDF page = printed page + 10): building blocks (2.2), p. 400; unitary induction (2.4) and
  Langlands classification, Theorem 1, p. 400; association (3.4) and local Langlands
  correspondence, Theorem 2, p. 403; Weil-group `L`-factors (3.6), p. 404.
- A. W. Knapp, *Representation Theory of Semisimple Groups: An Overview Based on Examples*
  (1986) (project source
  `provided-40cace9c0f8c2361e7b3d7459f7908362f819b68114945405f1c16d968b21855`; a scan without
  text layer, PDF page = printed page + 14, locators checked on rendered pages): Chapter VII, §1,
  pp. 167–169 (normalized induction, (7.2), (7.3a)); §2, item (2), formula (7.4), p. 170; double
  induction formula (7.5), pp. 170–171.
