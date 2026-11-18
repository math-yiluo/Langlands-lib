# Premises for the real-place contragredient pair-factor reduction

Module: `Langlands.Global.RankinSelberg.RealPlaceContragredientPremises` (namespace
`Langlands.Global.RankinSelbergGlobal`).

This module defines one predicate and states one local premise and one reduction statement. It
proves nothing. The reduction is proved in
`Langlands.Global.RankinSelberg.RealPlaceContragredientReduction`. The local premise is open.

## The target

The reduction concerns `RealPlaceContragredientPairLStatement`, stated in
`Langlands.Global.RankinSelberg.RealLocalTheoryReduction`. It is one of the four premises of
`RealPlaceLocalTheoryReductionStatement`, which gives the real-place functional equation. It says
the following. Let `F` be a number field with compact adele quotient. Let `T`, `Td` be actual
cuspidal realizations of `GL_(r+1)` over `F` with `Td` contragredient to `T`, and `T'`, `Td'` actual
cuspidal realizations of `GL_(t+1)` with `Td'` contragredient to `T'`. Let `v` be a real place,
and let `ds`, `es`, `dds`, `ees` be real-place parameters at `v` of `T`, `T'`, `Td`, `Td'`
(`HasRealPlaceParameter`). Then

`(realPairLFactor dds ees).denominator =
  (realPairLFactor (ds.map dualBlock) (es.map dualBlock)).denominator`,

where `dualBlock` (`RealLocalJacquet.dualBlock`) replaces the inducing character of each block by
its inverse. A `ReciprocalEntire` consists of its denominator, the entire function `1/L(s)`, so
this is equality of the two pair `L`-factors.

## Notation

`realStandardKFinite n ds` (an abbreviation in `Langlands.Automorphic`) is the space of
`O(n)`-finite functions in the Library's real standard module `realStandardModule n ds`. That
module is a subspace of the normalized principal series of `GL_n(ℝ)`. A character block of `ds`
takes one diagonal position and an induced block `d` of weight `m` takes two. For an induced
block, the functions must also have vanishing Fourier coefficients of order `|k| < |m|` along the
rotation in those two coordinates (see `StandardModule.md`). `realStandardRep n ds` is right
translation by `O(n) = Matrix.unitaryGroup (Fin n) ℝ` and `realStandardLie n ds` is the right
derivative action of `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`. These are the Library's `(𝔤, K)`-module structure
(`Langlands.Representation.Archimedean.RealStandardModuleGKModule`), the same one used in
`Automorphic.CuspidalArchimedeanStandardIrreducibleStatement`. `IsIrreducibleGKModule` is the
Library's irreducibility: the space is nonzero and its only subspaces stable under both actions
are `⊥` and `⊤`.

## Definitions and statements

### `IsRealStandardInvariantPairing n ds dds P`

`P : realStandardKFinite n ds → realStandardKFinite n dds → ℂ` is a bilinear form, and

- `P (realStandardRep n ds k f) (realStandardRep n dds k f') = P f f'` for every `k ∈ O(n)`;
- `P (realStandardLie n ds (1 ⊗ X) f) f' + P f (realStandardLie n dds (1 ⊗ X) f') = 0` for every
  real matrix `X`.

This is `(𝔤, K)`-invariance with `K = O(n)`. Only the real directions `1 ⊗ X` are required. By
linearity they give invariance under the whole complexified Lie algebra.

### `RealStandardPairingPairLStatement` (local premise L_R)

For every `n` and all lists `ds`, `dds` of real blocks with `realRank ds = n` and
`realRank dds = n`, suppose that

- the `(𝔤, K)`-modules of `ds` and of `dds` are irreducible (`IsIrreducibleGKModule`), and
- some bilinear form `P` with `IsRealStandardInvariantPairing n ds dds P` is nonzero.

Then for every list `xs` of real blocks,

- `(realPairLFactor dds xs).denominator = (realPairLFactor (ds.map dualBlock) xs).denominator`, and
- `(realPairLFactor xs dds).denominator = (realPairLFactor xs (ds.map dualBlock)).denominator`.

L_R is stated with the conclusion in the form the target needs, pair `L`-factors against every
partner and in both slots. It does not say that `dds` is a permutation of `ds.map dualBlock`.
That stronger form would be false, because real block lists are not unique. An induced block of
weight `0` gives the same standard module and the same `L`-factor as two suitable character
blocks. Induced blocks of weights `m` and `-m` with the same exponent also give the same module.

Why L_R is true (standard theory, not proved here). Write `I(ds)` for the `K`-finite standard
module of `ds`.

1. The left and right kernels of `P` are subspaces stable under both actions. Since `P ≠ 0` and
   both modules are irreducible, both kernels are zero.
2. So `f' ↦ P(·, f')` is an injective `(𝔤, K)`-map from `I(dds)` into the `K`-finite dual of
   `I(ds)`. The dual of an irreducible admissible module is irreducible, so this map is an
   isomorphism.
3. The `K`-finite dual of `I(ds)` is irreducible and its Langlands parameter is the dual of the
   parameter of `I(ds)`. For normalized induction the contragredient of the representation
   induced from `σ` is induced from the contragredient of `σ`, and the contragredient of a
   building block of Knapp 1994, (2.2), is the building block with inverse character. In the
   Library this is the block `dualBlock`.
4. By Knapp 1994, Theorem 1(c), two Langlands quotients are equivalent only if their lists of
   building blocks agree up to order. By Theorem 2 they correspond to the same semisimple
   representation of the Weil group `W_ℝ`. So the Weil-group representations of `dds` and of
   `ds.map dualBlock` are isomorphic.
5. `realPairLFactor xs ys` is `realLFactor (realPairBlocks xs ys)`, a product over the blocks
   `RealBlock.tensor` of all pairs. Together these blocks describe the tensor product of the two
   Weil-group representations, and `realLFactor` multiplies their `L`-factors as in Knapp 1994,
   (3.6). The Library normalizes `Γ_ℂ(s) = 2(2π)^{-s}Γ(s)`, and then
   `Γ_ℝ(s)Γ_ℝ(s+1) = Γ_ℂ(s)`. So a weight-`0` induced block has the `L`-factor of its two
   character constituents, and the pair `L`-factor depends only on the isomorphism classes of
   the Weil-group representations. Step 4 then gives both equalities.

### `RealPlaceContragredientPairLReductionStatement`

`Automorphic.CuspidalArchimedeanStandardIrreducibleStatement.{u} →
RealStandardPairingPairLStatement → RealPlaceContragredientPairLStatement.{u}`.

The first premise is the published global irreducibility statement: a standard module that is a
parameter of an actual cuspidal realization at an archimedean place is irreducible. Only its
real-place half is used. This module adds no new global premise. The proof is
`realPlaceContragredientPairLReduction` in the reduction module. It builds, from the
contragredient pairing of `T` and `Td`, a nonzero invariant pairing of `I(ds)` and `I(dds)`, and
from the pairing of `T'` and `Td'` one of `I(es)` and `I(ees)`. Then L_R gives

`den L(dds × ees) = den L(ds.map dualBlock × ees) = den L(ds.map dualBlock × es.map dualBlock)`,

using the first conclusion for the pair `(ds, dds)` with partner `ees`, and the second conclusion
for the pair `(es, ees)` with partner `ds.map dualBlock`.

## Provenance and status

All declarations here are internal. They split `RealPlaceContragredientPairLStatement` into the
published global irreducibility statement and one local input. The construction follows the
complex-place analogue `ComplexPlaceContragredientPremises`. Its local premise is about block
permutations, which is true for complex characters but not for real blocks, so L_R is stated
through pair `L`-factors instead.

L_R is a standard fact about `GL_n(ℝ)` and is recorded as an open premise, not as a claim
proved in the Library.

- A. W. Knapp, *Local Langlands correspondence: the archimedean case*, Proc. Sympos. Pure Math.
  55, Part 2 (1994), 393–410 (project source `knapp-1994-archimedean-llc`): building blocks
  (2.2) and unitary induction (2.4), p. 400; Langlands classification, Theorem 1, p. 400; local
  Langlands correspondence, Theorem 2, p. 403; Weil-group `L`-factors (3.6), p. 404.
- A. W. Knapp, *Representation Theory of Semisimple Groups* (1986), Chapter VII, for induced
  representations and their contragredients. The retained copy has no text layer, so this
  citation is to the subject matter, not to a theorem number.
- H. Jacquet, *Archimedean Rankin–Selberg integrals*, Contemp. Math. 489 (2009). The local
  functional equation there is stated with the contragredient representation, whose parameter
  is the dual one.
