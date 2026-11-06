# Euler polynomials of character-sum parameters

This is an internal helper module. It computes Weil–Deligne Euler polynomials
of the character-sum pairs from
`Langlands/Correspondence/UnramifiedReciprocityBridge.lean`, and of every pair
representing a character-sum parameter class. Everything is derived from
existing Library interfaces, so the module makes no new literature claim. It
proves neither `FullCorrespondenceUnramifiedStatement` nor any automorphic
statement.

Notation: `eulerPolynomial f = det(1 - X f)` is
`Langlands.LocalFactor.eulerPolynomial` (the reversed characteristic
polynomial). `LocalFactor.WeilDeligne.eulerPolynomial A I g` is the Euler
polynomial of `g` acting on the `I`-fixed part of the monodromy kernel of `A`,
that is, on `inertiaKernelRepresentation I A`.

## Linear algebra (`Langlands.LocalFactor`)

- `eulerPolynomial_eq_prod_of_repr`: let `b` be a finite basis of a free
  finite module over a commutative ring. If `f` acts diagonally in `b`, with
  `b.repr (f v) i = c i * b.repr v i` for all `v` and `i`, then
  `eulerPolynomial f = ∏ i, (1 - C (c i) * X)`. The proof shows that the matrix
  of `f` in `b` is `Matrix.diagonal c`, rewrites with the published
  `eulerPolynomial_eq_det`, and takes the determinant of a diagonal matrix.

## Zero monodromy and trivial inertia (`Langlands.WeilDeligneRepresentation`, `Langlands.LocalFactor.WeilDeligne`)

Let `I` be a normal subgroup and `A` a Weil–Deligne pair with
`A.monodromy = 0` on which every element of `I` acts as the identity.

- `inertiaKernelInclusion_surjective`: the inclusion of
  `inertiaKernelRepresentation I A` into the carrier is surjective. It is
  injective (`inertiaKernelInclusion_injective`), and by the published
  `inertiaKernel_rank_eq_iff` the two ranks agree. An injective linear map
  between spaces of equal finite rank is surjective.
- `inertiaKernelEquivOfMonodromyEqZero`: the same inclusion as a linear
  equivalence.
- `LocalFactor.WeilDeligne.eulerPolynomial_eq_of_monodromy_eq_zero`: for every
  `g`,
  `LocalFactor.WeilDeligne.eulerPolynomial A I g =
  LocalFactor.eulerPolynomial (A.representation g)`. The proof conjugates
  `A.representation g` by the equivalence above, using the published
  `LocalFactor.eulerPolynomial_conj`.

## Character sums (`Langlands.Correspondence`)

Here `ψ : ι → W_F →* ℂˣ` is a finite family (`ι : Type`), and
`characterSumPair.{uF, uP} F ψ` is the direct sum of zero-monodromy character
lines.

- `eulerPolynomial_characterSumPair_representation`: for every `g`, the Euler
  polynomial of `g` acting on the carrier of `characterSumPair F ψ` is
  `∏ i, (1 - C (ψ i g) * X)`. The basis is `Module.Basis.ofRepr` of the linear
  equivalence `⨁ i, ULift ℂ ≃ₗ (ι →₀ ℂ)` built from
  `DFinsupp.mapRange.linearEquiv` of `ULift.moduleEquiv` and
  `finsuppLequivDFinsupp`. In this basis `g` acts diagonally with entries
  `ψ i g`, and this holds definitionally.
- `eulerPolynomial_characterSumPair`: if every `ψ i` is trivial on
  `Weil.Local.localInertia F`, then
  `LocalFactor.WeilDeligne.eulerPolynomial (characterSumPair F ψ)
  (localInertia F) g = ∏ i, (1 - C (ψ i g) * X)`. The proof combines the two
  results above with `characterSumPair_monodromy` and
  `characterSumPair_isUnramified`.
- `eulerPolynomial_of_isCharacterSumParameter`: let `e` be any reciprocity
  candidate and `χ : Fin (r + 1) → QuasiCharacter F` a family whose pullbacks
  `weilCharacter F e (χ i)` are trivial on inertia. Let
  `D : WeilDeligneClass.{uF, uP} F r.succPNat` satisfy
  `IsCharacterSumParameter F e χ D`. Then every local pair `A` with
  `classOf A = parameterForget F D` satisfies
  `LocalFactor.WeilDeligne.eulerPolynomial A (localInertia F) g =
  ∏ i, (1 - C (weilCharacter F e (χ i) g) * X)`. The proof composes the
  published equivalence invariance
  `LocalFactor.WeilDeligne.eulerPolynomial_eq_of_equiv` along `A ≃ B`, where
  `B` is the witness of `IsCharacterSumParameter`. It continues along
  `characterSumPair ≃ B`, obtained from `directSumCongr` of
  `zeroMonodromyCongr` of the `characterLineEquiv` equivalences followed by
  the witness equivalence.
- `weilCharacter_localGeometricFrobenius`: under a geometric candidate `e`,
  for unramified `χ`,
  `weilCharacter F e χ (localGeometricFrobenius F) = χ ϖ`, where `ϖ` is
  `F.canonicalTopologicalData.uniformizerUnit`. This follows from
  `weilCharacter_apply_of_isUnramified` and the published
  `localGeometricFrobenius_degree`, which gives degree `1`.
- `eulerPolynomial_of_isCharacterSumParameter_of_isGeometricReciprocity`: let
  `e` be a geometric candidate and every `χ i` unramified. If
  `IsCharacterSumParameter F e χ D` holds and `classOf A = parameterForget F D`,
  then
  `LocalFactor.WeilDeligne.eulerPolynomial A (localInertia F)
  (localGeometricFrobenius F) = ∏ i, (1 - C (χ i ϖ) * X)`. The proof
  specializes the previous result at the geometric Frobenius lift. Trivial
  inertia action comes from `weilCharacter_eq_one_of_mem_localInertia`.

The results are stated for every representative `A` of the underlying pair
class rather than through a class-level Euler polynomial. Such a
representative exists by `Quotient.exists_rep`. The module adds no continuity
or semisimplicity hypothesis.
