# Regular cyclic induction: proofs of the two reductions

The module `Langlands.Automorphic.Unramified.CyclicRegularInductionReductionProof`
proves both propositions of
`Langlands.Automorphic.Unramified.CyclicRegularInductionReductionStatement`:

| Theorem | Proves |
| --- | --- |
| `cyclicRegularInductionReduction` | `CyclicRegularInductionReductionStatement.{uF,uE,uV,uW}` |
| `cyclicRegularInductionReductionTC` | `CyclicRegularInductionReductionTCStatement.{uF,uE,uV,uW}` |

Both theorems keep the four independent universe parameters of the
statements. A closing `example` instantiates both at `.{0,0,uV,uV}`.

Neither proof uses the premise `CyclicNormKernelUnramifiedOrderStatement`.
The twist step needs only `η_v(ϖ_v)^f = 1` at the retained places, where `f`
is the residue degree of an upper place above `v`. This identity follows from
the triviality of `η` on norms. That `η_v(ϖ_v)` has order exactly `f` is not
needed.

## The unrestricted reduction

`cyclicRegularInductionReduction` discards the norm-order premise. It applies
the Library theorem `cyclicRegularInductionNormReduction` (module
`Langlands.Automorphic.Unramified.CyclicRegularInductionNormReduction`) to the
existence premise `CyclicRegularInductionExistenceStatement` and the recovery
premise `CuspidalEulerConstituentRecoveryStatement`.

## The totally complex reduction

`cyclicRegularInductionReductionTC` uses the same argument as
`cyclicRegularInductionNormReduction`, over a totally complex base field `F`.
It takes the totally complex premises
`CyclicRegularInductionExistenceTCStatement` and
`CuspidalEulerConstituentRecoveryTCStatement`. Three lemmas of the module
carry the argument.

1. **Residue-degree power of the character value** (private
   `finiteUniformizerValue_pow_inertiaDeg`). Fix a base place `v` and an
   upper place `w` above it with ramification index one. Embed the canonical
   uniformizer unit of `F_v` into `E_w`. Its local norm is the uniformizer
   raised to the local degree, which is the residue degree `f` because the
   ramification index is one. The norm of the idèle class supported at `w`
   is the idèle class of this local norm
   (`ideleClassNorm_ofAdicCompletion`), and `η` is trivial on it. Hence
   `η_v(ϖ_v)^f = 1`.
2. **The twist is another weak induction** (private
   `isWeakInductionOf_determinantTwist`). Let `c` be weakly induced from `d`
   with attached spectra `s` and `t`. The twist of `c` by the finite-order
   character `η` has the scaled system `scale η.finiteUniformizerValue s` as
   an attached spectrum, after enlarging its exceptional set
   (`IsoClass.HasSpectralSystem.determinantTwist`). Scaling
   substitutes `η_v(ϖ_v) X` for `X` in each Euler polynomial
   (`SpectralSystem.scale_eulerPolynomial`). At almost every place the Euler
   polynomial of `s` is the induced polynomial of `t`. That is a product over
   the upper places `w` above `v`, each unramified, of polynomials in `X^f`,
   where `f` is the residue degree of `w`. By lemma 1 the substitution fixes
   each factor. So the scaled and unscaled
   systems have the same Euler polynomials at almost all places, and
   `SpectralSystem.IsArithmeticWeakInductionOf.of_sameEulerPolynomials` gives the twisted class
   as a weak induction of `d`.
3. **Uniqueness over a totally complex base**
   (`isWeakInductionOf_unique_of_cuspidalEulerConstituentRecoveryTC`). Let
   `c` and `d` be cuspidal classes in `IsoClass F r` for one rank index `r`,
   so both of rank `r + 1`, and both weakly induced from `t`.
   The two upper presentations may differ, but
   `exists_sameEulerPolynomials_of_isWeakInductionOf` gives attached spectra
   of `c` and `d` with equal Euler polynomials at almost all places. The
   one-element families `c` and `d`, with these spectra, have the same
   finite-sum Euler polynomials (`IsobaricData.sameEulerPolynomials_finiteSum_one`).
   The totally complex recovery premise gives a bijection `Fin 1 ≃ Fin 1`
   matching the two families, and `PositiveRankCuspidalClass.ofFixedRank_injective`
   gives `c = d`. Neither class needs a unitary central character. This is
   the argument of the Library theorem
   `weakInductionUniqueness_of_cuspidalEulerConstituentRecovery`, with the
   recovery premise applied to the totally complex `F`.

Ranks follow the convention of `CuspidalOperatorRealization`: a cusp in
`CuspidalOperatorRealization F n` or a class in `IsoClass F n` has rank
index `n` and actual rank `n + 1`. The main proof applies the existence
premise to `F`, `E`, the generator, the rank index `m`, the upper cusp `T` of
rank `m + 1`, and the unitarity and regularity hypotheses on `T`. This gives a
rank index `r` and an actual lower cusp `S` of rank `r + 1 = (m + 1)[E:F]`,
weakly induced from `T`. Lemma 3 shows that every cuspidal class in
`IsoClass F r` weakly induced from `T`, that is, every such class of rank
`r + 1`, equals the class of `S`. This covers an arbitrary competitor, with no
unitarity hypothesis. By lemma 2 the twist of the class
of `S` by `η` is weakly induced from `T`, so lemma 3 identifies it with the
class of `S`. `IsoClass.isFiniteOrderDeterminantTwist_iff_eq` turns this
equality into the self-twist relation `IsFiniteOrderDeterminantTwist η c c`
for `c` the class of `S`.

`CyclicRegularInductionNormReduction` keeps lemmas 1 and 2 private, so this
module cannot import them. It proves them again with the same proofs.

## Sources

The reduction derives from Arthur and Clozel, *Simple Algebras, Base Change,
and the Advanced Theory of the Trace Formula* (Annals of Mathematics Studies
120, 1989), Chapter III:

- Definition 6.1 and Theorem 6.2, printed p. 215, define automorphic
  induction from `GL(n)` over `E` to `GL(nl)` over `F`, where `l = [E:F]`,
  by Hecke eigenvalues at almost all places, and assert existence and
  uniqueness. In the Lean statements `n = m + 1` and `nl = r + 1`. On p. 215
  uniqueness follows from the eigenvalues at almost all primes. In the Lean
  proof the existence premise plays the role of existence, and lemma 3 gives
  uniqueness.
- The proof of Theorem 6.2, pp. 215–217, treats an extension of prime
  degree `l` through formulas (6.1) and (6.2) on p. 216. Formula (6.1), at a
  split place, takes the direct sum of the upper Hecke matrices at the places
  above `v`. Formula (6.2), at an inert place, chooses one `l`-th root of each
  eigenvalue of the upper Hecke matrix and multiplies it by each power of a
  primitive `l`-th root of unity `ζ` once. At such a place `η_v(ϖ_v) = ζ`
  (p. 216), and multiplication by `ζ` permutes these eigenvalues. Lemma 2 is
  the polynomial form of this invariance, for each upper place with its own
  residue degree.
- Lemma 6.4, pp. 217–218, concerns an upper cusp `π_E` not isomorphic to any
  proper Galois conjugate. It gives the unique representation `π_F` of
  `GL(nl)` over `F` whose base-change lift is the product of the Galois
  conjugates of `π_E`. This `π_F` is cuspidal and satisfies
  `π_F ≅ π_F ⊗ η_{E/F}`. The discussion after the lemma on p. 218
  (Corollary 6.5 with trivial stabilizer) identifies `π_F` with the
  representation automorphically induced from `π_E` in the sense of
  Definition 6.1 and Theorem 6.2. In the Lean proof the self-twist relation
  comes from uniqueness and lemma 2.
- Equation (2.4), p. 200, from Jacquet–Shalika, compares classes through
  their Hecke matrices at almost all places. The premises
  `CuspidalEulerConstituentRecoveryStatement` and
  `CuspidalEulerConstituentRecoveryTCStatement` state this comparison for
  cuspidal classes, through their Euler polynomials.
- Theorem 3.1, p. 201, shows that `η_v(ϖ_v)` is a root of unity of order
  `f_v` at almost all places. Only the identity `η_v(ϖ_v)^{f_v} = 1` enters
  this proof, and lemma 1 derives it from the triviality of `η` on norms.
