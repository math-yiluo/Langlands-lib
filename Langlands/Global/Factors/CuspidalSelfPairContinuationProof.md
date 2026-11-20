# Holomorphic continuation of the partial cuspidal self-pair Euler product

`Langlands.Global.cuspidalSelfPairContinuation` proves
`Langlands.Global.CuspidalSelfPairContinuationStatement.{u, uQ}`. The statement
takes a number field `F : Type u` with `[CompactSpace (AdeleQuotient F)]` and
actual cuspidal realizations `T` and `Td` of `GL_(r+1)`. It assumes
`HasUnitaryCentralCharacter T` and
`Td.realization.IsContragredientOf T.realization`. The spectral presentations
`P` of `T` and `Pd` of `Td` use the independent factor universe `uQ`. The finite
set `S` of finite places contains both presentations' exceptional sets.

The proof constructs a holomorphic function `L` on `Re s > 1` and takes the
convergence threshold to be `1`. For each `s` in that half-plane, the norms
`‖partialEulerFactor P Pd hP hPd v s - 1‖` are summable over finite places
`v ∉ S`, and the factors have unconditional product `L s` (`HasProd`).

## Implemented proof

1. Choose a spectral presentation `Pc` of the actual pointwise conjugate
   `T.conjugate`. Its full-operator contragredient property identifies its
   spectra with those of the supplied contragredient `Td` at common
   unramified places. Choose a nonzero vector spherical outside `S`. Its
   Whittaker function `W` is nonzero at some `g`, where a nonnegative
   Schwartz–Bruhat test `Φ` can be chosen to equal one at the last row of
   `g`. The test is standard outside a finite set. [Conjugate presentation](../RankinSelberg/SelfPairContragredient.md),
   [spherical and Whittaker data](../RankinSelberg/SelfPairPositiveData.md),
   [Schwartz test](../RankinSelberg/SelfPairSchwartz.md).
2. The conjugate vector has Whittaker function `conj W` for the inverse
   additive character. The global integrand is a Mellin kernel with
   nonnegative weight `‖W‖² Φ`. The product of the two central characters is
   trivial, so the equal-rank analytic theorem gives a holomorphic integral
   on `Re s > 1`. Applying `equalUnfoldingStatement_proof` gives equality
   with the absolutely integrable Whittaker integral sufficiently far to
   the right. The bilateral form of Landau's theorem then gives
   integrability throughout `Re s > 1`. [Self-pair integral](../RankinSelberg/SelfPairWhittaker.md),
   [equal-rank unfolding](../RankinSelberg/EqualUnfoldingProof.md),
   [Landau's theorem for the Mellin kernel](../RankinSelberg/SelfPairLandau.md).
3. At `s = 2`, full support of the quotient measure and positivity at `g`
   give a positive integral. Exhaustion by partial domains gives a finite
   `A` with positive partial integral at `2`. It contains `S` and all the
   exceptional places of `Pc`, the character and the test. The positive
   real exponential in the Mellin kernel leaves the support of the weight
   unchanged, so the integral on that partial domain is positive for each
   real `σ > 1`. [Integral positivity](../RankinSelberg/SelfPairIntegralPositivity.md),
   [positivity at real parameters](../RankinSelberg/SelfPairLandau.md).
4. When `Re s` exceeds both `1` and the local radius,
   `EqualEulerReduction.setIntegral_insert` gives the one-place factorization
   for an added place outside `A`. Induction over a finite set `E` of such
   places gives the finite-product identity on the same half-plane. The
   integral for `A ∪ E` equals the product of factors over `E` times the
   integral for `A`. The Mellin integrability from step 2 gives holomorphy of
   the restricted integrals on `Re s > 1`. The independent bound
   `‖α‖ ≤ q_v^(1/2)` on each Satake eigenvalue gives holomorphy of the local
   factors there. The identity theorem then extends the finite-product
   identity to `Re s > 1` in `eq_prod_of_insert_of_differentiableOn`. At a real
   `σ > 1`, `prod_bound_of_re_pos` bounds the norms of the finite Euler
   products outside `A` by the full integral divided by the positive partial
   integral for `A`. The spectrum comparison transfers these bounds from
   `Pc` to the supplied `Pd`. [One-place factorization](../RankinSelberg/EqualEulerFactorizationReduction.md),
   [Satake bound](CuspidalPairAbsoluteConvergenceProof.md),
   [Whittaker integral bound](../RankinSelberg/SelfPairEulerBound.md).
5. `continuation_of_prod_bound_other` absorbs the finite set `A \ S` into
   the bounds. At each real `σ > 1`, taking logarithms bounds the finite
   sums of the nonnegative local logarithmic series. This proves
   summability of the double series with coefficients
   `|tr(A_v^k)|² / k`, multiplied by `q_v^(-kσ)`. The resulting complex
   Dirichlet series is holomorphic on `Re s > 1`. Its exponential is the
   required function, and the logarithmic expansion gives `Summable`
   and `HasProd` for the original Euler factors outside `S`.
   [Passage from finite bounds to convergence](CuspidalSelfPairContinuationAssembly.md).

## Provenance

This proof uses the global integral of Route A. In Jacquet–Shalika's proof
of Lemma (5.2), the quotient by a product of local integrals gives
continuation near each point where the local data are chosen to make the
denominator nonzero. The Lean proof uses the conjugate Whittaker integral to
get bounds on finite products at real arguments, then uses the nonnegative
coefficients of the self-pair logarithm to obtain the holomorphic function.

- H. Jacquet and J. A. Shalika, *On Euler products and the classification of
  automorphic representations I*, Amer. J. Math. 103 (1981), 499–558.
  Lemma (5.2) and its proof, pp. 554–555, give the continuation target and
  global integral route. Corollary (2.5), p. 515, gives the local bound,
  used here in non-strict form. The global integral and its continuation
  are in (4.5.4)–(4.6), pp. 550–551. Proposition (2.3), pp. 511–513
  (PDF 13–15), evaluates the unramified local integral of the normalized
  spherical Whittaker functions against the characteristic function of the
  integral lattice. This supplies the local factor in the one-place
  factorization. Formula (4.7.2), p. 552 (PDF 54), factors the global integral
  into local integrals. The proof of Theorem (4.8) on that page applies
  Proposition (2.3) to those integrals at unramified places. Formulas
  (5.3.1)–(5.3.3), p. 556, give the logarithmic expansion and the nonnegative
  self-pair coefficients. Registered source
  `provided-6d5abbbab517cf7269b6ab243e0d7a101940980b658f88cb722e13748f802ad4`,
  SHA256 `c6b669ccf00a3ce35c10aa60f3dc7538d6269bf279791e5286b893c597275620`.
- J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004),
  §2.3, pp. 208–211, gives the global integral in the conventions used by
  the Library, the ordinary unfolding on p. 210, and Theorem 2.2 on
  p. 211. Registered source `cogdell-2004-analytic-theory-gln`,
  SHA256 `8117f145869274324b12344dc83fa3289e3bd27c515b8d0d4a0211cd64174944`.
- The published bilateral Landau theorem uses D. V. Widder, *The Laplace
  Transform*, Chapter II, §5, Theorem 5b and proof, pp. 58–59, and Chapter VI,
  §1, formula (4), pp. 237–238 of the 1946 printing. The corresponding
  Dirichlet series argument is G. H. Hardy and M. Riesz, *The General Theory
  of Dirichlet's Series* (1915), Theorem 10, p. 10.
  [Landau–Mellin sources and proof](../../Analysis/LandauMellin.md).
