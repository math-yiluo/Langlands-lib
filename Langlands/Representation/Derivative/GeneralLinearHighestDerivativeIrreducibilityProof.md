# Irreducibility of the highest actual general-linear derivative

Worker 1002. `Langlands.Derivative.generalLinearHighestDerivativeIrreducibility`
proves the published proposition
`Langlands.Derivative.GeneralLinearHighestDerivativeIrreducibility.{uF,uV} F T`
without changing the statement or its imports. The theorem applies to every positive
rank, every character of the specified type, every irreducible smooth complex `π`,
and every highest-order datum `hd`. There is no admissibility, finite-length, or
unitarity premise. The carrier universe is `max uF uV` and the result includes
highest derivatives of rank zero.

The target is the irreducibility assertion of A. V. Zelevinsky, *Induced representations
of reductive p-adic groups II. On irreducible representations of GL(n)*, Ann. Sci.
ENS (4) 13 (1980), Theorem 8.1, printed p. 195 (PDF page 32), registered as
`zelevinsky-1980-induced-ii`, SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The proof does not identify the multisegment label of the derivative, the other
assertion of Theorem 8.1.

## Implemented proof

1. **Two ordered products.** Socle exhaustion realizes `π` inside an ordered
   product of segment socles with datum `d`. The one-step lemma in
   `HighestDerivativeChainSegmentProduct` and exactness show that `hd.order` is the
   sum of the cuspidal ranks of these segments: the derivative of `π` at that sum is
   nonzero and every higher derivative embeds into a zero derivative of the product.
   Write `k = hd.order`. The Library's contragredient and real-twist compatibilities
   realize `π' = |det| π̃` inside another ordered product with datum `c`, whose
   segments are the duals twisted by `|det|`. The two multisegments have the same
   level sequence, since neither operation changes segment ranks or lengths.
   In particular `k` is the highest order for both `π` and `π'`. Their derivatives
   `X` and `Y` at this order embed in the respective truncated products `d'` and
   `c'`, which have the same tail level sequence.
2. **Smooth duality of the derivatives.** Evaluation pairs the mirabolic
   restrictions of `π` and `π'` with covariance `|det|`. Smooth bidual injectivity
   gives nondegeneracy in `π`, and separation by evaluation gives it in `π'`.
   Bernstein–Zelevinsky (1977), Proposition 3.8, applied in each direction and
   transported to the actual `GL` derivatives, gives an invariant pairing
   nondegenerate in `X` and an invariant pairing nondegenerate in `Y`. The former
   gives an injection `X → Ỹ`. Smooth contragredient exactness and biduality give a
   surjection `Y → X̃`: `Y` has finite length as a subobject of the truncated
   segment product, hence is admissible by admissibility of the irreducible factors.
   The latter pairing gives an injection `Y → X̃`. The surjection implies that
   `X̃` has finite length at most that of `Y`, and a proper image of the injection
   would have strictly smaller length than `X̃`. Thus the injection is an isomorphism.
3. **A quotient cannot both lose and retain the chain.** If `S` were a nonzero
   proper subrepresentation of `X`, write `W = X/S`. Exactness and homogeneity,
   iterated by `not_derivativeChain_of_quotient`, say that `W` fails the chain of
   `d'`. Yet `W̃` is nonzero (compact opens are cofinal and smooth functionals
   separate vectors), and its pullback embeds into `X̃ ≅ Y`, hence into `c'.induced`.
   Evaluation pairs `W̃` with `W` invariantly and nondegenerately in `W̃`.
   `derivativeChain_of_pairing` shows that `W` retains the chain of `c'`, the same
   sequence. This contradiction gives the subrepresentation dichotomy for `X`,
   and `hd.nonzero` supplies its nontriviality.

The duality part follows the approach of Zelevinsky's proof. The final contradiction
instead uses iterated nonvanishing along the level sequence; it does not use the
multiplicity-one result of Theorem 7.1 or uniqueness of the highest derivative's
irreducible constituents.
