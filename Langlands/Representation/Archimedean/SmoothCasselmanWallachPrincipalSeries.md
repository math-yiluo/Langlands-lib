# Word estimates along principal-series quotients

The compact Banach model in `RealStandardCompactBanach` realizes the scalar minimal
principal series of a rank-matched list of characters of `GL₁(ℝ)`. Its equivalence
`compactFiniteEquiv` identifies the algebraic principal series with the compact-finite
genuine smooth vectors and preserves the two actions. All word seminorms below use
the genuine derivatives of the indicated Banach representation.

- `RealPrincipalSeriesWordBoundStatement` asks for an estimate of the underlying norm of
  a compact and Lie intertwiner from this algebraic principal series into the genuine smooth
  vectors of a jointly continuous Banach representation. The right side is a constant times
  a finite sum of word seminorms in the compact Banach model. The target representation and
  map may be arbitrary within these hypotheses.
- `RealPrincipalSeriesQuotientWordLiftStatement` starts with an algebraically surjective
  compact and Lie intertwiner `B` from this principal series onto an irreducible admissible
  module `V`. The given equivalence identifies `V` with all compact-finite genuine smooth
  vectors of a jointly continuous Banach representation. For each fixed finite sum of word
  seminorms of the principal series, the conclusion gives a finite sum of word seminorms
  of the Banach realization of `V` and a constant. For every `v` one can choose a
  compact-finite lift `w` with `B w = v` whose first sum is bounded by the second sum times
  that constant. The lift may depend on `v` and the prescribed seminorms.

These propositions isolate the two estimates in the quotient argument. Bernstein–Krötz,
*Smooth Fréchet globalizations of Harish-Chandra modules*, arXiv:0812.1684v3, registered as
`bernstein-kroetz-2014-smooth-frechet-globalizations-arxiv-v3` (SHA-256
`f5f2e79d87532c9ac46389d7eb1606e0301eac0ba7c7972ab628e278e091ca3e`), proves
minimal-principal-series goodness in Theorem 8.1 (pp. 35–36). The first estimate is the
finite-word form of continuity supplied by that goodness result and intertwiner lifting
(Proposition 11.2, pp. 46–47). The compact action sends compact-finite vectors to
compact-finite vectors under the given map. Polynomial operator growth gives the
Schwartz-algebra action by integration on genuine smooth vectors of the target, and their
Sobolev topology is the word topology. These are the Banach and smooth-vector comparisons
in §§2.3–2.4 (pp. 7–11). The compact Banach model gives the source globalization with
the same compact-finite module as the induced Hilbert model in Theorem 8.1.

For the second estimate, smooth exactness (Lemma 6.2, p. 31, and Theorem 10.6, p. 45)
gives a quotient of smooth Fréchet spaces. Openness gives control of smooth lifts. The
kernel is closed and group invariant, so compact averaging gives density of its
compact-finite part. Given a smooth lift and any algebraic lift of `v`, their difference is
in the kernel. Approximating that difference by compact-finite kernel elements yields
algebraic lifts with the same image. Including the empty word in the controlling sum and
enlarging the constant absorbs the approximation error for each nonzero vector. For the
zero vector take the zero lift.

`isRealGKModule_of_smoothKFiniteEquiv` transports the genuine real Harish-Chandra module
compatibility to an algebraic carrier. The inverse equivalence commutes with the compact
action, and it commutes with the complexified Lie action by induction on the real tensor
product. The quotient compatibility lemma then gives `IsRealGKModule`.

`realSmoothCasselmanWallachBound_of_principalSeries` uses that compatibility and
`realPrincipalSeriesQuotient` to get a nonzero algebraic principal-series map `B`.
Irreducibility gives surjectivity by `IsRealStandardIntertwiner.surjective`. Composing the
target map `f` with `B` gives another compact and Lie intertwiner, to which the first
estimate applies. Apply the second estimate to its finite set of words. For a lift of `v`,
the output of `f ∘ B` is `f v`, and multiplying the two constants gives the required bound.
The algebraic carrier and the two Banach carriers have independent universes.
