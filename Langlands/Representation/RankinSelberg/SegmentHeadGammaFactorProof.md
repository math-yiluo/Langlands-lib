# Gamma factors of actual segment heads

The theorem `Langlands.RankinSelberg.segmentHeadGammaFactor` proves the exact
published `SegmentHeadGammaFactorStatement.{uF,uV,uW}`. It supplies a rational
gamma factor for every pair of supplied segment heads and factors for all
pairs of base blocks, with the required finite double-product identity. The
field universe and the two base-carrier universes are independent. The head
carriers retain the statement's `max uF uV` and `max uF uW` universes.

The source formula is Henniart, *Une caractérisation de la correspondance de
Langlands locale pour GL(n)* (2002), Section 2.6, printed page 595, third
display. Its multiplicativity input is Jacquet–Piatetski-Shapiro–Shalika,
*Rankin–Selberg Convolutions* (1983), Theorem (3.1)(i), printed pages 404–405.
The registered sources are `henniart-2002-characterization` (SHA-256
`40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`)
and `jpss-1983-rankin-selberg` (SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`).
Both relevant scans were visually read. The implementation applies the
Library's proved multiplicativity and component-comparison results to the
actual normalized inductions specified by the statement.

The proof proceeds as follows.

1. For each supplied head, the proved segment-head derivative theorem gives
   nonvanishing of its full derivative. The private functional bridge uses
   `TopLocalization.topLocalizationIso` to identify this derivative, after the
   rank-zero cast, with the upper-unipotent character coinvariants. The
   `functionalsLocalizationDualEquiv` equivalence identifies their algebraic
   dual with the Whittaker functionals. The algebraic dual of a nontrivial
   complex vector space is nontrivial, giving a nonzero functional. Together
   with the head's proved irreducibility and admissibility, this supplies
   genericity and the existing rational gamma-factor certificate.
2. The representative-independent head relation provides a surjective
   intertwiner from the increasing segment induction. Taking the full
   subrepresentation makes the head an actual irreducible component. A
   private conversion identifies the induction's smooth block family with
   the explicit real determinant twists on the uniform positive block shape.
3. The supercuspidal Kirillov theorem and multiplicity one give full
   Whittaker type for each twisted supercuspidal base. The proved
   `TemperedLFactorGamma.gamma_doubleProduct` supplies all block gamma
   certificates and the gamma certificate for the double product of the two
   normalized inductions. Full Whittaker type also supplies their smoothness.
   The proved `componentFactorComparison` identifies this product with the
   gamma factor of the supplied generic heads.
4. The two public transport lemmas in this module move the twist of the
   second block to the first block. Opposite real determinant twists preserve
   the full gamma relation: specialize `UnramifiedGammaTwist.pair_factor` to
   inverse characters, whose product is one, and spectral shift zero. The
   zero shift rescales the rational function by the unit one. Applying the
   opposite twists proves the converse. Reading the larger rank first covers
   both positive rank orders, and the rank-zero branches reduce to the
   statement's `False` relation. Moving a second exponent `y` to the first
   exponent `x` then gives `x + y` by the twist composition law.

For blocks indexed by `i : Fin Δ.length` and `j : Fin Δ'.length`, this last
step yields the exact exponent `(i + j : ℕ)` cast into the reals. Thus the
zero-based indices agree with Henniart's exponent `i + j - 2` for one-based
indices. All factors use the supplied additive character, canonical p-adic
topology, normalized determinant absolute value and supplied self-dual Haar
measure. No segment formula, genericity premise or factor-existence premise
remains as an additional hypothesis. This module proves the gamma component;
the L and contragredient-L components remain separate obligations.

The functional, rank-cast and block-family bridges are internal derived
arguments for the published target, rather than extra assertions attributed
to either original source. Finite heartbeat bounds cover the block-family
conversions and the final assembly.
