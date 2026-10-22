# Ring properties of actual strict Tate algebras

Author: Worker 56.

`StrictTateAlgebra.tateRingProperties` proves
`TateRingPropertiesStatement K` from the constructed Noetherianity and
factoriality theorems and their integral-closure consequence.
For every complete ultrametric normed field `K` and every `n : ℕ`,
the conclusion is the conjunction of `IsNoetherianRing`, `IsDomain`,
`UniqueFactorizationMonoid`, and `IsIntegrallyClosed` for
`StrictTateAlgebra (Fin n) K`. The valuation may be trivial.

Noetherianity is proved by induction on the variable count. A nonzero
ideal can be moved into coordinates where it contains a distinguished
series, giving a finite quotient over the smaller Tate algebra. This
makes the quotient ideal finitely generated; lifting its generators
proves finite generation of the original ideal.

The domain property is inherited from formal power series over the
coefficient field. For factoriality, coordinate change and preparation
reduce an element to a monic Weierstrass polynomial over the smaller Tate
algebra. Its monic factors remain Weierstrass polynomials. The actual
polynomial/analytic quotient equivalence transfers primality of the
factors to the analytic algebra. Induction and the Noetherian ascending
chain condition give unique factorization. Mathlib's unique-factorization
domain result then supplies integral closedness.

The wrapper merely assembles these proved properties. The proof assumes
no ring properties of the analytic algebra, and the Jacobson property is
not a conclusion.

The source is Proposition 2.3.2(i),(iii), pages 5-6, and Corollary 2.3.3,
page 6, of the retained Berkovich-course notes. Integral closedness is the
standard consequence of factoriality, also used in the domain case of
Proposition 2.6.1 on page 11. The helper Markdown explains the differences
between the implemented proofs and the source's Rückert presentation.
The published target and its source correspondence are recorded in
`TateRingPropertiesStatement.lean` and `TateRingPropertiesStatement.md`.

Source `provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
The retained source is
`literature/Retained original of Berkovich's Affinoid algebras course notes (14 pages).pdf`,
“2. Affinoid algebras,” notes of part of Vladimir Berkovich's course.
The note-taker and publication date are unidentified.
