# Strict Tate algebras and restricted series over Banach rings

Authors: Worker 36 (original construction), Worker 56 (coefficient generalization).

The carrier is the actual subalgebra of Mathlib's multivariate formal power
series for which the coefficients tend to zero along the cofinite filter.
For a finite variable set over a complete nonarchimedean field this is the
usual strictly convergent power-series algebra of polyradius one.
Addition and multiplication come from formal series; multiplication is
convolution.

The Lean construction allows an arbitrary variable type and incomplete
coefficient rings. These are explicit extensions of the source's finite
variable Banach-algebra definition: restrictedness means that the
coefficients tend to zero along the cofinite filter on the actual finitely
supported exponent set. Completeness is proved when the coefficient ring
is complete. No identification with a different notion of infinite-variable
analytic algebra is asserted.

The construction works over any ultrametric normed commutative coefficient
ring. Coefficients identify the additive group with functions on the discrete
monomial set that vanish at infinity. The supremum norm is transported along
this additive equivalence. The ultrametric estimate for finite convolution
sums proves submultiplicativity. Completeness is transported from Mathlib's
complete space of functions vanishing at infinity, when the coefficient ring
is complete.

Coefficientwise estimates prove the ultrametric triangle inequality.
A constant series has exactly the norm of its coefficient. Norm one is
inherited when the coefficient ring has norm one. These instances share the
same coefficient supremum norm. The normed-algebra instance over a normed
field is provided separately; the original affinoid construction over a
nonarchimedean field retains its scope. Trivially valued fields and the
zero coefficient ring are not excluded from the ring-level construction.
When the coefficient ring is nontrivial, the actual restricted-series
subalgebra inherits nontriviality. This instance allows the analytic division
theorems to be applied with a smaller Tate algebra as coefficient ring.

This generality is needed to treat a finite-variable Tate algebra as restricted
series in its final variable with coefficients in the smaller Tate algebra.
This file does not prove that regrouping equivalence or Weierstrass division.
The generic-coefficient change preserves the underlying construction and
intrinsic proofs.

Source: the retained Berkovich-course notes, Section 2.1, page 1, define the
finite-variable Tate algebra; Section 2.2, pages 2-3, defines restricted series
over a nonarchimedean commutative Banach ring before Weierstrass division.
The full 14-page original was read; page 1 and page 3 were visually checked.
It is undated notes of part of Vladimir Berkovich's course, note-taker
unidentified; PDF metadata dated 2011-02-28. Source
`provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`,
retained at
`literature/Retained original of Berkovich's Affinoid algebras course notes (14 pages).pdf`.

The proof route uses Mathlib's `MvPowerSeries.IsRestricted.subring` and
`ZeroAtInftyContinuousMap`. Only polyradius one is constructed here;
weighted radii and analytic domains require further constructions.
