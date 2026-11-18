# Changing the generic character of the complex local Whittaker model

Write \(n=r+1\) and \(t=\operatorname{diag}(a^r,a^{r-1},\ldots,1)\)
for \(a\in\mathbb C^\times\). This module works with the coefficient
model in `ComplexPlaceFunctionalEquationReduction.lean`. Jacquet defines
the Whittaker models used in the local integrals in *Archimedean
Rankin–Selberg integrals* (2009), printed and PDF pp. 3–6. The model
transport and the scalar action below are derived within Lean for the
Library's model.

## Translation of the model

Conjugation by an invertible diagonal matrix preserves the upper
unitriangular subgroup. For \(t^{-1}ut\), each entry on the first
superdiagonal is \(a^{-1}\) times its value at \(u\). The sum of these
entries gives the identity between \(\psi_b(t^{-1}ut)\) and
\(\psi_{ba^{-1}}(u)\) in the Library's positive trace convention.

For each intertwiner \(B\), the proof takes the linear map with values
\(g\mapsto Bf(t^{-1}g)\). The conjugation identity supplies its
unipotent equivariance. Left translation is smooth and commutes with
right compact translation and right differentiation. The growth estimate
uses submultiplicativity of the complex matrix height, proved from its
Frobenius-norm formula and the corresponding bound for a product.
Consequently the translated map is an intertwiner for \(\psi_{ba^{-1}}\).
Its range lies in the new model. The supremum of the original ranges
then gives the translation result on every model element.

## Scalar matrices

For an inducing list \(d\) of length \(n\), `centralCharacter` is the
product \(\omega_d\) of its characters. Evaluating the normalized
principal-series character on scalar diagonals gives \(\omega_d\).
The normalization exponents sum to zero by pairing an index with its
reverse, and the remaining product runs through the inducing list in
its original order.

For \(z\in\mathbb C^\times\), the proof starts on an intertwiner image
and takes the path \(g\operatorname{scalar}(\exp(t\log z))\) for
real \(t\). The published diagonal derivative formula gives a scalar
right-derivative equation for standard vectors in the central direction
\((\log z)I_n\). The intertwiner preserves this equation. The chain rule
along the path therefore gives the scalar exponential differential
equation for the output coefficient. At \(t=1\) its exponential multiplier
equals \(\omega_d(z)\) by the principal-series character formula. The
identity \(W(g\,\operatorname{scalar}(z))=\omega_d(z)W(g)\) extends from
intertwiner images to their supremum by linearity.
