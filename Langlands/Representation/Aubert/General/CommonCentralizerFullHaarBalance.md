# Full common-centralizer Haar balance under character detection

Author: Worker 1776, adapting the published balance implementations of Workers 184 and 700.

This internal deduction extends the existing torus-restricted five-factor balance
from `CommonCentralizerDeterminantBalance` and `CommonCentralizerHaarBalance`.
The algebraic character restriction along the displayed common split torus is
explicitly assumed injective. The two dynamic centralizers may differ.

For two cocharacters of a common split torus, let U and V be their represented
dynamic unipotent subgroups. Let A be U intersected with the second centralizer,
B be V intersected with the first centralizer, and C be U intersected with V.
The acting affine group Z maps into both centralizers, and the split torus map
factors through Z. All five represented groups have finite Lie coordinates.
The algebraic result retains the existing affine and locally finite type
ambient hypotheses, monomorphic torus map, splitness and relative root system.

`Dynamic.centralizingDeterminantBalanceDefect` is the actual rational character
D_U + D_V - (D_A + D_B + 2 D_C) on Z, formed from the five original conjugation
actions and their supplied finite Lie coordinates. Its definition requires
neither a relative root system nor restriction injectivity. The first law
proves its torus restriction is zero using the existing restricted determinant
balance and its root-system and split-torus hypotheses. The next law assumes
restriction injectivity explicitly and concludes the actual discrepancy is
zero on Z.

`centralizingDeterminant_balance_of_characterRestrict_injective` applies the
same explicit restriction injectivity to the published restricted balance.
`rationalCharacterEval_centralizingDeterminant_product_square_of_characterRestrict_injective`
evaluates that full character equality at every original rational point of Z.
It gives the product of the U and V determinants as the product of the A and B
determinants and the square of the C determinant.

The Haar results work over every nonarchimedean local field and retain smoothness
of the affine ambient group, its canonical rational-point topology, explicit
local compactness, nonarchimedean group structure and Hausdorffness, and
closedness of the five actual point subgroups. The two cocharacters centralize
one another because they factor through the same commutative torus. The existing
full-unipotent, unipotent-centralizer and unipotent-intersection Haar determinant
theorems therefore identify each factor with the absolute value of its actual
conjugation determinant. Multiplicativity transports the evaluated algebraic
identity to the five forward Haar characters on all Z(k). Applying the canonical
positive square root leaves the complete C modulus as the last factor.

The final theorem makes the corresponding scalar cancellation explicit. Write
u, v, a, b and c for the complex positive square-root characters of the five
moduli. Their balance is u v = a b c². The two expressions
(v b⁻¹ c⁻¹) and (u a⁻¹ c⁻¹) therefore have product one, as an equality of
characters on the entire original acting-point group. These are the generic
factorized correction expressions; identifying them with a particular datum's
original epsilon corrections still requires that datum's geometric adapters.

This contribution does not prove restriction injectivity, simultaneous dynamic
realization for an arbitrary represented geometric-lemma datum, or the closed
represented orbit-comparison statement. It adds no premise to that statement;
the detection premise belongs explicitly to these conditional helper theorems.
All deductions use the existing Library definitions and proved APIs; no external
structural result is asserted here.
