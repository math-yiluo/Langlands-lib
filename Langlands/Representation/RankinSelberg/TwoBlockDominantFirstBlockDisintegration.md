# Dominant first-block joined rows and local upper coefficient

This derived helper supplies the exact supplied-product row disintegration
for the first-block calculation of JPSS, *Rankin–Selberg Convolutions* (1983),
Section 4.9, printed pp.416–418, used in Section 4.10(2), printed p.419.
The paper illustrates the larger-rank calculation with zero complementary rows;
the general complementary row parameters here are derived from the published
matrix definitions, affine supplied-Haar bridge and unequal-rank convergence.

Write a = m₀ + 1 and b = m₁ + 1. `firstBlockRowJoinEquiv` concatenates the
Jacquet rows Z of shape b × a before the external rows T of shape j × a,
without changing the order within either rectangle.
`measurePreserving_firstBlockRowJoinEquiv` identifies the exact product of
the two supplied rectangular Haar measures with the supplied measure on
(b + j) × a matrices. It uses the sum/product and coordinate equivalences
for finite product measures, including when j is zero.

`integral_firstBlockJoinedRows` assumes genuine product integrability of
H(X,q) on the supplied small quotient measure times the joined rectangle.
It proves integrability of the resulting Z average and the identity

    ∫ Z, ∫ q, ∫ T, H(join(Z,T),q) = ∫ q, ∫ X, H(X,q).

The proof transports product integrability through the row equivalence and
product associativity, applies Fubini on almost every Z fiber, and then uses
the measure-preserving substitution and Fubini for the joined integral.
It does not infer convergence from an equality of total Bochner integrals.
The auxiliary `unequalRankSliceCoefficientAt_eq_integral` proves that the
rank transport in the smaller coefficient agrees with the rank transport
in its actual integrand.

`firstBlockUpperRowAverage` integrates the actual larger upper scalar over U
at the representative diag(q.out,I_b) R(Z) g and columns (U,Y).
`firstBlockUpperRowAverage_eq` applies the affine substitution T = Uv + YZ.
The result uses the actual smaller quotient integrand with b + j rows and
unchanged k, the right-translated test function, and the actual coefficient
`firstBlockCoefficient ell f g`. This expression removes the chosen
representative and retains the base-point weight |det g|^(s − (j+k+1)/2 + j).

`firstBlockUpperCoefficient` integrates that row average at s = 0 over Z and
the supplied small determinant slice. Under actual smaller-product
integrability, `firstBlockUpperCoefficient_eq_small` proves that its Z
average is integrable and that the coefficient equals the actual smaller
JPSS coefficient times the same base-point weight. The proof uses the
joined-row result and the exact affine row-average identity.

`upperSliceConvergesAt` transports the published upper product convergence
theorem to a fixed large rank using only its rank equality. The theorem
retains representations of full Whittaker type and permits both supplied
functionals to vanish. `firstBlockUpperCoefficient_eq_small_of_whittakerType`
uses it with the translated actual coefficient-image vector and the
contracted first-block coefficient. Thus the local coefficient identity
has no additional analytic premise for these inputs. It retains the exact
supplied scalar Haar, compatible small quotient measure, its sigma-finiteness,
and the supplied right-invariance certificate. Independent field, test-vector
and block-vector universes are preserved.

This helper proves a local coefficient disintegration. Global quotient
disintegration, lower convergence, application of the first-block functional
equation and the final finite Laurent convolution identity remain separate
obligations.
