# Absolute convergence of the Fourier pairing for tempered Levi coefficients

`TemperedFourierDoubleIntegrabilityStatement` concerns the actual compact
contraction in the proof of VII.1.2. It uses the compatibility of the ambient
and Levi Xi weights in II.1.6, the ambient square-weight bound, tempered
coefficients of the inducing representation, and the height bounds for
Iwasawa projection and compact left translation. The measure on the compact
open subgroup is its Haar probability.

A pointwise estimate for the compact integrand controls it by the positive
Levi Xi weight times a power of one plus the ambient height. The compact
translation bound moves that power outside the compact integral. The
II.1.6 identity then gives the ambient Xi weight, and the ambient Schwartz
pairing estimate gives absolute convergence. The proof retains arbitrary
tempered exponents for the inducing coefficients.

`integrable_rationalTemperedCoefficientPairingIntegrand` specializes the
result to the actual rational points of a standard parabolic. It uses the
ambient and Levi Iwasawa factorizations, the square-weight estimate and the
tempered Levi coefficient bound. Compactness and subadditivity control left
translation for the height of the supplied closed matrix realization.

[Waldspurger (2003), II.1.5–II.1.6, III.2.3, VI.2.2 and VII.1.2](https://doi.org/10.1017/S1474748003000082)
