# Affine denominators of a finite regularized spectral pairing

`affineRegularizedSum` is a finite sum of terms of the form in Delorme's (7.8)–(7.12). Each summand uses fixed coroot coordinates, a fixed polynomial translated by the cutoff, and a spectral coefficient holomorphic on a common open set containing the imaginary axis. The coroot evaluations depend affinely on the spectral parameter. The statement assumes that their linear parts are real on real inputs and that each affine evaluation is nonzero at some imaginary parameter.

For a translated polynomial \(q\) and coordinate \(\alpha\), the denominator of every monomial in the regularized integral divides the affine evaluation to the power \(\deg_\alpha(q)+1\). The proof replaces each term by the corresponding nonnegative remaining power after multiplying by these factors, retaining the signed factorial and the polynomial coefficient. These cleared expressions are entire in the affine evaluations. Multiplication by the exponentials, the other summands' denominator factors and the holomorphic coefficients gives one holomorphic numerator on the common coefficient domain. Where all the affine evaluations are nonzero, division by the common denominator gives the original sum.

The proof indexes each power as a repeated affine factor and applies `hasImaginaryHyperplanePresentation_of_affine_product`. This gives a centered local hyperplane presentation along the imaginary axis as well as holomorphy on the common coefficient domain with the affine zero sets removed. The presentation is the input to local division when the generic comparison supplies bounds on the imaginary axis.

See P. Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics **426** (2023), 109107, §7, pp. 24–25, (7.8)–(7.12).
