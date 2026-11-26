# Fourier boundary values for products of cone denominators

`OrthantFourierBoundaryStatement`, proved by `orthantFourierBoundary`, computes a
boundary value in coordinates indexed by a finite type. Fix nonzero real numbers
\(d_i\) and a test \(f\) integrable for the supplied s-finite frequency measure
\(\nu\). An s-finite measure is a countable sum of finite measures.
The oriented orthant is \(C=\{x:d_ix_i>0\ \text{for all }i\}\).
With frequency phase \(e^{-i\sum_i x_i y_i}\), assume that the Fourier integral
\(\widehat f(x)=\int e^{-i\sum_i x_i y_i}f(y)\,d\nu(y)\) is integrable on \(C\).
Then as \(t\) tends to zero through positive values,

\[
\left(\prod_i \operatorname{sgn}(d_i)\right)
\int \left(\prod_i (t d_i+i y_i)^{-1}\right)f(y)\,d\nu(y)
\longrightarrow \int_C \widehat f(x)\,dx .
\]

The physical measure is product Lebesgue measure. The finite type can be empty.
The frequency measure may include the dual Haar normalization.

For positive \(t\) the one-dimensional complex exponential integral over the
half-line of sign \(d_i\) is \(\operatorname{sgn}(d_i)/(t d_i+i y_i)\). The signed
factor comes from the endpoints in the antiderivative. The norm of the full
integrand before integration in either variable is bounded by the product of the
integrable exponential damping on the orthant and \(|f(y)|\). Product integration
gives the product of the one-dimensional integrals, and Fubini for the s-finite
frequency measure gives
`orthantReciprocal_integral`. The resulting damping exponent \(\sum_i d_i x_i\)
is nonnegative on \(C\). Removing the damping uses
`tendsto_integral_remove_exponential_damping`.

This is the coordinate calculation of P. Delorme, *Troncature pour les
espaces symétriques réductifs*, Acta Math. 179 (1997), §9, (9.1) and Lemma 11,
printed p. 72 (PDF p. 32). The registered source
`delorme-1997-reductive-symmetric-space-truncation` has SHA-256
`02eb996aa75322ecb3294cbe839dd9cc2b37077d781455e49128a2f01e0dc70c`.
The coroot coordinates there turn the denominator into a product of linear
factors and the measure into a multiple of product Lebesgue measure. The
boundary value here is formulated against each test through an ordinary
limit of its scalar integrals.
