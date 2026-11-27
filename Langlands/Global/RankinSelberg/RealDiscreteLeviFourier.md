# Fourier bounds for products of real discrete-series cells

`realDiscreteLeviFourierBound` proves `RealDiscreteLeviFourierBoundStatement`. For each of finitely many discrete cells fix a positive absolute weight \(k_i\) and a Fourier degree bound \(D_i\). The compact profile \(F\) may couple the angular variables. In its \(i\)-th variable, with every other angle held fixed, it must be a linear combination of the modes \(\pm(k_i+1+2m)\) of absolute value at most \(D_i\). If \(|F|\leq R\), the integrand
\[
 F\bigl((\arctan x_i)_i\bigr)
 \prod_i (1+x_i^2)^{-(k_i+1)/2} e^{-2\pi i x_i s_i}
\]
is integrable for product Lebesgue measure. The absolute value of its integral is bounded by \(CR\prod_i |s_i|^{k_i/2}\), with a nonnegative \(C\) depending only on the weights and the degree bounds. Both signs and zero are allowed in each frequency. `mem_angularSpace_of_trigPoly` supplies the coordinate hypothesis from an ordinary trigonometric polynomial once its forbidden coefficients vanish.

The coordinate spaces are finite dimensional, so `RealLeviProducts.mem_prodSpan` expresses the profile as a finite sum of products. Expanding each factor gives a finite span of products of the individual modes. For one product mode, integration in the real cell coordinates separates by Fubini. The scalar estimate `realDiscreteAngularFourierBound` bounds each factor by the absolute frequency to power \(k_i/2\). Linearity gives the estimate for each fixed element of the product space. Finite-dimensional interpolation writes an arbitrary element using fixed profiles with coefficients given by evaluations. Those evaluations are bounded by \(R\), so the constant works uniformly over all the profiles, including ones obtained by varying a compact translate.

This is an internal Fourier estimate for the inner integrations over discrete blocks in a Jacquet integral. The open-cell integral appears in Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §7.2. The separate group-level tempered majorization is Proposition 3.4. [Author-posted edition, pp. 21 and 47](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
