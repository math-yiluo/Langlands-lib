# The elliptic numerator from a finite rotation Fourier window

The existing Fourier window of weight \(m\) has indices
\(2k+1-m\) for \(0\le k<m\). This includes the parity condition
\(j+m+1\) even. `signedLowSum_eq_windowSum` obtains that parity by
averaging the two sign contributions, using the coefficient
\((1+(-1)^{j+m+1})/2\) at each low mode.
After multiplication by \(e^{i\theta}-e^{-i\theta}\),
its exponential sum telescopes to \(e^{im\theta}-e^{-im\theta}\).
The identity holds also for the empty window at \(m=0\).

`realStandardEllipticCartanWindow` inserts the radial factor
\(\exp(2xt)\) and identifies the result with the difference of the
two `complexTerm` factors in the finite Cartan numerator. The proof
uses the window enumeration and `expMode_add`, followed by the
finite telescoping identity. This internal calculation supplies the
angular normalization in a regular Cartan evaluation of the compact
trace integral.
