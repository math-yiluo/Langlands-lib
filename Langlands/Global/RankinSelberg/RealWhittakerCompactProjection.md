# Finite separation of compactly averaged real Whittaker coefficients

For a coefficient map \(B\) realized by a continuous Whittaker evaluation on
the smooth standard module, `RealWhittakerCompactProjectionStatement`
separates
\[
  \int_{\mathrm O(n)} \kappa(k)\,B(f)(xkg)\,dk
\]
into a finite sum \( \sum_i B(u_i)(x)\,\ell_i(\rho(g)f) \).
The continuous weight \(\kappa\) must have finite left-translation orbit
span. The \(u_i\) are compact-finite vectors of the original standard
module. The \(\ell_i\) act on the expanded smooth position principal series
and satisfy finite compact right-derivative bounds. The vectors and
functionals work simultaneously for every \(f,x,g\).

On the compact Banach profiles the averaging operator is convolution.
Left invariance of Haar measure writes its kernel as \(\kappa(x^{-1}y)\).
A finite basis of the left orbit span of the weight separates this
kernel into a finite sum in \(x\) and \(y\). The Banach averaging
operator therefore has finite-dimensional range.

Take a basis of the image of the genuine smooth module under that
operator. Each basis vector is the empty word coordinate of a
compact-finite smooth average. Lift those vectors back to the
original compact-finite source. The coordinate functionals are bounded
because they act on a finite-dimensional normed space. Hahn–Banach
extends them to the Banach profile carrier, and composing with
averaging and the empty word gives continuous functionals on the smooth
carrier. The compact derivative extension theorem supplies the
\(\ell_i\) on the expanded position model.

Finally, evaluate the compact integral of the orbit of \(\rho(g)f\)
after right translation by \(x\). Continuous scalar evaluation
commutes with the compact smooth integral, giving the left hand side.
Expanding the average in the lifted basis gives the separated sum.
This is the internal compact averaging step used in Jacquet's
equal-rank recursion, §8.2.
