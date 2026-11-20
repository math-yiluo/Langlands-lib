# Rational similitude of polarized relative Frobenius

Let \(X\) be a polarized \(p\)-divisible formal order module over a
\(\mathbf Z_p\)-algebra of exponential characteristic \(p\). Fix a coefficient
map \(\theta\) equal to the \(m\)-fold Frobenius. Given the isogeny property of
the actual relative Frobenius \(f:X\to X^{(\theta)}\),
`frobeniusRationalSimilitude` constructs a full-order rational similitude on
the entire affine base. Its forward section is the image of \(f\) in the
rational Hom sheaf. `frobeniusRationalSimilitude_hasMultipliers` verifies the
forward multiplier \(p^m\) and the inverse multiplier \(p^{-m}\) on the
represented scalar torsion, in the sense of the local numerator equations.

The forward pairing is the relative Frobenius power formula. To construct the
inverse, choose an integral dual isogeny \(g\) whose composites with \(f\)
are \([p^d]\). The inverse tensor is \(p^{-d}g\). Apply the forward pairing
equation to \(gx,gy\), then use bilinearity to obtain
\[
  e_X([p^m]gx,[p^m]gy)=e_{X^{(\theta)}}(x,y)^{p^{2d+m}} .
\]
This holds on every scheme test of each torsion level. The integral isogeny
\([p^m]g\) represents \(p^{d+m}f^{-1}\), so its multiplier gives the rational
inverse multiplier \(p^{2d+m-2(d+m)}=p^{-m}\).

This is the rational pairing calculation for the rigidifier in Michael
Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper
half spaces* (1997), Appendix (A.4), printed p. 114 (PDF p. 40). Compare
M. Rapoport and Th. Zink, *Period Spaces for p-divisible Groups* (1996),
Lemma 6.44 and its proof, printed pp. 309–310 (PDF pp. 321–322), for the
Frobenius and inverse-dual relation in the split case. The isogeny and kernel
rank of \(f\) have their own target in `RelativeFrobeniusIsogenyStatement`.
