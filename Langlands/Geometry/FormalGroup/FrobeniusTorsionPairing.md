# Relative Frobenius on the represented torsion pairings

Let \(M\) and \(N\) be coordinate formal modules over a commutative
\(O\)-algebra \(R\) of exponential characteristic \(p\), with divisible
scalar towers for \(\pi\in O\). Let the \(O\)-algebra endomorphism \(\theta\)
of \(R\) be the \(m\)-fold Frobenius. For an affine \(R\)-test of exponential
characteristic \(p\), `affineFrobeniusTestMap` gives the absolute Frobenius map
from the test with structural map composed with \(\operatorname{Spec}(\theta)\)
to the original test. The structural triangle commutes because ring
homomorphisms preserve powers. The action on global sections is the
\(p^m\)-power map.

Suppose \(p\) is prime. At each represented scalar kernel, the image of a
point under relative Frobenius corresponds, under the coefficient
comparison, to restriction along this affine test map. The proof checks
this identity in coordinates, where relative Frobenius raises each
coordinate to the \(p^m\)-th power. Compatibility of the Cartier pairing
with coefficient extension and restriction then gives the power identity
on affine tests. The trivial test ring is covered by uniqueness of its
unit. For an arbitrary scheme test, both torsion points factor through the
spectrum of its global sections, since the two scalar kernels are affine.
Restricting the affine identity gives
\[
e_\theta(F^m x,F^m y)=e(x,y)^{p^m}
\]
on all scheme tests. Here \(e\) is the pairing of the supplied torsion
Cartier duality and \(e_\theta\) is its coefficient extension.

The natural-number scalar \(k\) acts on represented torsion points by the
\(k\)-th power in their multiplicatively written point group. Bilinearity
therefore identifies the right-hand side with \(e([p^m]x,y)\).
For a supplied torsion principal polarization this proves the integral
similitude equation with multiplier \(p^m\) in \(O\).

This calculation supplies the pairing identity behind the Frobenius change
of rigidifier in Harris (1997), Appendix (A.4), printed p. 114 (PDF p. 40),
and the dual-summand Frobenius relation in Rapoport–Zink (1996), Lemma 6.44
and its proof, printed pp. 309–310 (PDF pp. 321–322). The argument works
directly with the represented torsion pairings and takes the compatible
Cartier duality or polarization as input.
