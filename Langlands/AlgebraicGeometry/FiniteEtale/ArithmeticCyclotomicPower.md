# Cyclotomic powers over arithmetic fields

`ArithmeticCyclotomicPowerStatement` concerns a field \(K\) purely inseparable over a
finitely generated subfield. For any prime \(\ell\), it supplies a single natural number
\(q>1\) such that at each level some automorphism of the separable closure of \(K\) over \(K\)
acts on all \(\ell^n\)-th roots of unity by raising them to the \(q\)-th power. The exponent is
independent of the level.

## Lean proof

In characteristic zero, irreducibility of the cyclotomic polynomial over the rational prime
field gives an automorphism of the algebraic constants sending a primitive root to its
\((\ell+1)\)-st power. Every root at that level is a power of a primitive root. In positive
characteristic \(p\), Frobenius on the constants gives exponent \(p\).

Choose a transcendence basis for the finitely generated subfield over its prime field. Algebraic
independence survives adjoining the algebraic constants. Acting on the coefficients of
multivariate polynomials while fixing the variables extends each chosen automorphism to the
rational function field over the constants. The extension lemma for algebraic field embeddings
then gives an automorphism of the algebraic closure fixing the rational function field over the
prime field.

The given finitely generated subfield is finite over that last rational function field. Let
\(d\) be the order of the permutation group on its finite set of embeddings into the algebraic
closure over the rational function field. Taking the \(d\)-th power of an automorphism fixes
the finitely generated subfield. Its purely inseparable extension is also fixed because each
element has a power under an iterate of Frobenius in the fixed field, and that power determines
the element uniquely. The proof restricts the resulting automorphism to the separable closure.
The exponent on roots of unity is the corresponding \(d\)-th power of the prime-field exponent.

## Source

Deligne, *Résumé des premiers exposés de A. Grothendieck*, SGA 7 I, Exposé I, paragraph
following Proposition 1.1, p. I-6, observes that if \(\ell\) is prime to the characteristic
exponent, no finite extension of a field finitely generated over its prime field, or of a purely
inseparable extension of such a field, contains all \(\ell\)-power roots of unity. In this range
the condition is equivalent to infinite image of the \(\ell\)-adic cyclotomic character. The
Lean proof constructs a positive integer power shared by all levels. It also covers the case
where \(\ell\) equals the characteristic and the only root at every level is \(1\).
