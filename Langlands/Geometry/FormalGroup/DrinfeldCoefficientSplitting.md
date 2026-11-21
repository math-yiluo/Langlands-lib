# Splitting the Drinfeld coefficient algebra

Let \(C\) be the integer ring of the given unramified subfield of reduced
degree \(d\). Fix a residue embedding into the framing field \(\kappa\).
The residue coordinate on a test algebra \(B\) lifts the resulting \(d\)
cyclic characters of \(C\) to maps \(\lambda_i:C\to B\).
`subfieldCyclicSplitting` identifies \(B\otimes_{\mathcal O_K}C\) with
\(\prod_{i\in\operatorname{Fin}(d)} B\) by sending \(b\otimes a\) to the
tuple with entries \(b\lambda_i(a)\).

For distinct indices \(i\) and \(k\), choose \(a\in C\) such that
\(\lambda_i(a)-\lambda_k(a)\) is a unit. Multiplying
\(1\otimes a-\lambda_k(a)\otimes 1\) by the inverse of that unit gives
a tensor whose evaluations at \(i\) and \(k\) are \(1\) and \(0\).
The product over the other coordinates lifts the \(i\)-th coordinate vector.
These lifts make the evaluation map surjective. The two modules are finite
free of equal rank, so the surjection is an isomorphism. The proof uses the
finite free module criterion in `OrzechProperty`, which also covers the zero
test algebra. The naturality calculation extends the coefficient lifts'
base change identity from pure tensors to all tensors.

The split algebra is a derived construction for the unramified coefficient
grading in the opening paragraph of §2B of Drinfel'd's paper, where the
division uniformizer shifts the coefficient characters.\
[V. G. Drinfel'd, *Coverings of p-adic symmetric regions*, 1976, §2B, p. 110](https://doi.org/10.1007/BF01077936)
