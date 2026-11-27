# Polynomial symbols of a finite-dimensional Lie algebra

In the ordered Poincaré–Birkhoff–Witt basis of an enveloping algebra,
the degree-\(d\) symbol keeps precisely the basis monomials of degree
\(d\) and sends them to the corresponding commutative monomials.
A word of length \(d\) has symbol equal to the product of the linear
polynomials of its letters. For words in basis elements, reorder the
letters into PBW order. The commutators contribute only to lower
degree. Multilinearity gives the formula for arbitrary letters.

On elements of filtration degree at most \(d\), `pbwSymbol_commutator`
carries commutation with a Lie generator to the polynomial derivation
induced by that generator's Lie bracket. The word calculation expands
the commutator using the product rule. At degree \(d\), each bracket
replaces one letter and the word formula gives the corresponding
derivative term. Shorter words have zero degree-\(d\) symbol and
commutation with a generator preserves their filtration bound.
