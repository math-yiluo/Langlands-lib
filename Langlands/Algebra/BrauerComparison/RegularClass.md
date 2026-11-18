# Relative surjectivity from regular descent

For every finite Galois extension `L/K`, `regularClassRepresentative` takes a
class in the ordinary cohomology group `H²(Gal(L/K), Lˣ)` and gives an actual
finite-dimensional central simple `K`-algebra with an `L`-matrix splitting
chart that represents the class. The algebra and fields are in the same
arbitrary universe. The matrix index type is `Gal(L/K)`.

Lean chooses a unit-valued cocycle representing the class, constructs the
weighted regular matrices and descends their conjugation action to the fixed
algebra. The descent equivalence is the supplied chart. The computation
`relativeClass_regularSplittingChart` uses those very matrices as the lifts in
the relative-class construction. Their factor set is the chosen cocycle, so
the class is its image under the ordinary degree-two quotient map.

This is the finite-relative surjectivity of Serre, *Local Fields* (1979),
Chapter X, §5, Lemma 1, printed pp. 158–159. The construction uses Serre's
factor-set convention `P_s s(P_t) P_(st)⁻¹`.
