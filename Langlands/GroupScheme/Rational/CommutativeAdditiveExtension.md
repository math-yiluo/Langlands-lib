# Group sections of commutative additive extensions

Worker 1485. Internal derived construction for the assigned characteristic-zero
commutative unipotent classification. This unit constructs an actual group-scheme
section of a commutative affine extension with full monic vector kernel and
one-dimensional vector quotient. The quotient map must be flat and surjective.
No classification theorem is assumed; this remains a supporting unit of that
classification task.

For a field `k : Type u`, let `j : K ⟶ E` be monic on underlying relative schemes,
let `q : E ⟶ H`, and suppose the full all-test range of `j` equals the range of the
scheme-theoretic kernel of `q`. Assume `E` is commutative and supply natural vector
coordinates on `K` of dimension `d` and on `H` of dimension one. The construction
first takes any scheme section `s` of `q`, with affine `H`.

`additivePoint` identifies a scalar in a coefficient algebra with the quotient
point having that one additive coordinate. It preserves addition and commutes
with every coefficient algebra map. Each coordinate of the existing
`VectorExtensionDescent.defect` defines `scalarDefect`. Its image in `E` is
`s(x) s(y) s(x+y)⁻¹`. Naturality follows from the naturality of the actual defect
morphism and the coordinates. Commutativity and cancellation prove the ordinary
additive two-cocycle identity in each scalar coordinate.

`correctionPolynomial` applies the internal `NaturalAdditiveCocycle` integration
theorem to each coordinate. In characteristic zero it gives a polynomial `f_i`
with defect `f_i(x+y)-f_i(x)-f_i(y)`. No normalization at zero is required.
`correctionPoint` evaluates these polynomials on the quotient coordinate and
returns to actual kernel points. It is natural on all coefficient algebras, and
satisfies `b(tr) = defect(t,r) b(t) b(r)` in the kernel point groups.

The affine representability construction `homOfAffinePoints` turns this natural
family into `correctionHom`. The corrected scheme section is `(j ∘ b) s` in point
notation, with positive correction sign because of the chosen defect convention.
The correction is killed by `q`, so the corrected section remains a right inverse.
The cochain identity cancels its multiplication defect on affine tests. Equality
of the two morphisms on the universal pair, checked on every affine test, then
proves multiplicativity on every relative scheme test. `homOfPoints` packages
this into `extensionSection : H ⟶ E`, and `extensionSection_comp` proves that it
splits the original group-scheme quotient.

Finally `exists_extensionSection` assumes affine `E`, flat surjective `q`, the
same full monic kernel, and the existing predicates `IsVectorGroupOfDimension K d`
and `IsVectorGroupOfDimension H 1`. The existing affine vector-extension section
theorem supplies the initial scheme section, and the construction above supplies
the group section. The finite kernel dimension may be zero. No smoothness,
connectedness, algebraic closure, or unipotence comparison is needed in this unit.
