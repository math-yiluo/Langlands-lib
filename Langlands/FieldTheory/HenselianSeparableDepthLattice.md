# Actual valuation-depth lattices in finite separable extensions

Let `v : Valuation K (WithZero (Multiplicative ℤ))` have Henselian valuation
ring `O`, and let `L/K` be a separable extension. The declaration
`henselianSeparableDepthLattice v hH L r` is the actual `O`-submodule
of elements of `L` whose normalized prolonged additive value is at least
the real number `r`. The fields may occupy independent universes.

For finite-dimensional `L/K`, the field trace cannot decrease the normalized
value. The proof embeds in the separable closure, expresses the trace as a
natural multiple of the sum of the minimal-polynomial roots, uses invariance
of the prolongation on those roots, and applies the ultrametric inequality
to the sum and its natural multiple. The nonnegativity criterion on embedded
base scalars follows from the negative integer logarithm. It proves scalar
closure of the depth ball. Increasing the depth gives a submodule.

Assume additionally that `v` is surjective. The base valuation ring is a
discrete valuation ring: surjectivity makes the valuation value group the
full unit group of the integer value monoid, which is nontrivial and cyclic.
The actual depth ball is finite and free over `O` when `L/K` is finite.
To prove finiteness, choose a field basis `b`. Its trace-dual coefficient
at `j` is `trace(x * b j)`. For `x` in the depth ball its value is at least
`r + value(b j)`. Choose a nonzero base scalar `t j` with integer value
`floor(r + value(b j))`; the quotient of the coefficient by `t j` is integral.
Trace-dual expansion therefore places the ball in the `O`-span of the
finite family `t j * b.traceDual j`. Noetherianity gives finiteness of the
submodule, and torsion freeness over the principal ideal ring gives freeness.

Every element of `L` can be moved into the ball by a nonzero integral base
scalar. For nonzero `x`, choose a scalar of integer value
`ceil(max(0, r - value(x)))`; zero is immediate. Consequently the ball spans
all of `L` over `K`. This last conclusion does not require finite
dimensionality.

These are derived supporting constructions for the additive depth models in
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Section C.2,
printed pp.697–698 (PDF pp.728–729). The trace-dual finite-module proof is
internal linear algebra, rather than a literal statement or proof from that
section. No integral group model, supplied relative-root identification,
apartment comparison, or complete C.5.3 assertion is made here.
