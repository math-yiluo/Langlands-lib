# Actual algebraic tensor cohomology and analytic comparison

This internal construction uses the original algebraic coefficient action on
`S.Space ⊗[ℂ] Space e ρ`, with its reduced Lie module structure constructed
in `ArchimedeanAlgebraicCoefficientTensorComparison`. The pure-tensor formula
there identifies its second-factor operator with the original algebraic
`lieAction e ρ`. The full compact tensor action is the original diagonal
group action. `tensorAlgebraicCompactRepresentation_reduced_lie` restricts its
already proved algebraic covariance along the actual reduced Lie inclusion.
`tensorAlgebraicFiniteReducedLieHom` bundles original finite adelic translation
as a map of this actual reduced algebraic tensor Lie module.

Assume `NeZero n` for the horizontal differential and cohomology, as in the
analytic construction using the actual split-center retraction.
`tensorAlgebraicHorizontal_infinitesimal` derives the required original
algebraic insertion law. Given an actual algebraic horizontal cochain, take
its inverse image under the proved full horizontal analytic-algebraic
equivalence. Apply the derived analytic insertion theorem to that cochain,
then the actual reduced tensor Lie equivalence. Its Lie compatibility,
linearity and the horizontal equivalence's inverse law give precisely the
insertion sum for the original algebraic cochain. No algebraic insertion or
chain-compatibility certificate is supplied.

These derived covariance and insertion laws instantiate
`horizontalEquivariantDifferential` with the original algebraic Lie module.
`tensorAlgebraicHorizontalDifferential` therefore is the actual original
algebraic coefficient differential restricted to the original full compact
horizontal tensor cochains. Its value lemma identifies that differential
explicitly; its square is zero by the published coefficient square-zero
theorem. The original finite Lie module map and coefficient functoriality
prove that this differential commutes with the original finite horizontal
action.

`tensorAlgebraicHorizontalCycles`, `tensorAlgebraicHorizontalBoundaries` and
`tensorAlgebraicHorizontalBoundariesInCycles` are the actual kernel,
preceding differential ranges (zero in degree zero), and boundary inclusion
range inside cycles. `TensorAlgebraicHorizontalCohomology` is their actual
cycle quotient. `tensorAlgebraicHorizontalClass` is its quotient projection;
the specialized laws give surjectivity and characterize zero classes by actual
boundary membership. Original finite translation restricts to these actual
cycles and descends to this quotient, with its cycle-class formula and quotient
projection as a finite intertwiner.

`tensorAnalyticAlgebraicHorizontalDifferential` proves the horizontal
coefficient equivalence is a chain equivalence for the two actual restricted
differentials, by the previously proved full cochain differential comparison.
The published horizontal cohomology equivalence construction now restricts
this same finite-equivariant chain equivalence to cycles and descends to the
two existing quotient representations:

- `tensorAnalyticAlgebraicHorizontalCyclesEquiv` retains the underlying
  transported horizontal cochain.
- `tensorAnalyticAlgebraicHorizontalCohomologyEquiv` is an equivalence of the
  actual finite adelic cohomology representations.
- Its forward class formula sends a closed analytic representative to the
  class of its transported algebraic representative.
- Its inverse class formula transports algebraic representatives back by the
  inverse cycle equivalence.

Thus both cohomology objects arise from their original coefficient
differentials, and the comparison is a proved descended equivalence.
The number-field universe remains independent of the small finite selected
embedding and coefficient indices. Both complex-place orientations, all
original coefficient vectors, empty finite indices and every cochain degree
are retained. Positive rank is explicit for insertion, differential and
cohomology; the initial algebraic covariance and finite Lie map hold in every
rank. This construction introduces no topology on the function, tensor or
cohomology spaces and makes no nonvanishing or occurrence assertion.

The provenance is internal composition of the original algebraic tensor
actions, proved coefficient comparison, derived analytic insertion, actual
coefficient differential and published cycle/quotient equivalence construction.
No new original-source correspondence is claimed.
