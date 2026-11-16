# Arithmetic and parameter transport for two induced real blocks

This internal helper module derives consequences of the published definitions in
`RealUnlinkedSwapReduction`, `RealLargeStandardIrreducibleReduction` and `StandardModule`.
Its namespace is `Langlands.Archimedean.RealInducedSwapArithmetic`. It does not prove
`RealInducedSwapStatement` in full.

`inducedParameter d` is the pair `(d.weight.natAbs, d.exponent)`, consisting of the absolute
weight and the complex exponent visible to an induced real block. It forgets the sign of
the weight of the original complex character. `inducedParameter_eq_iff` expands equality
of these pairs into equality of their components. The parameter map is the selected
definition of this contribution.

For nonzero weights, `unlinked_iff` expands the Mœglin data of two induced blocks and gives
the two forbidden exponent differences, indexed by positive natural numbers. In
`unlinked_iff_of_order`, the decreasing order of real exponents excludes the reverse
difference: its real part is nonpositive, whereas the forbidden value is positive.
`unlinked_of_im_ne` excludes linking when imaginary exponents differ. `unlinked_of_gap_lt`
excludes linking when the ordered real exponent gap is below the first forbidden value.
These are arithmetic consequences of the Library's exact linking definition.

`standardModule_eq_of_absolute_weights` proves equality of standard modules when position
characters agree and the absolute weights of induction blocks agree at each position.
The proof uses the membership criterion for the principal series and transfers every
Fourier vanishing condition across the equality of its weight bound.
`standardModule_replace_induced` applies this criterion to an induced block whose absolute
weight and exponent are unchanged, in arbitrary surrounding lists. Finally,
`swap_of_same_parameters` replaces each of two adjacent induced blocks to show that their
standard modules in the two orders are equal, then transports the identity intertwiner
using the published `RealInjectiveIntertwinerExists.of_eq`.
`standardModule_replace_of_parameter_eq` packages replacement using equality of the
`inducedParameter` values.

The proofs use no irreducibility criterion or unproved intertwining theorem. The
same-parameter swap needs neither rank nor nonzero-weight hypotheses, because it follows
from equality of spaces of functions for every ambient rank. All content is derived
internally; the original mathematical conventions remain those documented with the
imported Library declarations.
