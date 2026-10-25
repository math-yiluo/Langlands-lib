# Product opposite generalized kernel

`Langlands.Jacquet.refinedOppositePowerKernelJacquet` proves the published
`RefinedOppositePowerKernelJacquetClause` with independent field and carrier
universes. The helper `refinedOppositePowerKernel_eq_jacquetKernel` proves the
same equality for every smooth representation; admissibility is used only to
supply smoothness in the exact wrapper.

This is an internal extension of the Library's `BlockPowerKernelProof` argument
to the actual product lower radical. For each radical element, component
contraction gives a threshold in each factor; their finite supremum gives a
single threshold valid in the product, including an empty outer shape. Span
induction on the genuine coinvariant relations then shows that each relation is
killed by every sufficiently deep compressed action. The actual product
compression multiplication law identifies these actions with powers of one
operator.

Conversely, quotient compatibility of compression identifies the class of a
compressed vector with the action of the inverse product block scalar on its
coinvariant class. This scalar belongs to the actual refined Levi, whose
descended action is invertible. A vanishing power therefore forces the original
class to vanish. These inclusions establish equality of the generalized kernel
and the kernel of the actual fixed Jacquet map.

The proof uses actual product compact open subgroups and arbitrary smooth
representations of the product Levi. It assumes neither tensor factorization
nor finite-dimensionality of the whole carrier. Stable-image surjectivity and
the generic constituent comparison are separate statements.
