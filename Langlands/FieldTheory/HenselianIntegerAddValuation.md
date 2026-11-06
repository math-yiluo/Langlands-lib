# Integer-normalized additive valuations over Henselian fields

This internal construction combines the published `integerValuationToReal`,
`henselianRealGaloisProlongation` and `LocalField.logAdditiveValuation`.
The base field and its algebraic Galois extension have independent universes.
The input is an arbitrary integer-valued valuation whose valuation subring is
Henselian. No topology, completeness, residue-field hypothesis or surjectivity
is needed for this construction.

`exists_integerRealProlongation` applies the real Galois prolongation theorem.
The real realization has exactly the original valuation subring, so its
Henselian hypothesis follows from the supplied one. The chosen prolongation
`henselianIntegerRealValuation` restricts exactly to the base real realization,
and every base-field algebra automorphism preserves its values.

`henselianIntegerAddValuation` takes the negative logarithm divided by
`Real.log 2`, sending zero to infinity. The published negative-logarithm
construction proves the additive valuation laws. Automorphism invariance
passes through this construction. On a nonzero embedded base element `x`
the value is exactly the real integer `-WithZero.log (v x)`: the real
realization is `2 ^ WithZero.log (v x)`, and the logarithmic scale cancels.
Thus positive values correspond to the base maximal ideal.

For a finite Galois extension, the field norm is the product over all
automorphisms. Induction over that finite product and value invariance give
the norm formula with multiplier the extension degree. The norm of a
nonzero element is nonzero. Its embedded value is an integer by the base
formula, and division by the positive extension degree gives the claimed
inverse-degree integer lattice containment. No surjectivity onto that
lattice is asserted.

This is a normalized valuation prerequisite for the coordinate construction
of Kaletha–Prasad, Construction 6.1.17. It does not identify coordinates
with relative root groups or construct an apartment. Its proof is derived
from the imported Library results; it makes no additional literature claim.
