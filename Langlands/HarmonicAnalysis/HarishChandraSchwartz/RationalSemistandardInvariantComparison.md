# Certified comparison on the actual semistandard components

The normalized tensor used by Waldspurger (2003), V.3 and VI.3 (printed
pp. 295 and 305–306), extends the standard-operator comparison to the unitary
orbit. `WeylSectionComparisonData` displays the comparison inputs at each
actual source index and compact Weyl lift to each parabolic at the conjugate
Levi. They include the common compact, compact Weyl representatives, actual
dynamic cocharacter presentations, and the normalized discrete-series data
of `WeylSections.HasIntrinsicSourceNormalization`. The construction is
conditional on `WeylSections.ClosedSectionComparisonStatement` at each arrow.
That target retains the regular standard tensor, normalized Haar,
coefficient and form preservation, and finite compact-level realization.

`WeylSectionComparisonData.fiberComparison` takes the unique actual comparison
from that target. It intertwines the two product-group actions and is natural
under all inducing isomorphisms, including self-twists. Its evaluation is
bijective by the V.3.1 property at the unit parameter and the canonical
changes of compact model. `fiberComparisonEquiv` uses this bijectivity
to equip the same comparison with its equivariant inverse.

The chosen smooth realization respects the actual compact levels and their refinement
inclusions in the conjugate-base presentation. `smoothComparison` composes
it with the canonical smooth change to the intrinsic target base.
`smoothComparison_apply` evaluates the result in the actual conjugate
inducing fiber. The change of base preserves that coefficient value.
`smoothComparison_symm_apply` identifies the inverse smooth comparison
on each fiber with the inverse of `fiberComparisonEquiv`.
