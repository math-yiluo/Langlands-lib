# Conditional reduction for unramified root-filtration boundedness

Worker 312. This is a derived reduction for Task 6433. It retains two explicit
unproved inputs: `HenselianDiscreteQuasiSplitStatement` and
`QuasiSplitIntegerBoundedApartmentExistenceStatement`. It does not prove the
unconditional `MaximalUnramified.ZeroRootFiltrationBoundedStatement`.

The helper
`IntegerValuationBuildingData.isAlgebraicallyBounded_filtration_of_quasiSplit`
starts from bounded apartment existence and a supplied building datum over a
henselian discretely valued field for a quasi-split group. Existence gives a
full V 6-compatible apartment class for the datum's actual maximal split torus.
`IntegerValuation.IsOmegaCompatible.changeCentralizer` transfers that class's
compatibility to the supplied centralizer representative. The published
`IntegerValuation.IsOmegaCompatible.eq_of_isMaximalSplitTorus` then identifies
the supplied and constructed apartment classes. Rewriting this equality
transfers boundedness at every point and every relative root to the supplied
filtration.

`UnramifiedZeroRootFiltrationBoundedReductionStatement` packages the implication
from the two structural inputs to the exact current unramified target, at
arbitrary universe `u`. The theorem
`unramifiedZeroRootFiltrationBounded_of_henselianDiscrete_of_boundedApartment`
proves that implication. It uses
`unramifiedQuasiSplit_of_henselianDiscrete` for quasi-splitness of the supplied
connected reductive group. The field remains `inertiaFixedField F`. The
surjectivity and henselianity of its normalized integer valuation are the
published `MaximalUnramified.valuation_surjective` and
`MaximalUnramified.valuationSubring_isHenselian`. Its compatibility with the
target's prescribed relation
`ValuativeRel.ofValuation (fixedFieldValued F).v` follows from
`MaximalUnramified.valuation_isEquiv`. The preceding helper then applies to the
same supplied datum, apartment point and root.

All mathematical steps in this file are internal consequences of the named
interfaces and published uniqueness and unramified-valuation results.
No target or imported statement is changed.
