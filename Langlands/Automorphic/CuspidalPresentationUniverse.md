# Independent carrier universes for cuspidal spectral presentations

Author: Worker 1815.

This internal transport construction allows the local factor carriers of an
existing all-place irreducible admissible cuspidal spectral presentation to
lie in any independent universe, including `Type 0`. It does not construct an
initial presentation or prove existence of an irreducible admissible finite
slice. Those are separate inputs to the eventual cuspidal contragredient
presentation proof.

`Global.FiniteAdelicGL.tensorEquiv` applies the published
`RestrictedTensor.congr` to the local linear equivalences and then uses
`RestrictedTensor.map_intertwines` for the actual restricted-product action.
Pullback along `restrictedProductEquiv` gives an equivariant equivalence for
the finite adelic group. The source and target exceptional sets may differ;
the reference vectors must be preserved at all but finitely many places.

`FiniteTensorPresentation.mapFactors` uses the simpler case of an unchanged
exceptional set and transports every reference vector by its local
equivalence. Injectivity preserves nonzeroness, and intertwining preserves
integral fixedness. The inverse tensor equivalence followed by the original
presentation equivalence maps onto exactly the same embedded finite
realization. Thus the tensor equivalence is a constructed bijective
intertwiner, not a new factorization hypothesis.

`exists_small_finiteLocalFactor` applies the published theorem
`Langlands.padicIrreducibleSmoothSmallRealization` with
`CompletionPadic.padicField v` and `CompletionPadic.topologicalData v`.
The latter uses the completion's original topology, so the returned smooth
representation has exactly the topology used by `FiniteLocalGL`. The
theorem requires irreducibility and smoothness; it requires no
countability or resizing witness.

`CuspidalSpectralPresentation.mapFactors` combines these constructions,
retains the same actual nonzero finite slice, and obtains normalized
unramified data from `FiniteTensorPresentation.unramifiedData` using the
transported factors. Its spectral exceptional set is the tensor exceptional
set. It claims no equality between old and new chosen spectral fields.

Finally, `CuspidalSpectralPresentation.exists_small` extracts the factor
irreducibility and admissibility from those of the actual local components
using `localComponent_isIrreducible_iff` and
`localComponent_isAdmissible_iff`. It chooses a small equivalent factor at
each place, transports admissibility by `Langlands.isAdmissible_of_equiv`,
and constructs the new complete presentation. The same two component
comparison theorems give irreducibility and admissibility at every finite
place, including the exceptional places.

All field, source-factor and target-factor universes are independent. This
is derived infrastructure from the named Library theorems and the existing
presentation structures, not a separately attributed literature result.
It changes none of their definitions or hypotheses.
