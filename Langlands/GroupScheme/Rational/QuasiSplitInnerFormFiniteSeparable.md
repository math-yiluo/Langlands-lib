# Finite Galois refinement of a finite-separable inner-form presentation

This internal constructor uses the existing actual `QuasiSplitInnerForm`
definition without modifying it or the existence statement. All fields
and schemes lie in arbitrary universe `u`.

`QuasiSplitInnerForm.coverRefinement f`, for a `K`-algebra embedding
`f : L →ₐ[K] M`, is the actual morphism `Spec M → Spec L` over
`Spec K`. Its underlying scheme map is `Spec f`. The algebra-map
identity of `f` proves the required triangle over `Spec K`.
`coverRefinement_fpqc` equips `M` with the `L`-algebra structure induced
by `f` and applies the published faithful-flatness and quasi-compactness
result for field extensions. This construction needs no finiteness or
separability assumption.

`QuasiSplitInnerForm.ofFiniteSeparable` starts with a finite separable
extension `L/K` and a supplied presentation consisting of a quasi-split
model over `K`, its actual full-centre adjoint quotient, quasi-splitness
of that adjoint, natural local multiplicative equivalences to `G` on
`Spec L`, and an actual adjoint-valued natural cocycle satisfying the
discrepancy equation. It returns an actual `QuasiSplitInnerForm G`.

The implemented construction takes the normal closure
`N = IntermediateField.normalClosure K L (SeparableClosure K)`.
Mathlib supplies its finite-dimensional and Galois properties. The
normal-closure embedding equivalence factors a chosen embedding of `L`
into the separable closure through `N`, yielding `f : L →ₐ[K] N`.
The separable closure and its intermediate field both have universe
`u`, so the output carrier has exactly the required universe.

The new local isomorphisms are `e.refine (coverRefinement f)` and the
new cocycle is `ξ.refine (coverRefinement f)`. The discrepancy theorem
from `LocalGroupIsoRefinement` proves the required equation on every
relative test scheme. Its universal-overlap formula identifies the
refined overlap morphism with pullback along the product refinement.
The model, quotient, quotient property, adjoint, quasi-splitness proofs,
and inner action are the supplied ones.

The provenance is internal: the field construction uses existing
Mathlib normal-closure and separable-closure APIs; the remaining steps
are precomposition and the published refinement laws. No external
structural theorem is cited or assumed here. This is a conditional
assembly constructor. It does not construct the initial model,
adjoint quotient, finite-separable local isomorphisms, or discrepancy
cocycle, and does not prove `QuasiSplitInnerFormExistenceStatement`.
Those remain obligations of the host existence proof.
