# Composition of restrictions of actual descent data

This internal construction derives composition coherence for the actual
restriction constructor of `Descent.Refinement`, using the transition and
pullback-comparison laws of `Descent.Reindex`. All schemes lie in one arbitrary
universe, and the only hypotheses on the morphisms are the stated commuting
squares.

Let `D : Datum p G` for `p : S → B`. Consider two squares given by
`t : V → C`, `q : V → S`, `b : C → B` with `q ≫ p = t ≫ b`, and
`r : W → E`, `v : W → V`, `c : E → C` with `v ≫ t = r ≫ c`.
The helper `reindex_comp_condition` proves
`(v ≫ q) ≫ p = r ≫ (c ≫ b)` by composing the second equality with `b` and
using the first equality and associativity.

`Datum.reindex_comp_compatible` proves that the actual canonical comparison
`v*(q*G) ≅ (v ≫ q)*G` respects the twice-restricted datum
`(D.reindex t q b w₁).reindex r v c w₂` and the directly restricted datum
`D.reindex r (v ≫ q) (c ≫ b) w`. This is compatibility of actual group-scheme
homomorphisms on the cover `r`, with both original cocycles already supplied
by the restriction constructor.

The proof first uses `reindexOverlap_eq` to express the direct overlap with
the explicit endpoints `(fst r ≫ v) ≫ q` and `(snd r ≫ v) ≫ q`. This helper
is the defining overlap formula with endpoint equalities substituted; it does
not assume that chosen pullbacks are strictly associative. On the other side,
`transition_reindex` expands the transition of the first restricted datum.
After cancelling the invertible comparison on the final endpoint,
`pullbackComparison_assoc` identifies the two comparison composites at each
endpoint. The remaining inverse/forward comparisons cancel, giving the required
compatibility equation.

`Datum.collapseReindexSolution` takes a supplied solution of the twice-restricted
datum and composes its comparison with this compatible isomorphism using
`Solution.mapIso`. Its descended object stays the supplied solution's object
over `E`. The resulting solution is for the directly restricted datum on `r`.

These are coherence and supplied-solution transport results. They construct no
solution from an arbitrary original datum and do not establish the quasi-split
inner-form existence statement.
