# Preservation and exact-K0 reduction of actual target induction

This internal construction continues `TargetInductionComparison` and supplies
the target-induction counterpart of `SourceJacquetReduction`. It derives
preservation and identifies an exact K0 map from structural subgroup equalities
and the literal restricted standard induction.

`geometricTargetDecompositionOfEq` takes a standard restricted semidirect
decomposition inside `M I`, equality of the ambient target-intersection Levi
with `M K`, and equality of the restricted target parabolic and radical with
their standard counterparts. Rewriting the three groups proves
`GeometricTargetDecomposition`. This part uses only a group.

The other results use any locally compact nonarchimedean group with closed
ambient Levis and radicals. The indices `I,J,K` and the ambient element `n`
are arbitrary; there is no minimality, normalizer, finite label-type or
nonemptiness assumption. They retain the target decomposition, the standard
restricted decomposition, the inclusion `M K ≤ M I`, and the three exact
subgroup equalities of `geometricTargetInductionComparisonIso`.

`geometricTargetInductionPreservationOfEq` assumes finite-length and short-exact
preservation for the literal `normalizedInductionFunctor` inside `M I` at
`K`, with closedness of its restricted radical obtained by inverse image
under the subgroup inclusion. The private helper substitutes the equality
of ambient fine Levis. It composes standard preservation with pullback along
`subgroupOfContinuousEquiv`, then removes identity conjugation from
`leviNormalizedInductionIsoOfEq` by the natural identity isomorphism and a
left unitor. Preservation transfers along the resulting natural isomorphism.
Thus no preservation premise for the actual target induction is added.

`geometricTargetInductionK0` is the actual target-intersection induction map
on the full exact finite-length Grothendieck group, using these derived
preservation witnesses. `geometricTargetInductionK0OfEq` identifies it with
the literal restricted standard induction map, preceded by pullback from
the ambient fine Levi to its `subgroupOf` and by identity conjugation from
the actual target-intersection Levi to `M K`. The proof applies
`map_eq_of_iso` to the natural target comparison and `map_comp` to its two
compositions. The equality therefore holds on all virtual classes.

The index, group and carrier universes `uI,uG,uV` are independent. Induction
takes carriers in `uV` to carriers in `max uG uV`, with no added saturation
assumption on the input. The standard finite-length premises may be extracted
from the literal Levi-family `ParabolicFiniteLength` hypotheses used by the
final target. All subgroup topologies and Haar normalizations remain those
of the existing actual functors.

The provenance is internal: the construction uses the named target natural
comparison, the existing identity-conjugation and subgroup pullbacks, and
the published transfer and exact K0 lemmas. Its decomposition and map-comparison
pattern is adapted from `SourceJacquetReduction`. No external mathematical
assertion is invoked. The subgroup identities remain inputs; this unit does
not prove those identities, the geometric expansion, normalized stages,
the common-term factorization or the full rational Jacquet compatibility
target.
