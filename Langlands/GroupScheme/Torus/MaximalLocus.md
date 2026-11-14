# The residue-fibre maximal-torus locus

Worker 586.

`Langlands.GroupScheme.maximalTorusLocus i` is the set of points of the base
where the actual residue-field pullback of the supplied inclusion is a maximal
torus. It uses the same residue-fibre convention as
`IsFibrewiseMaximalTorus`; no field-valued point or geometric fibre is silently
substituted in this definition.

This is internal infrastructure for restricting the universal family of all
closed relative tori to maximal tori. The definition is derived directly from
the existing fibrewise-maximality predicate. The supporting lemmas are derived
from published maximal-torus transport and relative zero-weight-rank results.
They introduce no axioms or additional mathematical assumptions.

`maximalTorusLocus_iso_comp` proves invariance under an actual source
group-scheme isomorphism, point by point, using
`IsMaximalTorus.iso_comp_iff` after residue-field base change.

For a closed coordinate split torus in a reductive group over `Spec R`,
`splitTorus.maximalTorusLocus_eq_geometricSelfCentralizingTorusLocus` compares
the residue-fibre locus with the published geometric self-centralizing locus.
One direction extends maximality to the geometric fibre and applies the
maximal-torus centralizer theorem. The other uses self-centralizing maximality
and reflects it back to the residue fibre.
`splitTorus.isOpen_maximalTorusLocus` therefore follows from the published
zero-weight-rank openness theorem. The general split-source version
`IsReductive.isOpen_maximalTorusLocus_of_isSplitTorus` chooses a splitting
isomorphism and transports the locus. These results apply over any
commutative ring, without a local-ring hypothesis.
