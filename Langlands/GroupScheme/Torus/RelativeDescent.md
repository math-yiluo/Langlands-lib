# Étale descent of relative tori and transport of fibrewise maximality

Author: Worker 693.

This internal helper module supports the arbitrary-base quasi-split inner-form
construction. It derives its results from the published relative-torus predicate,
maximality on field-valued points, field-extension reflection, and the canonical
comparison isomorphisms for iterated pullback.

`RelativeTorus.IsTorus.descendedSplittingCover` constructs an étale cover of the
original base by composing a chosen splitting cover upstairs with the given
étale surjection. The theorem `descendedSplittingCover_splits` proves that each
member splits the original group using the iterated-pullback comparison.

`RelativeTorus.IsTorus.of_baseChange_of_etale` reflects the relative-torus property
along an étale surjective morphism, without a quasi-compactness assumption. Its
proof composes the splitting cover upstairs with that morphism. The converse is
the published arbitrary-base-change theorem.

`IsFibrewiseMaximalTorus.comp_iso` and `iso_comp` transport residue-fibre
maximality along actual ambient and source isomorphisms.

`IsFibrewiseMaximalTorus.baseChange` works for every base change when the ambient
group is smooth and affine. A residue-field point upstairs composes to a
field-valued point downstairs, where the published `fieldPoint` theorem applies.
The canonical iterated-pullback comparisons identify the actual torus maps.

`IsFibrewiseMaximalTorus.of_baseChange` reflects maximality along any surjective
scheme morphism for a supplied closed inclusion, without smoothness or
affineness assumptions on the ambient group. For each base point choose a
preimage; the residue-field extension and its
canonical factorization identify the upstairs fibre with an extension of the
downstairs fibre. Field-extension reflection gives the conclusion.

These results construct neither a torus nor a Borel subgroup. In particular they
do not prove quasi-split inner-form existence. Their provenance is an internal
deduction from existing Library results, rather than a new transcription of a
literature statement.

Shared declarations `IsFibrewiseMaximalTorus.comp_iso`, `IsFibrewiseMaximalTorus.iso_comp`, `IsFibrewiseMaximalTorus.baseChange` are imported from `Langlands.GroupScheme.Torus.FibrewiseMaximalTransport`; their mathematical hypotheses, conclusions and data are unchanged.
