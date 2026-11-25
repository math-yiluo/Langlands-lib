# Centre comparison for relative central quotients

`Langlands.GroupScheme.RelativeCentralQuotientCenterReductionStatement.{u}` is the named `Prop`-valued statement recording
the centre-preimage equality conditional on the normal multiplicative-type centrality theorem, reductive source and target, and a closed central multiplicative-type kernel.
`Langlands.GroupScheme.relativeCentralQuotientCenterReduction` proves this proposition by the existing helper theorem.
The helper signatures and all mathematical hypotheses are retained; the
other results below are proved companion helpers.

This internal module supplies two all-test subgroup-functor comparisons used in
the centre clause of `RelativeCentralQuotientStatement`. It is derived from
the published definitions, relative-centre theorem, and actual subgroup
pullback construction.

`center_le_comap_of_flat_surjective_hom` proves that a flat surjective
homomorphism carries the centre into the target centre, over every scheme.
For an arbitrary target point, the proof pulls back the homomorphism to
obtain a flat surjective test cover on which that point lifts. Centrality
in the source gives commutation with this lift. Applying the homomorphism
and cancelling the cover proves commutation on the original test scheme.
No reductivity, kernel-centrality, or finite-presentation hypothesis is
needed for this direction.

`RelativeRoot.IsFppfQuotient.center_comap_eq_of_multiplicativeTypeNormalCentral`
assumes the full `MultiplicativeTypeNormalCentralStatement` explicitly. It
also assumes a reductive source and target, a closed central subgroup of
multiplicative type, and a supplied fppf quotient by its range. It proves
that the preimage of the full target centre is the full source centre.
The relative-centre theorem represents the target centre by a closed group
of multiplicative type. The actual group-scheme pullback represents its
preimage. The assumed normal multiplicative-type theorem makes this
preimage central in the source. The opposite containment is the first
lemma. Normality of the given central subgroup is checked pointwise, and
connected residue fibres follow from source reductivity.

The second result is a conditional assembly step for Conrad's
Corollary 3.3.5: it does not prove the assumed normal multiplicative-type
theorem, establish target reductivity, or show that an arbitrary flat
central closed kernel is of multiplicative type. Those are not proved
here. The full relative central quotient target is not proved by this
module.
