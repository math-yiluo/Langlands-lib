# Reduction of henselian extension closedness to complete fields

This derived supporting unit reduces the full unchanged
`HenselianExtensionPointEmbeddingStatement` to the published, still unproved
`CompleteExtensionPointClosedRangeStatement`. It does not prove that prerequisite
or assert unconditional completion of Conrad's Proposition 5.11(3).

The construction `ExtensionClosedReduction.towerExtensionPointMap` sends points
of the base change to a middle field to points over a larger field, using the
canonical isomorphism from iterated base change to base change from the original
field. The evaluation lemma identifies it with change of coefficients on points
of the original space. Its continuity follows from the published continuity of
coefficient change and the homeomorphism induced by an isomorphism of spaces.

For separated X and a henselian extension L in which K is closed, complete both
fields. The complete-field prerequisite makes the image of X(Completion K)
closed inside X(Completion L). The tower comparison is a homeomorphism, so this
image remains closed on the original-base carrier. Its inverse image along the
continuous map from X(L) is exactly the extended X(K) locus: the nontrivial
inclusion is `ExtensionCompletionReduction.exists_point_of_completion_eq`, and
the other inclusion is functoriality of coefficient change. This proves the
conditional separated-space closedness lemma. It requires henselianity only of L.

Finally, the published `ExtensionLocalReduction.isEmbedding_of_covered` gives
the full embedding under the separated-open-cover hypothesis. The published
open-subspace localization of closedness reduces the closed-range obligation to
the preceding separated-space result. Combining embedding with closed range
gives exactly the original statement's conditional closed embedding, with no
finite-degree, completeness or extra separation hypothesis added to that target.

All results here are derived from the actual published spectrum-valued point
maps, chart topologies, completion intersection and base change comparisons.
No separate literature assertion or analytification construction is introduced.
