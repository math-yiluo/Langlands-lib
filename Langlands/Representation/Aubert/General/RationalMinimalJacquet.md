# A nonzero cuspidal Jacquet module on actual rational points

Worker 78 extracted the minimal-index argument written by Worker 379 in the
published `RationalCuspidalEmbeddingProof`, and discharged its compact-limit
input using the published `RationalUnipotentRegularity` theorem. This is an
internal construction for the Jacquet-detection task. It preserves the actual
rational-point group, canonical evaluation topology, standard families and
normalized Jacquet functors.

`exists_nontrivial_isLeviCuspidal_jacquet` proves that every nontrivial smooth
complex representation has a standard index `I` with nontrivial normalized
Jacquet module `r_I π`, and with that same module satisfying `IsLeviCuspidal`
inside `M_I`. `nonzeroCuspidalJacquetIndex` chooses such an index as a subtype
whose property contains both conclusions. The universes `u` and `v` are
independent; carriers have universe `max (u + 1) v`.

The inputs are a nonarchimedean local field, a connected reductive group scheme,
a maximal split torus, a generic cocharacter, `hStandard`, `hInter`, `hRoots`,
closed standard radicals and Levis, and local compactness and the
nonarchimedean-group property at `pointTopology`. The API exposes the affine
and monomorphism instances used to form the standard families; in the support
target these are `hG.isAffineHom` and `hi.isSplitSubtorus.mono`. Nontriviality of
`π` suffices; irreducibility is not needed for this construction.

The implemented proof follows the first part of the published embedding proof.
The full radical is trivial by `unipotent_univ_eq_bot`, so its relation span is
zero and a nonzero vector remains nonzero in the full-index Jacquet module.
Choose an index of minimal finite cardinality with nontrivial Jacquet module.
Every proper inside-Levi label `K` has `card (leviIndex I K) < card I`, hence
the corresponding ambient Jacquet module is a subsingleton.

For cuspidality, apply
`CuspidalEmbedding.mem_relations_of_subsingleton` and
`CuspidalEmbedding.subsingleton_jacquet_of_forall_mem_relations`. The radical
product comes from `unipotent_product_of_subset`, using `hInter`. The inclusion
of the finer radical in the normalizer of the coarser radical comes from
`unipotent_le_parabolic_of_subset` and `(h I).le_normalizer`.
`standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`
derives compact containment for that finer ambient radical from `hStandard`.
Then `CuspidalEmbedding.closedNormalizerCharacter_eq_one_of_compactLimit` and
`Jacquet.inverseHalfCharacter_eq_one` show that the outer inverse-half modulus
is trivial on the part inside `M_I`. Vanishing of the finer ambient Jacquet
module therefore implies vanishing of the inner Jacquet module. Closedness of
`M_I` supplies its local compactness. This is exactly the proper-standard-test
predicate `IsLeviCuspidal`.

This helper has no endpoint, quotient-compactness, compact-limit, exactness,
finite-length, admissibility or finite-generation premise. It does not extract
an irreducible quotient or an embedding into an induction. It also does not
compare the chosen Levi to a support datum or prove the assigned detection
target. No classification, character-independence or actual geometric-filtration
result enters the proof body. Its direct imported proof helpers are from
`RationalCuspidalEmbeddingProof`; their declarations above are the precise
reused proof material, not an application of its stronger embedding conclusion.

The route is the minimal-Jacquet portion of the embedding argument already
explained in `RationalCuspidalEmbeddingProof.md`. This module makes no additional
translation of an original-literature assertion. Worker 379 is a coauthor for
the reused proof material.
