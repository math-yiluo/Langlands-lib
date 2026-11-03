# Assembly of an actual rank-one Jacquet pattern

Worker 64. This is an internal conditional construction for the actual normalized
functors. The index, ambient group and carrier parameters `uI`, `uG` and `uV` are
independent. Representation carriers have universe `max uG uV`. The assembly
uses a finite index type; the empty type is allowed. The elementary cuspidality
and zero-propagation comparisons do not require finiteness of the index type.

`rankOneJacquetConstituentsOfExactData` chooses a pair of actual finite-length
representations with `HasTwoConstituents` and the exact
`RankOneJacquetPattern` of
[`GeneralCorollaryTargets`](../GeneralCorollaryTargets.md).
Its input includes all the representation-theoretic data needed for that
conclusion:

- an actual length-two sequence with finite-length irreducible constituents
  `A` and `B`, in either orientation;
- nonzero actual normalized Jacquet modules of both `A` and `B` at `J`;
- an actual short exact sequence with middle `r_J(i_J σ)`, subobject
  `Ad(n⁻¹)σ`, and quotient `σ`;
- zero actual middle Jacquet modules `r_K(i_J σ)` at every proper `K ≠ J`;
- a limit-of-compact-subgroups hypothesis on every `U K`, supplying exactness
  of the actual normalized Jacquet functors;
- irreducibility of `σ` and the literal self-normalization witness `hself`.

The given `n` belongs to the normalizer of the given subgroup `T`. The construction
does not require a longest-representative hypothesis: it works for any supplied
`n` for which the displayed geometric sequence and self-normalization witness
exist. It retains that exact `n` and witness in its conclusion. The conjugation
functor is literally `conjugationFunctor (n : G)⁻¹`, with action
`x ↦ σ(n*x*n⁻¹)`.

## Implemented argument

`HasRankOneJacquetMiddleSequence` is a Prop-valued definition of the supplied
actual short exact sequence
`Ad(n⁻¹)σ → r_J(i_J σ) → σ`. It asserts existence of the two actual intertwining
maps and their injectivity, surjectivity and range/kernel exactness. It imposes
no maximality or longest-representative condition and supplies no proof that
the sequence exists. Naming this input also keeps its elaboration shared
between the existence theorem and the constructor.

`HasTwoConstituents.symm` swaps the two labels, using the disjunction of sequence
orientations in that predicate.

`isCorollaryLeviCuspidal_iff_isLeviCuspidal` identifies the corollary's categorical
zero condition with the support-category condition that the same actual
inside-Levi Jacquet carriers are subsingletons. It uses
`SmoothRep.isZero_iff_subsingleton_carrier` from the
[object deduction module](../../Smooth/LengthTwoEndpoints.md); it supplies no
admissibility or support theorem.

`HasTwoConstituents.jacquet_isZero` applies the published
`jacquetFunctor_map_isShortExact` to the given actual maps. The object deduction
lemma `SmoothRep.isZero_endpoints_of_shortExact` then propagates zero of the
middle to both endpoints. The proof explicitly handles both sequence
orientations.

`exists_rankOneJacquetPattern_of_exact_data` first derives irreducibility of
`Ad(n⁻¹)σ` by the published
`Langlands.isIrreducible_comp_continuousMulEquiv_iff`, applied to the actual
conjugation equivalence. It applies exact normalized Jacquet restriction to the
supplied constituent sequence at `J`. The supplied geometric sequence has the
same middle object and two irreducible endpoints. The object deduction lemma
`SmoothRep.endpoints_iso_of_shortExact_two_irreducibles` gives actual isomorphisms
of the nonzero Jacquet endpoints with these two objects, in one of the two
orders. Swapping the original constituents when necessary realizes the ordered
pattern. The previous zero-propagation lemma supplies the other proper Jacquet
vanishings. The final definition chooses the pair using this existence result
and a private, generic choice of a pair satisfying a binary predicate.

No splitting or distinctness of the two simple objects is used. There is no
global finite-length-preservation assumption: the constituents' finite length
is supplied, and the generic object deduction derives the finite lengths
needed to compare the two Jacquet sequences.

## Dependencies and scope

The actual local exactness input is
`Langlands.Aubert.General.jacquetFunctor_map_isShortExact` in
[`AlternatingOperator`](AlternatingOperator.md), using
`Langlands.Jacquet.Localization.characterLocalizationExactness` at the trivial
character. The irreducibility transport declaration is in
[`CompactCoefficient.GroupTransport`](../../CompactCoefficient/GroupTransport.md);
it uses the elementary order isomorphism of invariant subspaces under a
surjective group homomorphism, rather than a support or classification theorem.
The composition-factor and zero-object deductions are exactly those documented
in the object deduction pair. `SupportCategory` is imported for the cuspidality
predicate and its comparison.

This conditional construction supplies neither the geometric sequence nor
nonvanishing, a length-two constituent sequence, the unipotent structural
hypothesis, or the other-proper middle vanishings. It invokes no adjointness,
cuspidal-support theorem, character independence or Langlands classification.
Importing modules containing definitions or other results is not an invocation
of those results. In particular this construction does not prove
`RationalRankOneJacquetModulesStatement`: its explicit local data still need
proofs at the actual rational-point scope.
