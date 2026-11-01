# Actual smooth subquotients of finite external tensors

Author: Worker 19.

This internal algebraic adapter relates the existing actual smooth-subquotient
relation to the existing representation-level actual-subquotient relation. It
then transports occurrences through group equivalences and extracts or
reassembles factors of a finite external tensor. It supplies no local
rank-three representation structure or final Jacquet transfer.

The smooth relation writes the constituent first, whereas
`WeylBranchPieces.IsSubquotient` writes the ambient representation first.
`SmoothRep.isSubquotient_iff_representation` proves that these two relations
agree on actual smooth objects in the same carrier universe. In one direction,
the actual quotient projection is followed by the inverse of the given
isomorphism to give a surjection from an actual invariant subspace. In the
other, `SmoothRep.subquotientPresentationIso` constructs the actual smooth
isomorphism from the invariant subspace modulo the surjection's kernel onto
the constituent. Its linear equivalence is the quotient-by-kernel equivalence;
equivariance follows by checking representatives. Smoothness of the actual
subspace and quotient comes from the existing injective and surjective
smoothness transfer theorems.

`SmoothRep.IsSubquotient.pullback` uses the already defined smooth pullback
along a topological group equivalence and the representation-level restriction
lemma. `SmoothRep.isSubquotient_pullback_iff` reflects occurrence by pulling
back along the inverse and cancelling the two group maps. Groups have
independent universe parameters; the two smooth carriers share `uV`.

`FiniteTensor.piTensorMap_injective` chooses a complex linear retraction of
each injective factor map. Tensoring those retractions gives a left inverse
of the tensor map. `piTensorMap_surjective` chooses linear sections and uses
the corresponding right inverse. These linear statements permit independent
index, source-carrier and target-carrier universes.

For a small finite index type, `FiniteTensor.isSubquotient_external` chooses
the actual injective/surjective span presenting each factor occurrence and
tensors the spans. The two tensor maps retain injectivity and surjectivity by
the preceding linear lemmas. All original factors occur in this construction.
There is no condition on their cuspidal support, dimension, admissibility or
length.

`FiniteTensor.isSubquotient_smooth_factor_of_external` converts a smooth tensor
occurrence to the representation relation, applies the existing
`isSubquotient_factor_of_external`, and converts back. Irreducibility is
required for each constituent factor, with no corresponding requirement
on the ambient factors.

The provenance is internal: actual subspaces, quotient maps, inverse group
maps and linear splittings prove the stated results. The external factor
extraction used here contracts a trivially acted complementary tensor factor
after restricting to one coordinate; its finite-dimensional minimality
argument is independent of representation classification.

## Dependency audit

The three direct imports are `Classification.SupercuspidalSupport`,
`CompactCoefficient.GroupTransport`, and `Tensor.ExternalSubquotient`.
Recursive traversal at the pinned Library base gives 147 project modules,
including this one. The classification namespace modules are exactly
`CanonicalConstituents`, `ConstituentRelations`,
`CuspidalJacquetMultiplicityStatement`, `Essential`,
`RelativeGenericityStatement`, `RelativeJacquetMultiplicityStatement`,
`RelativeRegularComparisonStatement`, `Segments`, `Supercuspidal`,
`SupercuspidalSupport`, `SupercuspidalTwist`, `Tempered`,
`TemperedInductionStatement`, and `TemperedSupportStatement`.

The proof route was checked in the actual bodies used here:

- The actual presentation isomorphism uses only the linear quotient-by-kernel
  equivalence, the defining equivariance of the supplied surjection, and
  `SmoothRep.mkIso`. The smooth quotient and subrepresentation constructions
  inherit smoothness along their actual surjection and injection.
- `hom_hom_surjective` follows by applying the inverse-isomorphism identity
  to a vector. The existing smooth injective/surjective presentation criterion
  used when tensoring spans is proved by range restriction, kernels and the
  same quotient-by-kernel equivalence.
- The existing `SmoothRep.pullback` retains the carrier and precomposes its
  action. Its smoothness proof takes the inverse image of an open stabilizer.
  The representation-level `IsSubquotient.comp` retains the invariant subspace
  and surjection and restricts their action. Reflection uses only the inverse
  group identity.
- The indexed tensor map identities are checked on pure tensors. Linear
  retractions and sections are available for arbitrary complex vector spaces
  by basis extension and projectivity; no finite dimension is assumed.
- In `ExternalSubquotient`, restriction to a single coordinate makes the
  complement's action trivial. Splitting off that coordinate uses the actual
  tensor regrouping equivalence. Nonzeroness of the constituent complement
  follows by tensoring vector-space bases. A contraction onto the selected
  factor reduces to an irreducible subquotient of a tensor with trivial
  complement. The proof chooses a finite-dimensional complementary subspace
  of least possible dimension on which the presenting quotient is nonzero.
  Contraction has its kernel inside that quotient's kernel, by minimality.
  Descent to the contraction image and irreducibility of the target give an
  actual surjection from a subrepresentation of the selected ambient factor.

The classification-named statement and definition modules in the import
inventory supply no classification conclusion to these constructions.
The tensor extraction does not use their multiplicity, tempered-support,
induction, head-existence, or exhaustion statements. No geometric-lemma,
Jacquet-finiteness or local cuspidal-product proof is used in this adapter.
Thus its direct and transitive proof route is independent of the eight
excluded classification tasks in the host contract, their conclusions and
proof successors, and uses no global support decomposition, ordered quotient
coverage or full multisegment classification.

Development compilation and inspection of the quotient presentation
isomorphism and the smooth factor-extraction theorem succeed without warnings,
with independent group and carrier universes and only `propext`,
`Classical.choice` and `Quot.sound`. These checks do not supply independent
semantic acceptance or prove either host transfer.
