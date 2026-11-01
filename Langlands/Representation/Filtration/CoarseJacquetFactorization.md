# Admissible coarse Jacquet constituents and tensor factorization

Author: Worker 19.

This internal adapter strengthens the actual constituent extraction in
`CoarseJacquetExtraction`. It retains every coarse block and the existing
`SmoothRep.IsSubquotient` relation. It does not prove either repeated-factor
rank-three transfer.

For any supplied p-adic topology `T`, finite-length admissible smooth ambient
representation `π`, arbitrary coarse block shape `B`, and refinement `S`, an
irreducible actual subquotient `D` of the composed normalized Jacquet module
comes from an admissible finite-length irreducible actual coarse constituent.
When the total rank is positive, that constituent can be replaced by an
isomorphic actual external tensor of admissible irreducible finite-length
block representations. The tensor itself remains an actual subquotient of
the whole coarse Jacquet module, and `D` remains an actual subquotient of
its refined normalized Jacquet module.

The field universe `uF` and carrier universe `uV` are independent. Every
factor has carrier in `Type uV`. The ambient representation need not be
irreducible, and no condition is imposed on outside factors.

## Implemented argument

`SmoothRep.isAdmissible_of_subquotient_of_compactOpenCofinal` takes an
actual injective/surjective presentation `X → A`, `X → D`. Injective
admissibility transfer makes `X` admissible. Apply
`isAdmissible_iff_of_shortExact` to the actual kernel inclusion of the
second map and to the map itself. Exactness is the range identity for a
submodule inclusion. Compact open averaging and cofinality in that
published short-exact-sequence theorem give admissibility of `D`.

The private `levi_compactOpen_cofinal` chooses a compact open subgroup
inside any given open subgroup using `T.leviCompactOpen` and its identity
neighborhood. It uses the supplied topology. The private
`finiteLength_of_irreducible` identifies irreducibility with simplicity
over the group algebra; a simple module is Noetherian and Artinian. This
is the elementary argument also used in
`SmoothRep.hasFiniteLength_of_isIrreducible`, reproduced privately to
avoid importing Grothendieck group constructions.

`exists_admissible_irreducible_coarseJacquet_subquotient` applies the
previous extraction theorem to obtain `E` and both actual occurrences.
The coarse Jacquet module is admissible by
`FiniteLengthAssembly.isAdmissible_normalizedJacquet`. The generic transfer above
makes `E` admissible, and simplicity makes it finite length.

`exists_factorized_coarseJacquet_subquotient` applies
`CuspidalSupport.padicLeviAdmissibleFactorization` to `E`. Its positive
rank hypothesis guarantees a nonempty finite block list. The resulting
equivariant linear equivalence gives an actual smooth isomorphism
`E ≅ FiniteTensor.externalSmoothObject A` using `SmoothRep.mkIso`.
Transport the coarse occurrence along this isomorphism on its constituent
side, and the refined occurrence along the functor's mapped isomorphism
on its ambient side. Each block factor has finite length by simplicity.
No full Jacquet quotient or parabolic induction embedding is introduced.

`IsCoarseJacquetFactorization` packages the conclusion as a proposition
about the block family `A`: its factors are irreducible, admissible and
finite length; its actual external tensor is an actual coarse Jacquet
subquotient; and `D` is an actual subquotient of that tensor's refined
Jacquet module. The definition is just this conjunction and does not
introduce a new occurrence relation.

## Provenance and dependencies

The new statements are internal consequences of the published actual
Jacquet, admissibility, finite-length, and finite tensor APIs. The finite
tensor factorization is the finite iteration of the Library's proved
two-factor existence theorem, whose proof uses compact averaging, a
minimal jointly fixed orbit-span dimension, scalar Schur's lemma,
Jacobson density, and evaluation on a multiplicity space. It does not
use global supercuspidal support decomposition or multisegment
classification. The coarse extraction dependency audit is recorded in
`CoarseJacquetExtraction.md`.

The four direct imports are `Filtration.CoarseJacquetExtraction`,
`CuspidalSupport.LeviAdmissibleFactorizationProof`,
`Smooth.Admissibility.ExactProof`, and `Group.GL.CompactOpen`.
Recursive traversal at the workspace's Library base gives 323 project
modules including this module, 22 more than the coarse extraction closure.
The classification namespace imports remain exactly
`ConstituentRelations`, `FiniteLengthProof`, `FiniteLengthStatement`,
`Segments`, `Supercuspidal`, `SupercuspidalContragredientAux`,
`SupercuspidalContragredientStatement`, `SupercuspidalSupport`, and
`SupercuspidalTwist`. Their lower definitions and proofs have the uses
described in `CoarseJacquetExtraction.md`; no classification conclusion
is invoked here.

The new proof route was checked at declaration level:

- `isAdmissible_iff_of_shortExact` obtains quotient admissibility by
  averaging a preimage over compact open subgroups
  (`Compact.fixedVectorSurjectivity`) and then using cofinality. Its
  injection and middle-exactness steps are elementary linear algebra.
- `padicLeviAdmissibleFactorization` is induction on the positive number
  of blocks, using continuous one-block and head/tail group equivalences,
  actual representation pullback, tensor equivalences, and
  `admissibleProductFactorization`.
- Its use of `AssociationReduction` is the elementary
  `length_pos_of_pos`: an empty block index set would make the sum of
  block ranks zero. The association and Weyl modules imported there
  supply no classification result to this proof.
- The two-factor existence proof makes a first-factor orbit span
  irreducible by minimizing a finite fixed-space dimension. Compact
  averaging and ambient irreducibility force every nonzero restricted
  subrepresentation to meet that fixed space. The first factor is
  admissible by embedding its fixed vectors in ambient product fixed
  vectors. Scalar Schur follows from an eigenvector in a nonzero finite
  fixed space. Jacobson density separates the coefficients of a tensor
  in the evaluation kernel. The multiplicity factor is admissible by
  injective evaluation and irreducible by the now bijective tensor
  evaluation. These are actual module constructions, without an
  existence or uniqueness theorem for supercuspidal support.

Thus the dependency route retains the exclusion of the eight
classification tasks named in the host contract, their conclusions and
proof successors. Neither global support decomposition, general ordered
quotient coverage, nor full multisegment classification is used. Lean
compilation and inspection of the closing existence theorem succeed with
independent `uF,uV` and only `propext`, `Classical.choice`, and `Quot.sound`.
