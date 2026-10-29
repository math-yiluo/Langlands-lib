# Strong irreducible heads from a positive total count

Authors: Worker 166, with Worker 429's proposed boundary and the published
multiplicity-one interface of Workers 495 and 502. This is a derived internal
algebraic statement, extending `Classification.multiplicityOneHeadCore` from
`MultiplicityOneConstituentProof`. No external source theorem is asserted.

`Langlands.Classification.PositiveTotalHeadCriterionStatement` concerns an
arbitrary group `G` with a topology, an arbitrary monoid `H`, and an additive
functor from smooth complex `G` representations to complex `H`
representations. The functor preserves epimorphisms. The group, monoid,
source-carrier, functor-image-carrier and test-carrier universes are
independent.

For a smooth representation `A`, a test representation `τ` and a natural
number `m`, the hypotheses are:

- `0 < m` and the existing actual relation
  `HasJordanHolderMultiplicity (F.obj A) τ m`;
- existence of a smooth irreducible `P` and an actual surjective morphism
  from `A` to `P`;
- for every smooth irreducible `P` and every actual surjective morphism
  from `A` to `P`, an actual count `c` with
  `HasJordanHolderMultiplicity (F.obj P) τ c` and `m ≤ c`.

Every count relation retains an actual finite simple-series witness. The
conclusion is the existing `HasIrreducibleHead A.representation`: an
irreducible quotient exists and all actual irreducible quotient maps to
carriers in the source universe have the same kernel. Quotient targets may
be isomorphic or identical; their isomorphism classes do not replace their
actual kernels. An algebraic quotient of a smooth representation inherits
smoothness by surjective smoothness transfer, so the quantified smooth
quotient premise can control every quotient in this conclusion.

The derivation rationale extends the published multiplicity-one product
argument. Two irreducible quotient maps with unequal kernels give a
surjection onto their actual binary product by
`unequalIrreducibleQuotientKernels`. Coordinate stabilizers show that this
product is smooth. An additive functor maps its inclusions and projections
to morphisms with the same identity and zero composites, producing a
surjection from the functor image of that product onto the product of the
two quotient images. Epimorphism preservation therefore supplies a
surjection from `F(A)` onto this latter product. The actual quotient-image
counts add by `jordanHolderProductAdditivity`; each is at least `m`.
`jordanHolderSurjectiveMonotonicity` bounds their sum by the total count
`m`, forcing `m + m ≤ m`, contrary to `0 < m`. Thus the quotient kernels
coincide.

No irreducibility of `τ`, finite dimension, admissibility, topological-group
instance or preservation of monomorphisms is required. The statement
retains quotient existence and all actual count witnesses as explicit
hypotheses. It supplies a categorical implication; it asserts no Jacquet
comparison, count existence, induction finite length or outer-induction
head theorem.
