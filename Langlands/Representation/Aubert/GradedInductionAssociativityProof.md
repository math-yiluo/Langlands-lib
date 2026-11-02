# Associativity of actual graded normalized induction

This internal proof derives associativity of the published multiplication
`gradedMultiplication F T hx` on the actual graded exact Grothendieck group
`GradedGrothendieckGroup F T`. The final theorem is
`gradedMultiplication_assoc`: for every supplied
`BinaryProductExactnessStatement F T` witness `hx`, with independent field and
carrier universes `uF` and `uV`,

`∀ x y z, m (m x y) z = m x (m y z)` where `m = gradedMultiplication F T hx`.

It is the first clause of `GradedInductionRingLawsStatement`. The unit clauses
are the imported `gradedMultiplication_unit_left` and
`gradedMultiplication_unit_right` of `GradedInductionUnitProof`;
commutativity is proved separately in `GradedInductionCommutativityProof`.
Nothing here concerns commutativity.

## Provenance

The mathematical source is Zelevinsky, *Induced representations of reductive
p-adic groups II* (Ann. Sci. ENS 13, 1980), §1.7, Proposition, part (a):
the product on `⊕ R(G_n)` is associative because both bracketings of
`ρ₁ × ρ₂ × ρ₃` equal the class of the induction from the three-block parabolic,
by transitivity of induction (Bernstein–Zelevinsky I, 1.1(c), and Zelevinsky
1.5). Zelevinsky leaves the rank-zero factor `G_0 = {e}` implicit. Here a
rank-zero factor is reduced to the unit class instead, because every
irreducible representation of the actual group `GL_0` is the unit line.

## Implemented proof

Generic induction principles.

- `span_range_ofObject` shows that classes of actual finite-length objects span
  the exact Grothendieck group: the quotient by their span is killed by
  `hom_ext_object`. `induction_on` is the resulting induction principle over
  zero, sums, integer multiples and object classes.
- `graded_induction` is `DirectSum.induction_on` phrased through the published
  `gradedInclusion`.

Rank zero.

- `gradedUnit_eq` records that `gradedUnit F T` is, by definition, the
  inclusion in rank zero of the class of `T.binaryProductUnit`.
- `nonempty_unit_equiv_of_isIrreducible` shows that every irreducible smooth
  representation `π` of `GL_0` is equivalent to the unit line. Since `GL_0` is
  a subsingleton, the map `c ↦ c • v` for a nonzero vector `v` is an
  intertwining map from the unit line. It is injective because `v ≠ 0`, and it
  is surjective by irreducibility.
- `rankZero_induction` uses the published bijectivity of the irreducible
  realization (`SmoothRep.irreducibleGrothendieckStatement`). Every rank-zero
  class is therefore a `ℤ`-combination of irreducible generators, and each
  generator is the class of the unit object. A property closed under zero, sums
  and integer multiples that holds on the unit class holds on all of exact
  rank-zero K0. This argument uses only full exact classes, so the relations
  from nonsplit short exact sequences are respected.
- `assoc_rankZero_left`, `assoc_rankZero_mid` and `assoc_rankZero_right` prove
  associativity when one factor is homogeneous of rank zero and the other two
  factors are arbitrary graded classes. Each proof applies `rankZero_induction`
  to the rank-zero factor and the bilinearity of `m` to the others. It finishes
  on the unit class with the imported unit laws.

Positive ranks.

- `equivOfEq` turns an equality of smooth representations into an equivalence.
- `binaryPairEquiv` identifies, for positive `a` and `b`, the actual binary
  product `(T.binaryNormalizedProductFunctor a b).obj (A, B)` with
  `T.normalizedProductInduced (Shahidi.twoBlocks a b _ _)
  (Shahidi.pairFamily A.representation B.representation)`. It composes the
  published equality
  `Classification.BinaryProductBridge.binaryNormalizedProductFunctor_obj_eq_twoBlocks`,
  the published `normalizedProductInductionObjEquiv`, and the identity on both
  factors through `normalizedProductInducedEquiv`.
- `binaryAssocEquiv` gives, for positive `a`, `b`, `c` and arbitrary smooth
  `A`, `B`, `C`, an equivalence between `(A × B) × C` and the pullback of
  `A × (B × C)` along the entry-preserving rank reindex
  `finCongr (Nat.add_assoc a b c)`. Both bracketings are first rewritten by
  `binaryPairEquiv`, applied to the outer product and then inside the inner
  factor. The published induction-in-stages equivalence
  `Parabolic.threeBlockAssociativityEquiv`, instantiated with the published
  regrouping theorem `Parabolic.orderedProductRegrouping`, then connects them.
- `assoc_objects_pos` rewrites both sides through the published
  `gradedMultiplication_homogeneous` and `binaryProductK0_classes`. It concludes
  with the imported rank-transport lemma `gradedInclusion_eq_of_rank_equiv`
  applied to `binaryAssocEquiv`.

Assembly.

- `assoc_objects` treats homogeneous classes of arbitrary actual finite-length
  objects in arbitrary ranks. If some rank is zero it applies the matching
  rank-zero lemma, and otherwise `assoc_objects_pos`.
- `gradedMultiplication_assoc` extends this successively in `x`, `y` and `z`.
  It uses `graded_induction` for the direct sum and `induction_on` for each
  exact K0, and handles zero, sums and integer multiples by bilinearity
  (`map_zsmul`, `LinearMap.map_smul₂`). The conclusion therefore holds for every
  virtual class in the full graded exact Grothendieck group.

## Dependency account

The direct imports and their roles are:

- `Langlands.Representation.Aubert.GradedInductionUnitProof`, the companion
  module of this task. It provides the unit laws and
  `gradedInclusion_eq_of_rank_equiv`, and transitively the published
  `Aubert.GradedGrothendieck` construction (`gradedMultiplication`,
  `gradedUnit`, `gradedMultiplication_homogeneous`, `binaryProductK0_classes`,
  `binaryProductUnit_hasFiniteLength`).
- `Langlands.Representation.Parabolic.ThreeBlockRegroupingAssembly` provides
  `threeBlockAssociativityEquiv`, `normalizedProductInductionObjEquiv` and the
  equivalence combinators `equivTrans`, `equivSymm` and `equivPrecomp`.
- `Langlands.Representation.Parabolic.OrderedProductRegroupingProof` provides
  `orderedProductRegrouping`.
- `Langlands.Representation.Classification.TwoSupercuspidalBinaryProductBridge`
  is used only for the equality
  `binaryNormalizedProductFunctor_obj_eq_twoBlocks`. That equality is definitional
  bookkeeping between the binary shape and `Shahidi.twoBlocks`. The import brings
  that module's classification-side closure into the import graph. No
  supercuspidal-product irreducibility result is invoked through this bridge.
  The finite-length preservation already used by the graded construction
  retains the classification-side dependencies described in
  `GradedGrothendieck.md` and `GradedInductionRingLawsProof.md`.
- `Langlands.Representation.Smooth.JordanHolderGrothendieck` provides,
  through `IrreducibleGrothendieckProof` and `IrreducibleRealization`,
  `irreducibleGrothendieckStatement`,
  `realizeIrreducibles_generator_irreducibleIsoClass` and
  `hasFiniteLength_of_isIrreducible`.

The checked axioms of `gradedMultiplication_assoc` are `propext`,
`Classical.choice` and `Quot.sound`. Its level parameters are `uF` and `uV`.

This is a derived consequence of existing Library constructions and proofs.
It introduces no new representation-theoretic hypotheses, and it claims no
polynomial presentation or Aubert comparison. The half-modulus
normalized-induction conventions, supplied field topology and saturated
carrier universe `max uF uV` are those of the imported construction.
