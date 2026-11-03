# Complete weight spaces under field extension

Author: Worker 1317.

Let `k ⟶ K` be an extension of fields in the original universe `u`. Let `G`
be an affine group scheme locally of finite type over `Spec k`, let `T`
be a commutative group scheme whose underlying group is a split torus,
and let `i : T.toGrp ⟶ G` be any homomorphism. Write `b` for
`algebraBaseMap k K`. Pullback group schemes and their Lie kernels in
this module are the actual scheme pullbacks, and all weight spaces use
the adjoint eigenvector condition over every commutative test algebra.
No reductivity, connectedness, maximality or injectivity assumption is needed.

`rootBaseChangeEquiv hT i` identifies `roots i` with the actual roots of
`(GroupScheme.baseChange b).map i`. Its underlying character is exactly
`characterLattice.baseChange b T χ`, as recorded by
`rootBaseChangeEquiv_val`. The inverse is supplied by the published bijection
on character lattices of split tori, restricted to actual root support using
the root-support comparison in `Torus.RootSupportBaseChange`. The construction
reuses `rootsBaseChangeEquiv` from that module through an abbreviation.

The proof first establishes the complete weight-space comparison:

- `weightSpace_baseChange_eq_iSup` expresses each target weight space as
  the supremum of `extendedWeightSpace i χ` over characters whose pullback
  is the prescribed target character.
- `weightSpace_baseChange_eq_extendedWeightSpace` specializes to a
  pulled-back character. Injectivity of split character-lattice pullback
  reduces its character fiber to a single original character.
- `weightSpace_baseChange_ne_bot_iff` uses the nonvanishing comparison in
  `Torus.WeightBaseChangeSupport` to preserve and reflect nonzero weight spaces.
- The imported `mem_roots_baseChange_iff G T hT i` from
  `Torus.RootSupportBaseChange` preserves and reflects root membership with
  the same hypotheses and actual character pullback.

For the first equality, the shared linear-algebra lemma
`submodule_eq_iSup_of_refinement` from `Torus.WeightRestriction` compares a spanning
family of submodules with an internal direct-sum decomposition when each
member of the family lies in a specified summand. Projection onto a fixed
target summand acts identically on generators in that summand and vanishes
on generators assigned to other summands. Submodule-supremum induction
therefore places that summand inside the supremum of its fiber. The reverse
inclusion follows from the given inclusions.

Here the spanning family is the scalar-extended original weight spaces:
the original split weight decomposition and
`iSup_extendedWeightSpace_eq_top` prove that they span. The target split
weight decomposition is available because splitness, affineness and local
finite type persist under pullback. The refinement inclusion is
`extendedWeightSpace_le`. Thus every use of the shared linear-algebra
lemma has its spanning and internal-decomposition hypotheses discharged.

`roots_negation_baseChange_iff` proves that negation stability of these
actual root sets is equivalent over `k` and `K`. One direction applies
support reflection to the negative original character. The other lifts
every target character using split character-lattice surjectivity, applies
original negation stability and then uses support preservation. Additivity
of character pullback commutes with negation in both directions.

This is an internal derived construction from the actual scalar-extension
spans in `Torus.WeightBaseChangeSupport`, the split weight decomposition in
`Torus.WeightDecomposition`, the projection API in
`Rational.GenericLieWeights`, and the actual split character-lattice
bijection in `Torus.SplitLatticeBaseChange`. The refinement proof
reuses Worker 1317's declaration in `Torus.WeightRestriction`. It attributes
no additional structural result to external literature.

The negation equivalence is a transport result. It supplies neither side
unconditionally. Existence of opposite roots for a reductive group remains
a separate obligation, and this module does not prove
`RelativeRootNegationStatement`.

The local affineness and finite-type instances for the base-changed group
have explicit module-specific names, so the related torus comparison modules
can be imported together without generated-name collisions.
