# Dynamic subgroup transport under actual pinned isomorphisms

This internal construction starts from a supplied complete
`f : SplitPinning.Iso p q` between affine group schemes over an arbitrary field
`k : Type u`. It constructs actual isomorphisms between the negative dynamic
parabolics of the two supplied pinnings, and between their positive dynamic
unipotent subgroups. Both isomorphisms commute with the corresponding inclusions
and the actual ambient group isomorphism `f.groupIso`.

The definitions are `SplitPinning.Iso.negativeBorelIso` and
`SplitPinning.Iso.positiveUnipotentIso`. The name `negativeBorel` is inherited from
`SplitBorelCell`; the assertion made here is that it represents the negative
dynamic parabolic. This module does not establish its geometric Borel property.

The construction and its specifications proceed as follows.

1. `height_eq` transports an integral expansion of a root in the simple roots
   through the full character-lattice map of `f`. Reindexing the sum using the
   simple-support bijection identifies its height with the target root's height.
   Consequently `isPos_iff` preserves positive roots.
2. `cocharacter_comp` expresses the inclusion square on actual cocharacters as
   equality of group-scheme morphisms. The two
   `positiveCocharacter_*_iff` lemmas use pairing invariance and `height_eq` to
   compare the signs of the root pairings with the transported cocharacter and
   the chosen target cocharacter. Each chosen scale is strictly positive. The
   chosen cocharacters and their scales are not asserted to be equal; the full
   character and cocharacter lattices, including central directions, are kept.
3. `unipotent_positiveGm_comp` and
   `parabolic_opposite_positiveGm_comp` apply the published
   `relativeRootSignInclusions` proof to those sign comparisons. The reverse
   cocharacter has negated pairings. These are equalities of subgroup functors,
   so they hold on every relative scheme test, including non-affine tests.
4. The `isRepresentedBy_*_comp` lemmas transport the published representing
   inclusions through the ambient group isomorphism. The dynamic functoriality
   equalities identify the resulting comaps with the target dynamic subgroups.
   Uniqueness of representing objects then gives the two actual isomorphisms.
   Their `*_hom_comp` lemmas state the inclusion squares.
5. The two `range_*_comp` lemmas use those squares and invariance of a range under
   source isomorphism. The two `range_baseChange_*_comp` lemmas apply the actual
   pullback functor to the same squares, giving equality of subgroup ranges on
   all relative scheme tests after every morphism
   `b : S ⟶ Spec k`, for any scheme `S : Scheme.{u}`.

The provenance is internal. The module derives its constructions from the
published `PinnedIsomorphismFunctoriality`, `SplitBorelCell`,
`RelativeRootSignInclusionsProof` and `RelativeTitsNondegeneracy` APIs, together
with dynamic isomorphism transport and uniqueness of represented subgroups. It
introduces no new structural existence assumption beyond the supplied complete
pinnings and their isomorphism.

This is a supporting transport construction. It does not construct a pinning,
an initial semilinear descent datum or a coefficient-algebra automorphism
section. It does not establish unconditional quasi-split inner-form existence.
