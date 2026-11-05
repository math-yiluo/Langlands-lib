# A vector factor with a separably wound complement

`Langlands.GroupScheme.RelativeRoot.commutativePTorsionVectorFactor.{u}`
proves exactly the published proposition
`Langlands.GroupScheme.RelativeRoot.CommutativePTorsionVectorFactorStatement.{u}`.
The statement is imported from `CommutativePTorsionVectorFactorStatement` and
is not modified. It is the vector-factor existence assertion of CGP B.2.5.

For every field `k` of prime characteristic `p` and actual smooth connected
commutative affine group scheme `U` killed by `p` on all relative scheme
tests, the theorem constructs ground-field factors `V` and `W` and an actual
group-scheme isomorphism `U ≅ V ⊗ W`. The factor `V` has natural additive
coordinates on every relative scheme test. The commutative factor `W` is
smooth, affine, connected and unipotent in the existing coefficient-
representation sense. Every morphism from the affine line over
`SeparableClosure k` to the actual base change of `W` is constant. Arbitrary
universe `u`, finite and imperfect fields, nonreduced tests and dimension-zero
vector factors are retained. There is no extra structural premise.

The implemented proof first applies
`smoothCommutativePTorsionVectorEmbedding` to obtain an actual closed
embedding over `k` into a vector group. Its natural all-test coordinates give
an actual isomorphism with the standard vector group `Vₙ`. Composing the
embedding with that isomorphism remains a closed embedding.

`ClosedVectorSubgroup.separableLineRetraction` then supplies an actual vector
group `Vᵣ`, a section `s : Vᵣ ⟶ U`, and a homomorphism `q : U ⟶ Vᵣ` with
`s ≫ q = id`. After separable closure, every affine-line map taking zero to
the identity factors through the changed section. Its construction uses a
nonzero additive row annihilating each proper closed vector subgroup, a
strictly smaller ambient vector envelope, and strong dimension induction
through actual scheme-theoretic intersections. The retraction is retained
from the full ambient vector group throughout the induction, so no extension
of a retraction from an intersection is assumed.

The complement is the full scheme-theoretic kernel of `q`, with its inherited
commutative group structure, defined by
`CommutativeSplitProduct.complement q`. The split commutative group
construction gives the actual product isomorphism in the required factor
order. `complement_geometry` supplies smoothness, affineness and connectedness
of this same kernel from the original source geometry and the affine, hence
separated, vector target. The all-test exponent descends along the monic
kernel inclusion. `CommutativePTorsion.isUnipotent` therefore proves the
required original-field unipotence: its proof applies the algebraically
closed p-torsion vector classification after algebraic closure and then the
existing affine unipotence reflection theorem.

After base change to `SeparableClosure k`, functoriality preserves
`s ≫ q = id`. The pointed-map capture property and
`CapturesPointedAffineLineMaps.kernel_hasConstantAffineLineMaps` show that
the full kernel of the changed `q` has only constant affine-line maps.
The canonical `kernelBaseChangeIso` identifies the actual changed complement
with this full kernel; constancy transports along its monic underlying
morphism. This proves the exact separable-closure conclusion in the target.

Worker 1561 assembled the proof and the relation, intersection-induction,
retraction, product and geometric-unipotence adapters. Worker 864 supplied
the polynomial-kernel ambient factor and capture constructions. Worker 1371
supplied the generic pointed affine-line and constant split-kernel adapter.
The vector embedding reuses Worker 1552's exact embedding proof and its
bundled helpers by Workers 1353, 1366 and 1589. Unpublished reused pairs are
included unchanged with the submission so that validation and independent
review can inspect the complete dependency closure. Their own focused
candidates may be integrated first.
