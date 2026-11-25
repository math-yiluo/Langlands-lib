# The affine simply connected Weil restriction theorem

The proof uses the relative almost-simple normal-idempotent theorem, finite-étale
chart-algebra descent and finite-family products; the Weil-pair descent, abelian-image
triviality and projection injectivity; and the almost-simple field-ascent argument of the
imported modules.

`affineSimplyConnectedWeilRestriction` proves
`Langlands.GroupScheme.AffineSimplyConnectedWeilRestrictionStatement.{u}` in every universe.
For a reductive `G` over `Spec A` with nontrivial simply connected geometric fibres, it gives a
finite projective étale `A`-algebra `B` such that `Spec B → Spec A` is surjective, and a
reductive `G'` over `Spec B` with simply connected almost-simple geometric fibres and
`G ≅ AffineWeil.groupScheme A B G'`. It also compares any two presentations satisfying
the hypotheses of the uniqueness clause. The assertion includes the zero ring.
[Published statement](AffineSimplyConnectedWeilRestrictionStatement.md)

## Proof

1. `WeilFactor.weilFactorIdempotentRigidity_of_inputs` applies
   `relativeAlmostSimpleNormalIdempotent` and `weilAbelianImageTriviality` to obtain
   `hR : WeilFactorIdempotentRigidityStatement.{u}`. The first theorem identifies
   relative normal idempotents of the affine point functor of a reductive group with
   almost-simple geometric fibres with projections given by coefficient idempotents.
   The second shows that a homomorphism of point functors from a Weil restriction
   of a reductive group with semisimple geometric fibres is trivial when its values
   on each test algebra commute. Its proof uses fppf-local membership in commutator
   subgroups and fppf separation.
   [Rigidity reduction](WeilFactorRigidityReduction.md),
   [normal idempotents](RelativeAlmostSimpleNormalIdempotentProof.md),
   [abelian images](WeilAbelianImageTrivialityProof.md).
2. `affineWeilPairEtaleDescent hR Langlands.AlgebraicGeometry.finiteEtaleChartDescent`
   supplies `AffineWeilPairEtaleDescentStatement.{u}`. Rigidity supplies the coefficient
   comparison maps on overlaps. Finite étale chart descent gives the descended algebra
   and the corresponding tensor-algebra isomorphisms. Pair descent constructs the factor
   group and recovers the local presentations over these comparisons.
   [Weil-pair descent](WeilChartSingleChartDescent.md),
   [finite étale chart descent](../../AlgebraicGeometry/FiniteEtaleChartDescentProof.md).
3. `affineSimplyConnectedWeilRestriction_of_pairDescent_and_rigidity` applies the
   pair-descent result and `hR` to prove both conjuncts. For existence, it takes a
   pinned étale atlas and forms the actual derived groups of complementary-torus
   centralizers on the pinned charts. Comparisons on algebraically closed field fibres
   give product isomorphisms after passing to further étale charts, by the affine split
   isomorphism theorem. Finite-family assembly expresses these products as Weil
   restrictions. Descent first gives a presentation on each pinned chart and then gives
   the presentation over `Spec A`. The local tensor-algebra and group isomorphisms in
   each descent step reflect simple connectedness of the descended geometric fibres.
   [Final reduction](AffineSimplyConnectedWeilRestrictionReduction.md),
   [existence construction](SimplyConnectedWeilExistenceReduction.md),
   [reflection under descent](SimplyConnectedWeilPresentation.md).
4. For the second conjunct the same reduction calls
   `WeilFactor.affineSimplyConnectedWeilRestriction_uniqueness_of_rigidity`. It composes
   the two isomorphisms through `G` to compare the Weil restrictions directly. Rigidity
   yields an `A`-algebra isomorphism `α : B'' ≃ₐ[A] B` and an isomorphism between the
   pullback of `G''` along `Spec α` and `G'`.
   [Uniqueness reduction](WeilFactorUniquenessReduction.md).

## Source

This composite proof implements the affine form of Proposition 6.4.4 in Brian Conrad,
*Reductive group schemes* (2014), pp. 232–233, registered as
`conrad-2014-reductive-group-schemes`. The existence argument uses the étale-local
product decomposition in that proposition. The comparison of presentations in the
published Lean statement is existential, and the implemented argument obtains it
from normal-idempotent rigidity.
