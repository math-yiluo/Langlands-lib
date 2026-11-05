# Continuity on actual adelic points for independently chosen spreads

`adelicSpreadFunctoriality` proves `AdelicSpreadFunctorialityStatement`.
`curvePlaceSpreadFunctoriality` and `numberFieldSpreadFunctoriality` prove
its two clauses. Postcomposition by an arbitrary morphism of schemes over
the original field is continuous on their actual full-adele points for
the topologies from any two specified finite-type arithmetic spreads.
The morphism is not assumed to lift to the chosen models.

All hypotheses and point carriers are those of the target. The curve
clause permits arbitrary perfect constants with the specified compatible
rational-function scalar tower and function-field structure. The
number-field clause uses the full `Adeles K`, including every infinite
factor. The two finite initial sets need not be comparable and may be
empty. The models may be nonaffine and nonseparated. Their structure maps
are locally of finite type and quasi-compact, hence of finite type.
The original integer and field scalar actions are retained.

This is a derived implementation of the explicit functoriality target
motivated by Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed p.6 following (3.5.1) and the opening of
section 4 on printed p.9. The perfect-constant-field and empty-initial-set
scope is the derived extension explained in the target's Markdown.
The implementation reuses actual integer-ring colimits, scheme-morphism
descent, continuity for model points, initial-set homeomorphisms and
independence of spreads. The general categorical helpers below are
internal consequences of these constructions.

First put the existing scheme-limit model cone in the standard `Over`
pullback order by conjugating its legs with pullback symmetries.
The resulting cone leg preserves the first model projection; its second
projection is the limit projection followed by the corresponding
integer-spectrum cone leg. For a prescribed morphism of the limit
pullbacks, `exists_level_morphism` produces a morphism at an actual
arithmetic stage. The helper conjugates that morphism in the same way
and retains its exact commutative square with the cone legs.

For each arithmetic case, the actual field-valued integer-ring colimit
gives the needed spectrum limit through `spectrumConeIsLimit`.
`adelicSIntegersNoetherian` makes the initial integer base Noetherian.
The finite-type models are locally Noetherian, supplying the
quasi-separatedness and local finite presentation required by morphism
descent without a separatedness premise. The arithmetic cone-leg point
identity follows by comparing the two pullback projections. Its first
projection uses the generic-fiber and initial-set point-equivalence
formulas; its second uses the original field diagonal and integer
inclusions.

For models with the same initial base, conjugate the given field-scheme
morphism by the specified generic-fiber isomorphisms, giving a morphism
between the actual generic fibers of the models. Descend it to a larger
finite place set T. The continuous model-point map at T, composed with
the first initial-set homeomorphism and the inverse second initial-set
homeomorphism, gives a continuous map between the original model-point
spaces. Its action after initial-set enlargement is exactly
postcomposition by the descended morphism.

The retained descent square and the first-projection formulas identify
this map after passage to the actual generic fibers. The proof applies
the injectivity of the inverse generic-fiber point equivalence and
compares the resulting underlying model morphisms. Postcomposition by
the second specified isomorphism then cancels its inverse from the
conjugated morphism. Composing with the two defining spread
homeomorphisms therefore gives the literal point map `p ↦ p ≫ g`.
Continuity transfers to that map.

For arbitrary initial sets S and U, base change both models to S union U.
Finite type is preserved by these actual pullbacks.
`modelPullbackCompIso` identifies each new generic fiber with the original
one, supplying a specified identification with its original field-scheme.
The spread-independence theorem equates the original and enlarged
topologies on each actual point type. Rewriting by these two equalities
reduces continuity to the same-base case. The number-field proof carries
out all these steps with its own integer diagram and full adele diagonal.
The entry theorem combines the two proved arithmetic clauses.

This proof establishes functoriality for specified spreads. Existence of
arithmetic spreads for every finite-type field-scheme, agreement with
other point topology constructions, and the other conclusions of the
paper remain separate results.

The model-cone projection, morphism-descent and pullback-composition helpers are
shared with the related spread proofs through
[`AdelicSpreadModelMorphisms`](AdelicSpreadModelMorphisms.md). This integration
consolidation preserves their definitions, hypotheses and conclusions.
