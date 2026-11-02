# Actual constituents detected by an irreducible exact-functor image

Author: Worker 357.

This internal algebraic construction chooses an actual irreducible subquotient
of a finite-length smooth complex representation whose image under a supplied
exact functor is nontrivial. It also constructs actual representation
equivalences to every other irreducible subquotient with nontrivial image,
provided the image of the ambient representation is irreducible.

## Inputs and returned data

The source and target are the actual categories
`SmoothRep.{0,uG,uV} ℂ G` and `SmoothRep.{0,uH,uV} ℂ H`.
The group universes `uG`, `uH` and carrier universe `uV` are independent.
Both groups have arbitrary supplied topologies. The two categories use the
same carrier universe, as required by the supplied generic exactness predicate.
No comparison between a group universe and the carrier universe is required.

The functor `J` has an explicit `J.PreservesZeroMorphisms` instance.
`Derivative.Mirabolic.MapsShortExactIntertwiners J` is a supplied premise:
whenever actual intertwiners `i` and `q` are injective and surjective with
`range i = ker q`, their images have these same properties. The location of
this predicate's declaration does not make `J` a derivative functor or supply
its exactness.

For an actual smooth representation `A`, the constructor
`Langlands.ExactFunctorDetectedConstituent.choose` assumes:

- `A.HasFiniteLength`, namely finite composition length of the actual complex
  group-algebra module of `A`;
- `(J.obj A).IsIrreducible`, including nontriviality of that image.

It returns `ExactFunctorDetectedConstituent.Data J A`, a structure containing
an actual smooth representation `constituent`, its irreducibility, its actual
subquotient occurrence in `A`, and `Nontrivial (J.obj constituent)`.
Its `equivalence` field takes any actual smooth `E` of the source category,
an irreducibility proof, an actual occurrence of `E` as a subquotient of `A`,
and `Nontrivial (J.obj E)`. It returns an actual equivariant complex-linear
equivalence from `constituent.representation` to `E.representation`.

The occurrence relation is the existing `SmoothRep.IsSubquotient`: a quotient
of an actual invariant subrepresentation, together with a smooth-category
isomorphism. The equivalence field returns data, not an equality of
Grothendieck classes or merely a proposition that an equivalence exists.
The choices and equivalences are noncomputable; no canonical choice or
coherence between the returned equivalences is asserted.

The auxiliary constructor `constituentEquiv` takes two supplied irreducible
actual subquotients `D` and `E` with nontrivial images under `J`, and returns
an actual representation equivalence between them under the same hypotheses
on `A` and `J`. Neither constructor assumes irreducibility, admissibility,
or finite-dimensionality of `A`, nor admissibility or a finite-length theorem
for its functor image.

## Implemented construction

The elementary filtration lemma
`ObjectRepFiltration.index_eq_of_nontrivial_grades` applies over any field
and monoid to a supplied finite zero-to-full filtration of an irreducible
algebraic representation. A nontrivial actual graded quotient forces its
adjacent invariant subspaces to differ: if they were equal, the surjective
graded projection and its kernel characterization would make every quotient
vector zero. Every invariant subspace of an irreducible representation is
bottom or top. Thus the lower step of any nontrivial grade is bottom and its
upper step is top. If indices `i < j` both gave nontrivial grades, monotonicity
between the upper step at `i` and the lower step at `j` would imply
`top ≤ bottom`, a contradiction. The same argument with the indices reversed
proves that the indices must be equal. Repeated and zero filtration steps
are permitted.

To construct `constituentEquiv`, finite group-algebra length gives a
composition series. The published
`LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries`
turns it into an actual invariant filtration `s` of `A` with simple actual
grades. The published `simpleSubquotientFactor` identifies `D` and `E` with
grades `i` and `j` of this same original filtration by representation
equivalences `fD` and `fE`.

The actual image filtration `t := s.exactSmoothImage J` has steps given by
the invariant ranges of the images of the original inclusions. Zero-map
preservation supplies its zero endpoint, and functoriality supplies its full
endpoint and monotonicity. The published exact comparison
`s.exactSmoothImageGradedIso J hJ` identifies each actual smooth grade of `t`
with `J` applied to the corresponding actual smooth grade of `s`.

Lift `fD` and `fE` to smooth-category isomorphisms and apply `J.mapIso`.
Together with the exact graded comparisons, these transport the supplied
nontriviality of `J.obj D` and `J.obj E` to the actual grades `t_i` and `t_j`.
The preceding irreducible-filtration lemma applied to `J.obj A` gives `i = j`.
The actual equivalence returned is `fD.trans fE.symm` after this equality is
substituted. Classical choice extracts the equivalences from their proven
existence propositions.

For `choose`, use a composition series `s` of `A` and the same image
filtration `t`. At least one actual grade of `t` is nontrivial: otherwise
`objectRepFiltrationSubsingleton` would make the entire image subsingleton,
contradicting its irreducibility. Choose such an index `i` and put
`D := s.smoothGradedObject i`. The composition series supplies irreducibility
of `D`; `s.smoothGradedObject_isSubquotient i` supplies its actual occurrence
in `A`. The exact graded comparison transports nontriviality to `J.obj D`.
Store these data, and define the equivalence field by `constituentEquiv`.
The existence argument includes a putative zero-length series: its image
would be subsingleton, so it cannot occur with the assumed irreducible image.

## Derived provenance and independence

This is a derived algebraic construction from the existing finite-length,
actual-filtration, subquotient-factor and exact-image APIs. It introduces no
new literature assertion. Its direct imports are
`Filtration.ExactConstituentExtraction` and
`Filtration.SimpleSubquotientFactorProof`. The first supplies the actual
image filtration and its exact graded comparison; the second supplies
equivalences from irreducible actual subquotients to original simple factors.
The uniqueness argument above is the new elementary step. It uses neither a
Jordan–Hölder comparison nor `Classification.CommonImageMultiplicityOneProof`.

A recursive native audit against Library commit
`5f6cde0afc23676fd99240c550fb11cbac67d970` finds 95 project modules
including this module and 76 external import roots. All 94 inherited project
Lean/Markdown pairs agree byte for byte with that Library. There are no
missing pairs, proof holes, or hits for the excluded host conclusions.
The only classification-named modules in the import closure are
`Supercuspidal`, `SupercuspidalSupport`, `Segments`, `ConstituentRelations`,
and `SupercuspidalTwist`. They provide lower definitions and actual
subquotient relations; this construction invokes no segment-head formula,
cuspidal-support existence or uniqueness conclusion, or segment
classification.

The imported exactness predicate remains an explicit assumption. No
mirabolic or derivative exactness statement is treated as a proved input.
The closure contains none of the excluded segment-derivative, generic
uniqueness, multisegment exhaustion, ordered-head existence, quotient coverage,
ordered conversion, tempered uniqueness, square-integrable classification or
exhaustion, regular exhaustion, or host irreducibility conclusions. In
particular, it does not import either separately submitted
`InvariantBilinearSmoothDual` or `HighestDerivativeConstituentQuotient`.

## Scope of the host task

This supporting construction does not prove
`Langlands.Classification.SegmentHeadProductIrreducibility`. A future
application must establish source finite length, exactness of its actual
functor, and irreducibility of the actual functor image, independently and
with the required universe conventions. No special-head derivative
nonvanishing, truncation, product formula, linked-pair converse, or
permutation argument is supplied here. Both directions of the full
repeated-segment special-head criterion remain obligations of the host task,
with its existing unsaturated base carrier universe and supplied topology.
