# Exact Grothendieck classes of finite smooth products

Author: Worker 164.

This internal adapter proves that the exact Grothendieck class of a finite
product of actual finite-length smooth representations is the sum of their
classes. Its actual Aubert specialization expresses the class of each finite
degree object as the sum of its actual induction--Jacquet term classes. No
homological concentration or signed-effectivity result is asserted.

`FiniteProduct.object A` bundles the pointwise product action of the actual
objects `A j`, smoothness from the finite intersection of coordinate
stabilizers, and finite group-algebra length from `FiniteLengthCutComplex`.
The index type is a finite type in `Type 0`. Consequently the product carrier
remains in the original coefficient-module universe, so it and all coordinate
objects lie in the same exact Grothendieck group. The group universe and carrier
universe remain independent; no resizing of actual isomorphism classes is used.

`class_eq_zero` first proves that a subsingleton object has zero class. The
zero maps from that object to itself give an actual short exact sequence,
since all three modules are trivial. Its exact class relation gives `x=x+x`,
hence `x=0` by cancellation in the exact Grothendieck group.

`reindex e A` is the actual equivariant linear equivalence from the product
indexed by the codomain of `e` to the product indexed by its domain. Its linear
part is the inverse of `LinearEquiv.piCongrLeft`; it sends a family `x` to the
family `j ↦ x(e j)`. The pointwise actions make equivariance definitional.

For an option-indexed family, `optionIn` inserts the `none` coordinate and
places zero in every `some` coordinate. `optionOut` forgets the `none`
coordinate. Both are actual intertwiners. Evaluation at `none` proves
injectivity of `optionIn`; extending a family by zero at `none` proves
surjectivity of `optionOut`. A family in the kernel of `optionOut` is zero at
every `some` coordinate, and so is precisely the image of its `none` value.
This proves `option_shortExact` using the published predicate on actual
intertwiners. The defining exact class relation then gives `option_class`.

`class_eq_sum` uses `Fintype.induction_empty_option`. Reindexing handles
transport through an equivalence of finite index types; the empty product is
subsingleton and has zero class; the option step applies `option_class` and
the induction hypothesis to the remaining coordinates. The final sum is the
ordinary finite sum of the coordinate classes.

These are equalities in the existing exact Grothendieck quotient. Although the
particular coordinate sequences used by this proof split, that quotient still
imposes every actual short exact relation, including all nonsplit ones. The
module does not replace it with a split quotient or assume that other exact
sequences split.

`ActualCutComplex.finiteTerm F T B A hA` bundles the actual action
`Transition.term T B A.representation` as a finite-length smooth object, using
`term_hasFiniteLength`. For degree `k`, the family consists of these actual
objects indexed by cut sets `s` with `s.card=k`, with shape
`(BlockShape.cutEquiv n).symm s`. An identity linear equivalence with definitional
equivariance identifies the previously constructed `finiteDegree` with this
finite product. Exact classes respect that actual smooth isomorphism, and
`FiniteProduct.class_eq_sum` therefore proves `ActualCutComplex.degree_class`.

The construction includes the empty index and rank zero and retains arbitrary
primes, the supplied p-adic field/topology and independent universes. In the
actual specialization all carriers remain saturated in `Type (max uF uV)`.
The input finite-length witness is retained; no admissibility, finite dimension,
semisimplicity, irreducible preservation or classification hypothesis is added.

The provenance is internal: the proof uses the explicit product actions and
coordinate maps and the already published defining relation of the exact
Grothendieck group. Its actual specialization reuses the actual complex and
finite-length adapters. Regrouping these classes into the alternating operator,
reflecting Jacquet exactness, proving support concentration and comparing the
surviving terminal class remain separate obligations.
