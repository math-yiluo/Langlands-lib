# Canonical evaluation across maps of covers

Author: Worker 13.

This internal construction extends the canonical evaluation in
`TrivializationFromSplitting` to localization along any map into the cover. It
proves compatibility with the actual maps in `CrossCover` and constructs a
natural trivialization under the existing graph-splitting hypothesis. Its
provenance is restriction of sheaf sections along graphs, naturality of sheaf
morphisms, and the previously proved bijectivity of invariant evaluation. No
external theorem is transcribed, and no imported declaration is changed.

## Parameters and maps

Let `C : Type w` have `Category.{v} C` and binary products, and let `J` be a
Grothendieck topology on `C`. Let `R : Type u` be a commutative ring. Coefficient
module carriers and the groups `G` and `H` are in `u`. The site universes remain
independent. No topology on a group, finiteness, or covering hypothesis is used
for the evaluation maps and their compatibility.

For a morphism `a : Z → Y` in `C`, `productEvaluationAlong J a F` is a morphism
on `J.over Z` from the restriction of `productSheaf J Y F` to the restriction
of `F`. At an object `U : Over Z`, it restricts sections along

`prod.lift (U.hom ≫ a) (identity U.left) : U.left → Y × U.left`.

Its naturality follows from composition of these graphs with morphisms of the
slice. `productEvaluationAlong_natural` is naturality in the coefficient sheaf.
For an action `Y : Action C G` and the identity map of `Y.V`,
`productEvaluationAlong_id` recovers the existing `productEvaluation J Y F`.

`coverPullback_productEvaluation` states that first restricting sections from
`Y × U` to `Z.V × U` along `a × id`, and then evaluating at the chosen lift
`U → Z.V`, is exactly evaluation along the composite lift `U → Z.V → Y`.
Its proof composes the two actual restriction maps and computes the product
morphism using the product identities.

For `Y : Action C G`, `a : Z → Y.V`, and a coefficient sheaf action `F` of `G`,
`associatedEvaluationAlong J Y a F` first restricts the invariant inclusion
to `J.over Z` and then applies `productEvaluationAlong`. Its source is the
restriction of `associated J Y F`; its target is the restriction of `F.V`.
It recovers `associatedEvaluation` for the identity map. The natural
transformation `associatedEvaluationAlongNat` assembles these maps in `F`;
its proof uses the existing naturality of invariant inclusion and the
coefficient naturality of evaluation.

## Cross-cover compatibility

Let `Y : Action C G`, `Z : Action C H`, `φ : H →* G`, and
`a : Z → (Action.res C φ).obj Y`. Let `F` be a coefficient sheaf action of
`G`, `E` one of `H`, and `c : (Action.res _ φ).obj F → E`. Write `L_Z` for
`J.overPullback (ModuleCat R) Z.V`. Then `crossCoverMap_evaluation` proves

`L_Z.map (crossCoverMap J φ a c) ≫ associatedEvaluation J Z E`

`= associatedEvaluationAlong J Y a.hom F ≫ L_Z.map c.hom`.

This is an equation for the specific constructed cross-cover map. The proof
uses its inclusion formula, functoriality of localization, coefficient
naturality of evaluation, and `coverPullback_productEvaluation`. It does not
choose an unrelated comparison isomorphism. The equation allows an arbitrary
group homomorphism and compatible cover map; it imposes no surjectivity
condition on either.

## Trivialization along a map

`associatedTrivializationAlongOfSplitting J Y a hsplit` assumes precisely that
for every module sheaf `F` and every `U : Over Y.V`, the map

`s ↦ (g ↦ graphRestriction J Y F U g s)`

from `F(Y.V × U.left)` to `G → F(U.left)` is bijective. Under that hypothesis
it constructs a natural isomorphism from `associatedFunctor J Y` followed by
`L_Z` to the forgetful functor on coefficient sheaf actions followed by `L_Z`.
Its forward natural transformation is exactly `associatedEvaluationAlongNat`,
as recorded by `associatedTrivializationAlongOfSplitting_hom`.

For a slice object `U : Over Z`, the component of evaluation along `a` is
definitionally the existing evaluation at `(Over.map a).obj U`. Applying
`associatedEvaluation_bijective` to that object proves componentwise
bijectivity. The isomorphism criterion for module homomorphisms, followed by
the componentwise criteria for natural transformations and the full
subcategory of sheaves, gives the natural isomorphism. Thus the construction
uses the earlier graph-splitting argument without repeating it.

The splitting hypothesis is substantial. This module does not prove it from
geometric torsor assumptions, nor does it descend invertibility from a slice
to the base site. The global finite-etale-torsor comparison, varying-cover
inverse coefficient systems, tensor/reduction comparison and actual Harris
schemes and torsors remain separate obligations. The constructions here apply
to arbitrary module sheaf actions; no additional constant-sheaf identification
on the slice is asserted.
