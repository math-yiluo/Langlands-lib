# Proof of étale-local lifting of normalized CM classes to smaller small levels

The theorem `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel.cmSublevelEtaleLift` has
type exactly `CMSublevelEtaleLiftStatement D C preservation composition unitCoherence
associativity comparison symmetry stability square universality dualityNaturality
polarizationStability compatibility h htor` of the module
`HarrisTaylorCMNormalQuotientPremiseStatements`: for small levels `U' ≤ U`, every
admissible test `S` (an object of `ComponentwiseAdmissibleCMBaseCategory`) and every
class `c` of `(smallLevelClassPresheafTower …).obj U` on `S`, there are an admissible
test `S₁`, a test morphism `p : S₁ ⟶ S` whose underlying scheme morphism is étale and
surjective, and a class `c₁` at level `U'` on `S₁` whose image under the forgetting
transition at `smallCMInclusion D hle` is the pullback of `c` along `p`. No normality
or division hypothesis is used.

## A coproduct lemma

`Langlands.AlgebraicGeometry.exists_componentι_factor_sigmaι`: for a family `Z` of
schemes with locally Noetherian coproduct `∐ Z`, the inclusion of every connected
component of `∐ Z` factors through the inclusion `Sigma.ι Z d` of one summand. Choose
a point `z` of the component and let `d` be the index of `(sigmaMk Z).symm z`. The
preimage under the homeomorphism `(sigmaMk Z).symm` of the summand `d` of the
topological disjoint union is clopen (`isClopen_range_sigmaMk`), so it contains the
connected component of `z` (`IsClopen.connectedComponent_subset`); by `sigmaMk_mk`
every point of that component lies in the range of `Sigma.ι Z d`, and the factorization
is `IsOpenImmersion.lift`.

## The proof

A class `c` on `S` is a family indexed by the connected components `d` of `S`, its
value at `d` an unpointed class on the connected admissible component scheme
`componentCMBase S d` (`disconnectedClassTower`). For every `d`,
`unpointedClassTower_exists_sublevel_etaleCover` of the module
`HarrisTaylorCMSublevelConnectedCover` gives a connected admissible base `T d`, an
étale surjective `f d : T d ⟶ componentCMBase S d` and a class `w d` at level `U'` on
`T d` whose image under the forgetting transition is the pullback of `c d` along
`f d`.

Let `S₁` be the scheme coproduct `∐ d, (T d).obj.left` over `Spec F` with the
structure map `Sigma.desc` of the structure maps of the `T d`. It is locally Noetherian
(`isLocallyNoetherian_iff_openCover` for `sigmaOpenCover`), hence an admissible test by
`componentwiseAdmissibleCMBase_of_relativeDual` with the published
`relativeDualSchemeExistence` and `relativeDualSchemeGeometry`. The morphism `p` has
underlying scheme morphism `Sigma.desc` of the composites of `f d` with the component
inclusions of `S`; it is a morphism over `Spec F` by `Sigma.hom_ext`. It is étale by
`IsZariskiLocalAtSource.sigmaDesc` (each composite is étale), and surjective by
`Surjective.sigmaDesc_of_union_range_eq_univ`: a point `x` of `S` lies in its own
component `d`, and `f d` is surjective onto that component.

For each connected component `e` of `S₁`, the coproduct lemma gives an index `d e` and
a factorization `g e` of the inclusion of `e` through the summand `T (d e)`; it is a
morphism `G e : componentCMBase S₁ e ⟶ T (d e)` of admissible bases. Define
`c₁ e` as the pullback of `w (d e)` along `G e`. A point of `e` maps under `p` into
the component `d e` of `S`, so `componentMap p e = d e`, and the restriction of `p`
from `e` to `d e` is `G e ≫ f (d e)` by `componentHomTo_unique`. Hence, by
`disconnectedClassTowerPullback_app_eq` and `unpointedClassTowerPullback_comp`, the
value at `e` of the pullback of `c` along `p` is the pullback along `G e` of the
pullback of `c (d e)` along `f (d e)`, which is the pullback along `G e` of the image
of `w (d e)`. By naturality of pullback in the level (`naturality_apply`) this is the
image of `c₁ e` under the forgetting transition, which is the value at `e` of the
image of `c₁`.

The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.
