# Actual base change of Deligne's four preliminary sheaf data

This module constructs base change on objects for the actual `eta,T,u,r`
data used in Drinfeld, *Coverings of p-adic Symmetric Regions* (1976),
Section 2 A, printed p.109 (PDF p.3), final paragraph, continuing on printed
p.110 (PDF p.4). The source requires a cyclically graded flat `O[Pi]`-sheaf
`eta`, a graded structural-module sheaf `T` with invertible homogeneous
components, a homogeneous `O[Pi]`-linear map `u` whose structural span
surjects onto `T`, and a rational degree-zero frame `r`. This is derived
infrastructure for the inverse-image assertion of Proposition 2.4 on printed
p.110, rather than a proof of that proposition.

All declarations are in `Langlands.DeligneFormalSpace.SheafPreDatum`.
Fix a commutative ring `O`, a positive natural number `d`, an element `pi`
of `O`, an `O`-algebra field `F`, schemes `S,S'` in the same universe, a
global scalar homomorphism `phi : O -> Gamma(S,top)`, and an arbitrary scheme
morphism `f : S' -> S`. No flatness of `f` is required. Nilpotence and the
local-field hypotheses of the source are not needed for this construction.
The result specializes to those hypotheses.

## Actual maps and compatibility

For `D : SheafPreDatum d pi F phi`, the output lattice and frame are the
actual ordinary inverse image `D.eta.inverseImage f.base`, and the output
tangent sheaf is the actual structural pullback `D.tangent.pullback f`.
The latter has global scalars `pulledGlobalScalar f phi`, the composite of
`phi` and the scheme map on global sections.

`pullbackU` starts on the underlying `O`-sheaf of the constructed inverse-image
lattice. It first uses the inverse of `inverseImageLatticeScalarIso`, then
`inverseImageU`. That earlier map is ordinary inverse image of `D.u` followed
by the canonical map from ordinary inverse image to the underlying sheaf of
structural pullback. No isomorphism assertion about this canonical map is
used. `pullbackUComponent` composes the earlier homogeneous map with the
constructed isomorphism to the actual homogeneous range subsheaf of the
pulled tangent sheaf.

`pullbackU_pi` derives the distinguished-operator equation by inverting the
scalar-comparison square and using `inverseImageU_pi`.
`pullbackUComponent_inclusion` uses the range-component inclusion equation
and the earlier inverse-image inclusion square. Thus the homogeneous maps
are restrictions of the same total pulled map.

## Deriving local generation

`pullbackSpan` is a submodule presheaf of the actual pulled tangent sheaf.
On each open its submodule is the structural-ring span of the range of
`pullbackU` on that open. Restrictions preserve the span by span induction:
naturality handles a generator, additivity handles sums, and semilinearity
of restriction handles structural scalar multiples.

`pullbackLocalSpan` applies the general `ModuleSheaf.localSaturation` helper
to this submodule presheaf. It is a genuine subsheaf, with membership meaning
that each point has a smaller open neighborhood on which the section is in
the displayed structural span.

`pullbackU_unit` proves the precise square between the original `u`, the
actual structural pullback adjunction unit, the ordinary inverse-image
adjunction unit of the lattice, and `pullbackU`. It follows from naturality
of the ordinary unit, `structuralPullbackComparison_unit`, and cancellation
of the two directions of the lattice scalar isomorphism.
`unit_mem_pullbackSpan` then uses span induction to show that the structural
unit takes an original structural span into the pulled structural span.
The generator case is that square; scalar multiplication uses the actual
structure-sheaf homomorphism of `f`.

For an arbitrary original section `t` over `U` and a point `x` of
`f^(-1)(U)`, the original `D.locallyGenerates` supplies a neighborhood `V`
of `f(x)` on which `t` lies in the original span. Naturality of the structural
unit and `unit_mem_pullbackSpan` put its image in the pulled span on
`f^(-1)(V)`. The local-saturation membership criterion gives
`unit_mem_pullbackLocalSpan`.

`unitToPullbackLocalSpan` factors the actual structural adjunction unit
through the pushforward of that subsheaf. Its maps are the original unit
maps with codomain restricted; linearity and naturality follow from the
unit. `unitToPullbackLocalSpan_inclusion` recovers the original unit after
inclusion. `pullbackToLocalSpan` transposes this factorization under the
actual structural pullback/pushforward adjunction. Injectivity of its hom
equivalence proves `pullbackToLocalSpan_inclusion`: the transpose followed
by inclusion is the identity of the pulled tangent sheaf.

Evaluating this identity on an arbitrary pulled section proves
`mem_pullbackLocalSpan`. The neighborhood criterion now gives
`pullback_locallyGenerates` for every pulled section. This argument derives
the required local generation; it takes no preservation certificate as an
input.

## Final constructor and scope

`SheafPreDatum.pullback` assembles the actual inverse-image framed lattice,
structural tangent pullback, pulled total and homogeneous maps, their Pi
and inclusion equations, and the derived local generation. Its type is

`D.pullback f : SheafPreDatum d pi F (pulledGlobalScalar f phi)`.

This unit constructs the four preliminary data on objects. Morphisms and
composition constraints, transport of admissibility conditions (a)-(c),
the functor on Nilp isomorphism classes, the normalized `PGL(d,F)` action,
and the comparison with data attached to special formal modules remain
open. So do the inherited integral determinant and exterior-power subsheaf
comparisons. Proposition 2.4, existence of a special formal module and
representability are not asserted here.
