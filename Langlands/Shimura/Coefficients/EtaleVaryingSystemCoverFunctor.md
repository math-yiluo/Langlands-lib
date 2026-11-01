# Cover functoriality of finite-torsor systems and their etale base change

Author: Worker 13.

This is an internal categorical construction from the actual systems in
[VaryingCoverInverse](VaryingCoverInverse.md), contravariant cover maps in
[VaryingSystemCoverChange](VaryingSystemCoverChange.md), and the geometric and
sheaf comparisons in
[EtaleVaryingSystemPullback](EtaleVaryingSystemPullback.md) and
[EtaleCrossCoverPullback](EtaleCrossCoverPullback.md). No new external-source
claim or comparison hypothesis is introduced.

Fix `I : Type uI` with a category whose morphisms lie in universe `vI`, and a
group diagram `D : I ⥤ GrpCat.{u}`. Schemes, the commutative ring
`R : Type u`, module carriers and groups share universe `u`; the two index
universes are independent.

`FiniteGeometricTorsorDiagram X D` is Mathlib's full subcategory of
`EquivariantDiagram D X.Etale` on the predicate
`∀ i, IsFiniteGeometricTorsor X (Y.action i)`. Thus an object consists of an
actual varying-group small-etale cover diagram and proofs of its finite
geometric torsor conditions. All equivariant natural transformations between
these diagrams are morphisms; no additional condition or compatibility field
is imposed. In particular, this construction does not choose Shimura covers
or assume their existence.

For any scheme map `f : Z ⟶ X`, without an etaleness hypothesis,
`etaleFiniteTorsorDiagramPullback f D` gives a functor between these full
categories. Its underlying diagram is
`(etaleTorsorDiagramPullback f D).obj Y.obj`. The existing finite-torsor
base-change theorem supplies its property at each index. Its morphisms are
the actual geometric pullbacks of the original equivariant transformations,
wrapped as morphisms in the full subcategory. Functor laws follow from those
of geometric diagram pullback. The object and morphism lemmas expose these
exact underlying constructions.

Write `L_X(Y)` for `etaleAssociatedVaryingSystemFunctor X Y.obj Y.property`.
It takes an arbitrary equivariant module diagram to the associated small-etale
sheaf diagram. Its level transitions are the coefficient-reduction maps
followed by the inverses of the proved finite-torsor cover-comparison maps.
No filteredness, surjectivity of group transitions, or finiteness, freeness or
local constancy of the module diagram is required.

`etaleAssociatedVaryingSystemCoverFunctor X D R` constructs

`FiniteGeometricTorsorDiagram(X,D)ᵒᵖ ⥤
  (EquivariantDiagram(D,ModuleCat R) ⥤ (I ⥤ Sheaf(X_et,ModuleCat R)))`.

It sends a cover diagram to `L_X(Y)`. For a cover map `a : Y ⟶ T`, its
map on `a.op` is the existing transformation
`q_a : L_X(T) ⟶ L_X(Y)`. Identity and composition use the proved
contravariant cover-change laws. The component at a coefficient diagram `M`
and index `i` is precisely `etaleCrossCoverMap` for the identity homomorphism
of `D_i`, the evaluated cover map `a_i`, and the identity coefficient map of
`M_i`. Thus both the cover and coefficient naturalities act on the existing
systems and their actual transition maps.

Now assume `f` is etale. Put `P_f` for geometric diagram pullback and
`Q_f` for postcomposition of sheaf diagrams with the actual
`EtalePullback.restriction f (ModuleCat R)`. The existing comparison is
`lambda_f(Y) : L_X(Y) ⋙ Q_f ≅ L_Z(P_f Y)`.
For every `a : Y ⟶ T`,
`etaleAssociatedVaryingSystemCoverChange_pullback` proves equality of
whole natural transformations:

`whiskerRight(q_a,Q_f) ≫ lambda_f(Y).hom =
  lambda_f(T).hom ≫ q_(P_f(a))`.

Both sides start at the restricted system on `T` and end at the system on
`P_f Y`. The proof applies natural-transformation extensionality at `M`
and then at `i`. The known component formulas reduce the equation to
`etaleConstantAssociatedPullback_crossCover` with the identity group and
coefficient maps. Evaluation of the geometrically pulled-back cover map is
definitionally the corresponding action-level pullback. The square is
proved from the actual invariant-section maps; it is not supplied as data.

`etaleAssociatedVaryingSystemPullbackCoverNatural f D R` packages these
squares as a natural isomorphism of functors on the opposite full cover
category. Its source first applies the cover functor over `X`, then
postcomposes each coefficient-system functor with `Q_f`. Its target first
pulls back the finite-torsor cover geometrically, then applies the cover
functor over `Z`. The component at `Y` is the existing whole-system
isomorphism `lambda_f(Y)`. At `Y`, `M` and `i`, its forward map is exactly
the constant-module associated-sheaf comparison on `Y_i` and `M_i`.
The isomorphism therefore retains naturality in cover diagrams, coefficient
diagrams and level indices simultaneously.

Non-etale inverse image of sheaves, algebraic-closure base change, compact
supports, cohomological comparisons, full-group and Galois actions, and the
specialization to Harris's Shimura towers remain separate obligations.
