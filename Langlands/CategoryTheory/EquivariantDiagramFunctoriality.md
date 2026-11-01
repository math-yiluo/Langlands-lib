# Identity and composition of functors on varying-group diagrams

For a fixed, arbitrary group diagram `D : I ⥤ GrpCat`, this module supplies
three natural isomorphisms for the existing `EquivariantDiagram.mapFunctor`.
The index, group and three category object/morphism universes are independent.

`mapFunctorCongr e` applies the actual `postcompose` functor to a natural
isomorphism `e : F ≅ F'`. Its forward and inverse components at diagram `M`
and index `i` are exactly `e.hom.app (M.obj.obj i)` and its inverse. The
existing `mapNatTrans` construction proves equivariance and naturality along
every index arrow and diagram morphism.

`mapFunctorId` identifies mapping the identity functor with the original
varying-group diagram functor. `mapFunctorComp F F'` identifies mapping a
composite with successively mapping its two factors. Their components are
identity morphisms. They are constructed as natural isomorphisms with reflexive
object components: the actions and transitions of both presentations agree
definitionally. Explicit component equations record the underlying maps.

This is internal categorical infrastructure, with no literature assertion or
geometric existence assumption. It supplies identity and binary composition
comparisons, without claiming higher coherence equations in this module.
