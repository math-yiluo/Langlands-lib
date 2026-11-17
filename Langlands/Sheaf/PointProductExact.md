# Exactness and injective preservation for actual point products

This internal construction presents the independent coefficients of
`PointProduct.productFunctor` as diagrams on the discrete category of point
indices. This changes the presentation of the coefficient category and retains
the actual product of skyscraper sheaves and its fiber adjunction.

The right adjoint `coefficientProductFunctor` preserves finite limits and is
additive. An epimorphism of coefficient diagrams is surjective at each
coefficient. The natural zero-preserving sections of `PointProductSetSections`
then lift every section of the product sheaf. Consequently this functor
preserves epimorphisms and is exact.

Actual site fibers preserve finite limits. Their diagram-valued functor
therefore preserves monomorphisms, so its right adjoint
`coefficientProductFunctor` preserves injective objects.

For any topological point family and any site object, the existing
germ-defined compact-sections functor is left exact. The natural set sections
also lift its compact sections. Its composite with `coefficientProductFunctor`
is thus exact. These claims use only the imported Library and Mathlib
interfaces; they impose no geometric separation or terminal-object premise.

This pair supplies categorical prerequisites for derived compact acyclicity.
It does not prove vanishing after equivariant induction or the smooth
coreflector.
