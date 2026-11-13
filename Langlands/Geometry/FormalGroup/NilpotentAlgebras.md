# Nilpotent coefficient algebras and formal module points

`Nilp R π` is the full subcategory of commutative R-algebras A satisfying
`IsNilpotent (algebraMap R A π)`. Its morphisms are all R-algebra
homomorphisms. Thus there is no chosen nilpotence exponent and no restriction
to Artinian, local or reduced algebras. `Nilp.of` constructs an object from
the algebra and a proof of this condition; `Nilp.forget` is its inclusion
into `CommAlgCat R`.

For a finite-coordinate formal O-module M over a commutative O-algebra R,
`ModuleLaw.algebraMapPoints` constructs the O-linear map on nilpotent
points induced by an R-algebra homomorphism. The O-algebra structures
on its source and target must form scalar towers with R. Its underlying
map applies the algebra homomorphism to every coordinate series.
Compatibility of coefficient mapping with formal substitution proves
O-linearity, identity and composition.

`algebraPointFunctor` uses the canonical composite O → R → A to construct
an actual functor `CommAlgCat R ⥤ ModuleCat O`. Its value is the O-module
of nilpotent coordinate tuples with M's evaluated group law and scalar
action. `nilpPointFunctor π` restricts this functor along `Nilp.forget`.
An O-linear formal homomorphism induces the natural transformation
`Hom.algebraPointNatTrans`; its naturality is the same compatibility
of coefficient mapping and substitution.

The source for the category is Drinfeld, *Coverings of p-adic Symmetric
Regions* (1976), §2 A, printed p.109, the paragraph beginning “Let Nilp”.
Specializing R to the integers O of its local field and π to a uniformizer
gives exactly the category defined there. Allowing an arbitrary commutative
R and a distinguished element is a derived generalization useful for
completed unramified coefficient extensions. The module-valued point
functors and their linear natural transformations are derived
infrastructure for the finite-coordinate formal O-modules of §1,
printed p.108. This module does not construct the functor G, heights,
locally glued formal groups or a representing object.
