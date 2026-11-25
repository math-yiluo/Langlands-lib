# Free sheaf Čech nerves on a site

This is an internal construction from Mathlib's presheaf
limits, Čech nerve, free module, sheafification and linear Yoneda functors.
It does not require finite products or pullbacks in the site category C.

For a Grothendieck topology J on C, a commutative ring R, and an arrow f of
set-valued presheaves, `freeSheafFunctor` applies the free R-module functor
objectwise and then sheafifies. `freeAugmentedCechNerve` applies this functor
to the augmented Čech nerve of f, formed in the presheaf category. Its degree n
is the free sheaf on the presheaf of tuples of n + 1 lifts with a common image.
The presheaf category has the finite wide pullbacks needed for this definition.

`freeCechChainComplex` is the alternating face map chain complex of this
simplicial sheaf. `freeCechAugmentation` is the canonical chain map to the
complex concentrated in degree zero at the free sheaf on the target of f.

For a coefficient sheaf F of R-modules, `cochainComplexFunctor` applies
Hom(-, F) to the free sheaf nerve, with its natural R-module structure, then
takes the alternating coface map complex. Its degree n is the R-module of
morphisms from the nth free sheaf to F. `cohomologyFunctor` takes the homology
of this cochain complex in the chosen degree. All these constructions use the
actual morphisms of sheaves and retain their coefficient functoriality.
The coefficient ring and values of each presheaf lie in `Type w`; the Hom
modules lie in universe `max u w`, where C has objects in `Type u` and
morphisms in `Type v`. Sheafification is an explicit instance hypothesis.

When the morphisms of C can be shrunk to the coefficient universe, `familyArrow`
packages a family U_i -> S as the map from the coproduct of the representable
presheaves of U_i to the representable presheaf of S. The final theorem is the
published covering-sieve/local-surjectivity criterion specialized to this map.
No subcanonical assumption is needed: representables here are presheaves and
are sheafified only after applying the free module functor.

This module neither proves that the augmented chain complex resolves its
target for a cover nor gives a comparison with derived sheaf cohomology.
Those are separate mathematical obligations; this module supplies their
concrete input complex without geometric product assumptions.
