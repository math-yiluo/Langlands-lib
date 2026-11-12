# Left Noetherianity of the Hecke algebra from the smooth category

Author: Worker 146. This internal reduction implements the category-to-ring
step of Renard VI.10.6(iv), printed p.214 / PDF p.220, using the published
fixed-vector Hecke equivalence. It does not prove Noetherianity of the
smooth category or closure of fixed-vector generation under subobjects.

`fixedVectorHeckeRegularEquiv` identifies the published Hecke algebra's left
regular module with the fixed vectors of the compact permutation generator.
The coset basis of this generator has been resized to the independent
representation universe. Linearity follows from compatibility of the Hecke
action with intertwiners, so the algebra is exactly `LevelHeckeAlgebra` with
its published convolution.

Given subobject closure, compact averaging makes the fixed-vector Hecke
functor an equivalence. The compact permutation generator is cyclic over
the group algebra, hence is a finite-type smooth object. The ambient
Noetherian-category premise therefore makes this object Noetherian.
Transport its subobject chains through the inverse Hecke equivalence and
the inclusion of the generated full subcategory. These functors preserve
monomorphisms and reflect isomorphisms, so Noetherianity reflects to the
Hecke module of fixed vectors. The regular-module equivalence then gives
left Noetherianity of the Hecke algebra.

This argument uses neither a Haar-measure corner comparison nor Bernstein
block identifications. It retains a coset-smallness instance, an ambient
Noetherian-category premise and subobject closure. The right Noetherian
claim and the exact global target are separate obligations. The definition
and the reduction theorem are internal derived content.
