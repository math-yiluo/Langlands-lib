# Lifting standard étale algebras across quotient maps

This module supplies the affine chart construction used to lift an étale cover
through a nilpotent thickening. It is derived from Mathlib's standard étale
presentations, polynomial lifts and tensor-product description of quotient
algebras.

`derivativePair` localizes at the product of the derivative of the monic
polynomial and the chosen localization polynomial. This product makes the
standard étale pair condition hold directly. In a standard étale presentation,
the derivative and the localization polynomial are both units at the specified
generator. `derivativePairEquiv` compares the two presentations by mapping their
generators to one another. The maps are inverse because the algebra maps out of
each presentation are determined by the generator.

`exists_pair_map_equiv` lifts the coefficients of the two polynomials along a
surjective ring map, preserving monicity of the defining polynomial. The
derivative commutes with coefficient change, so the lifted derivative pair
reduces to the modified presentation. `exists_pair_tensor_equiv` applies the
base-change construction for standard étale presentations to identify the
tensor reduction with the given algebra.

`exists_etale_quotient_lift` composes that equivalence with the identification
of the tensor reduction with the quotient by the extended ideal. The resulting
ring map is compatible with the coefficient-ring quotient, is surjective and
has kernel exactly the extended ideal. These assertions hold for every ideal.
`exists_etale_nilpotent_lift` uses preservation of ideal powers under extension
to deduce nilpotence of the kernel when the original ideal is nilpotent.
