# Actual determinant factorization for module-sheaf biproducts

This internal unit constructs the tensor factorization of the existing
chosen determinant line of a genuine biproduct of finite locally free
module sheaves on any scheme. It allows the ranks to vary between local
charts, including rank zero, and makes no nontrivial-ring, compactness,
noetherian or splitting assumption for the factorization.

For actual module sheaves `M` and `N`, `biprodSectionsEquiv M N U` identifies
sections of the genuine categorical biproduct `M ⊞ N` over `U` with the
product of the two actual section modules. Its forward map uses the actual
biproduct projections; its inverse adds the images under the actual
inclusions. The biproduct equations prove that these are inverse linear
maps. Naturality of the projections gives restriction compatibility.

`BiproductDeterminant.sectionBasis` transports the product basis through
this equivalence on every open inside a supplied pair of finite free
frames. Restriction compatibility produces actual free sheaf product
frames through `affineBasisFrame`. The computed section bases of these
frames are precisely the transported product bases. The algebraic mixed
unit product formula and invariance under a common linear equivalence
therefore show that their actual determinant cocycle is the pointwise
product of the summand determinant cocycles, on every overlap open.
The actual glued-cocycle tensor isomorphism then identifies the actual
product frame determinant line with the tensor of the two frame lines.

`FiniteLocalFrames.productLeft` and `productRight` restrict any two
finite-frame covers to their common intersections. The resulting
`FiniteLocalFrames.biprod` supplies actual finite local bases of the
biproduct, with local rank equal to the sum of the two local ranks.
`HasFiniteLocalBasis.biprod` records the resulting finite-basis property.

`finiteLocallyFreeDeterminantBiprodIso hM hN hP` compares the existing
chosen determinant for any finite-basis witness `hP` of `M ⊞ N` with the
actual tensor product of the existing chosen determinants for `hM` and
`hN`. It uses the common-refinement frame factorization and the canonical
actual frame-presentation comparisons, so it does not replace any chosen
determinant construction. The finite-basis witness for the biproduct can
also be obtained from `hM.biprod hN`.

`finiteLocallyFreeDeterminantBiprodPullbackIso` specializes the second
summand to the actual pullback of a base sheaf. The existing actual
determinant pullback isomorphism identifies its determinant factor with
the actual pullback of the existing base determinant line. Finally,
`finiteLocallyFreeDeterminant_biprod_pullback_isAmple_iff` proves that this
base-summand stabilization preserves and reflects ampleness of the actual
determinant when the total scheme is compact and quasi-separated and the
base is affine. It applies the proved actual affine-base line-twist
ampleness equivalence to the constructed actual tensor isomorphism.

The provenance is internal: actual biproduct identities, actual free
frames from section bases, mixed finite basis determinants, cocycle tensor
gluing, determinant presentation comparisons and determinant pullback
supply the factorization. The final ampleness equivalence uses affine-base
ampleness locality through the existing twist theorem. No classified
Grassmannian comparison or parabolic jet positivity is asserted here.
