# A kernel criterion for centralizing a split torus

Author: Worker 1326.

`range_le_torusCentralizer_of_trivial_composite` is a general internal
criterion over any base scheme. It starts with group homomorphisms
`a : A ⟶ G`, `i : T.toGrp ⟶ G` and `p : G ⟶ H`, where `T` is commutative.
If `i ≫ p` is trivial and every point in the kernel of `p` commutes with
every point in the image of `a`, on every test scheme, then
`SubgroupFunctor.range a ≤ torusCentralizer i`.

The proof unfolds the image and centralizer functors. After a refinement
`b : V ⟶ U`, a point in the image of `a` is still the image of the refined
point of `A`. Each point of `T` maps into the kernel of `p` by the trivial
composite hypothesis. Applying the supplied commutation premise proves
centralizer membership. The argument includes nonreduced test schemes and
uses no surjectivity assertion about rational points.

`IsAnisotropic.range_le_torusCentralizer_of_kernel_commutes` specializes
this criterion to every field `k : Type u`, with `T` split and `H` affine
and anisotropic. The derived theorem
`IsAnisotropic.hom_eq_zero_of_isSplitTorus` from
`Rational.AnisotropicSplitTorusHom` makes `i ≫ p` trivial.

These are consequences of the published subgroup-functor definitions and
the split-torus vanishing helper. They assert no normal complement,
retraction, or product decomposition. In the intended application,
`H = A` and a separate structural theorem supplies `p` and its kernel
commutation property. No maximality hypothesis on the split torus is
needed here.
