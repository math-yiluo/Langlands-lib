# The quadratic unitary Levi as a represented closed subgroup

`Langlands.GroupScheme.QuasiSplitUnitary.LeviRepresentedStatement` is S6
of the quasi-split `U(1,1)` construction. It is a proposition definition,
with its proof assigned to a separate proof task after publication.

The statement quantifies over fields `F` and `E`, an `F`-algebra structure
on `E`, `Algebra.IsQuadraticExtension F E`, a finite `F`-basis `b` of
`Matrix (Fin 2) (Fin 2) E`, and a nonidentity `F`-automorphism `c` of `E`.
It has no restriction on the characteristic, so it includes
characteristic two. The group is the existing full unitary group scheme
`groupScheme b c`, defined using the antidiagonal hermitian form and
the Library's algebra-involution scheme model.

There are two conjuncts:

1. The subgroup functor `Dynamic.centralizer (cocharacter b c)` is
   represented by `leviHom b c`. Here `SubgroupFunctor.IsRepresentedBy`
   means that the map is a monomorphism of schemes over `Spec F` and its
   range subgroup functor equals this centralizer, on every test scheme.
2. `IsClosedSubgroup (leviHom b c)` holds: the underlying scheme morphism
   is a closed immersion.

The representing source is the published
`WeilGm.groupScheme (CommRingCat.of F) E`, namely `Res_{E/F} 𝔾ₘ`.
The map `leviHom b c` was constructed in `QuasiSplitUnitaryLevi`; on
points with coefficient algebra `R` it is
`a ↦ diag(a,c_R(a)⁻¹)`.

This is the derived full-unitary specialization of the dynamic Levi
framework. Milne, *Algebraic Groups* (2017), Example 13.31 and
Theorem 13.33 with its proof, printed pp.264–266, give the analogous
`SL₂` calculation and general dynamic decomposition. His Proposition
24.40, Definition 24.42 and Theorem 24.44, printed pp.523–525, give the
unitary algebra-involution context. The last theorem concerns special
unitary groups; neither passage is being cited as an explicit computation
of this full unitary Levi. The particular tensor-unit formula and
representation assertion are derived from the antidiagonal hermitian
presentation and the represented point models.
