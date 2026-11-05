# Ambient vector factors of additive polynomial kernels

This internal construction strengthens the iteration for explicit additive
polynomial kernels by retaining an isomorphism of the ambient vector groups.
It does not give a presentation for an arbitrary unipotent group.

For an additive row `f : Fin n → k[X]`,
`exists_polynomialKernelAmbientFactor` produces natural numbers `r,m` with
`r+m=n`, an additive row `g` in `m` variables whose actual kernel has only constant
actual affine-line morphisms, and an actual group-scheme isomorphism
`e : V_n ≅ V_r × V_m`. The original row is the composite of `e`, the second
projection, and the row `g`. Here `V_d` is the actual standard vector group of
coordinate count `d`; `m` is the residual row length, not an assertion about the
dimension of its kernel.

If the original kernel is already constant, the first factor has dimension zero.
Otherwise the existing shear construction makes one row entry zero. Splitting
that coordinate reduces the row length; induction, the cartesian associator,
and vector coordinate splitting combine the accumulated vector factors. All
isomorphisms are actual group-scheme isomorphisms and use natural coordinates
on every relative scheme test. The previously constructed actual scalar-change
comparison proves in `exists_polynomialKernelAmbientFactor_separableClosure`
that the same residual kernel stays constant after actual scheme base change
to the separable closure.

Given such an ambient isomorphism, `polynomialKernelAmbientSection` is
`lift id 0 ≫ e.inv`, and `polynomialKernelAmbientRetraction` is `e.hom ≫ fst`.
Their composite is the identity. The section is a closed immersion, since it is
a section of a retraction and its target is affine over the base. Under the row
factorization it is annihilated by `f`.

`polynomialKernelAmbientKernelIso` restricts `e` to an actual isomorphism
`kernel(row f) ≅ V_r × kernel(row g)`. It composes the existing kernel
coordinate-change isomorphism with the kernel-of-second-projection isomorphism.
The three projection and inclusion formulas record compatibility with the actual
kernel inclusions and the ambient retraction. Including the vector factor in the
decomposed kernel and then in `V_n` is exactly the ambient section. These
identities follow from the pullback and cartesian product identities used to
construct the two isomorphisms.

`polynomialRow_zeroVariables` identifies the empty row with the zero
homomorphism by its sum on every scheme test. `polynomialRow_eq_zero_iff` proves
that the actual row vanishes exactly when its polynomial tuple is zero. For the
nontrivial direction, test it on the actual affine line with the universal
coordinate in one position and zero elsewhere. Additivity makes each other
coordinate contribute zero. The existing global-function polynomial bijection
on the affine line then detects that row entry as the zero polynomial. This
argument works over finite as well as infinite fields.

`polynomialKernelAmbientFactor_rank_lt` shows that a nonzero actual row forces
`m > 0`: otherwise its factorization goes through the empty row and is zero.
Together with `r+m=n` this gives `r<n`.
`exists_polynomialKernelAmbientFactor_of_ne_zero` combines this conclusion with
the same ambient decomposition and separable-closure constancy when the given
polynomial tuple is nonzero.

The construction works over every field in an arbitrary universe, without
perfection, infinitude, or a characteristic restriction. Its provenance is the
existing coordinate-reduction and scalar-change constructions; it uses no
additional structural assertion about general unipotent groups.
