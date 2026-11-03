# Retracts of tori and kernels of homomorphisms with a section

This internal unit constructs an actual group-scheme retraction onto the kernel
of a homomorphism from a commutative group scheme when a group-scheme section
is supplied. It then identifies affine kernels of such maps from tori as tori.

First, any affine group-scheme retract of a split torus over a field is split.
Factor the retraction through the published closed split-torus image.
Its inclusion has a right inverse because the original retraction does, and
it is a monomorphism because it is closed. It is therefore an isomorphism,
so the retract is a split torus. For a possibly nonsplit torus, extend to
the splitting field already supplied by `IsTorus`, base-change the same
retraction equation, and apply the split case. This proves that an affine
group-scheme retract of a torus is a torus over the original field.

Over any base scheme `B` in universe `u`, take a commutative group scheme `T`,
a group scheme `D`, homomorphisms `q : T ⟶ D` and `s : D ⟶ T`, and the
section equation `s ≫ q = 𝟙 D`. For every test `V` and point `x` of `T`,
remove the section component:

`x ↦ x * (x ≫ q ≫ s)⁻¹`.

Its image under `q` is the identity. Commutativity of `T` makes this a group
homomorphism. The actual kernel point equivalence regards it as a kernel
point. Precomposition of points preserves this formula on every test
scheme, so `homOfPoints` produces `sectionKernelRetraction : T ⟶ kernel q`.
The displayed evaluation theorem retains the original formula after
composition with the canonical kernel inclusion. For an original kernel
point the removed component is the identity. Cancellation of the kernel
monomorphism therefore proves
`kernelι q ≫ sectionKernelRetraction q s hs = 𝟙 (kernel q)`.

Over any field, if this actual kernel is affine, the retract results now
show it is a split torus when `T` is split, and a torus when `T` is a torus.
Affineness of the kernel is an explicit hypothesis of these final theorems.
No smoothness, connectedness, solvability or algebraic closedness of the
base field is assumed. The section is a homomorphism of group schemes;
a section of underlying schemes alone does not meet the premise.

The provenance is internal: the published split-torus image factorization,
the categorical fact that a split epimorphism which is monic is invertible,
base change, the actual scheme-theoretic kernel and all-test group-valued
Yoneda. This supplies a geometric step for the intersection of a torus in
an external semidirect product with its normal factor. It does not prove
that such an intersection is maximal, construct a unipotent complement,
or establish the full semigroup ordered-product target.
