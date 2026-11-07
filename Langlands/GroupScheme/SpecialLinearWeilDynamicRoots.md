# Actual contractions of Weil-restricted special-linear roots

Let `E/F` be a finite field extension, with both fields in arbitrary universe
`u`, and let `n : Type` be a finite matrix index type. For each pair of
distinct indices `i`, `j`, this internal construction gives an actual
`F`-cocharacter of the existing group scheme `Res(E/F) SLₙ` and proves
that it contracts the actual restricted coordinate-root morphism from
`SpecialLinearWeilRootGroups`. The result holds on every relative test
scheme, with no affineness condition on the test, separability condition
on the extension, or characteristic restriction.

The construction uses the actual tensor point models from
`SpecialLinearWeilPointModels`. For a test scheme `T`, `includeSections F E T`
is the ring homomorphism from its global sections into
`E ⊗[F] Γ(T, 𝒪_T)` through the right tensor factor. The algebra structure
is the relative one supplied by `sectionAlgebra F T`.
The theorem `tensorMap_includeSections` computes its pullback under any
actual change of test scheme. The theorem `tensorMap_comp` verifies
composition of these tensor coefficient pullbacks.

The point homomorphism `cocharacterPoints F E hij T` first identifies a
`Gm` point with its actual global unit `t`, maps the unit through
`includeSections`, and takes the determinant-one diagonal matrix with
entries `t`, `t⁻¹` at the two selected positions and `1` elsewhere.
The inverse of `tensorMatrixEquiv` makes this an actual point of the
restricted group. Matrix naturality proves that these homomorphisms are
natural in `T`. The existing group-valued Yoneda constructor gives the
actual group-scheme morphism `cocharacter F E hij`.
The theorem `tensorMatrixEquiv_cocharacter` records its matrix on every
test scheme.

For an actual point `x` of the restricted additive root on `T`,
`contraction F E hij x` is an actual point of the restricted special-linear
group on `T × A¹`. Its tensor matrix is the `(i,j)` transvection with
coefficient

`includeSections(s)² * tensorMap(projectionToT)(coordinate(x))`,

where `s` is the actual affine-line coordinate pulled back along the
second projection. The curve is constructed with the inverse tensor
matrix equivalence. The theorem `tensorMatrixEquiv_comp_contraction`
computes its pullback along every test map.

Restricting along the actual inclusion `Gm → A¹` turns `s` into the
underlying global unit. The proved diagonal conjugation identity from
`SpecialLinearDynamicRoots` then identifies the restricted curve with the
exact conjugation orbit; this is `contraction_isOrbitExtension`.
Restricting along the actual zero section makes its coefficient zero and
therefore gives the identity matrix; this is `contraction_evalZero`.
These two identities supply the witnesses in `Dynamic.unipotent`.
Consequently `root_range_le_dynamicUnipotent` proves the all-test
subgroup-functor inclusion

`range(rootMap F E hij) ≤ Dynamic.unipotent (cocharacter F E hij)`.

The provenance is internal: the construction combines the existing
actual Weil restriction, its proved tensor point comparisons, the actual
restricted root morphism, the explicit determinant-one diagonal matrices,
and the definitions of orbit extension and evaluation at zero. It does
not identify restricted coordinate-root images with arbitrary relative-root
functors or parabolic radicals, construct models of general factors, or
prove the unrestricted local Kneser–Tits theorem.
