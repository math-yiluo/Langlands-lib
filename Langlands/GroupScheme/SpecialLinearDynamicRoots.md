# Explicit contractions of actual coordinate-root maps in split SLₙ

For an arbitrary finite index type `n : Type`, commutative ring
`R : CommRingCat.{u}` and distinct indices `i`, `j`, this internal construction
gives the actual cocharacter
`SpecialLinear.Root.cocharacter R hij : Gm ⟶ SpecialLinear.groupScheme n R`.
Its matrix on every relative test scheme is diagonal, with entries `t` at
`i`, `t⁻¹` at `j` and `1` elsewhere. There is no field or characteristic
restriction.

The definition `contractingMatrix hij t` gives this diagonal matrix over
any commutative coefficient ring. Its determinant is one because the two
nonidentity diagonal factors multiply to one. The definition
`contractingMatrixHom` proves multiplicativity in the unit `t`, and
`map_contractingMatrix` verifies compatibility with every coefficient-ring
homomorphism. The actual global-section point equivalences for `Gm` and
SLₙ therefore give the natural group homomorphism `cocharacterPoints` on
each test scheme. The existing group-valued Yoneda constructor yields
`cocharacter`; `pointsEquiv_cocharacter` verifies its diagonal formula.

The theorem `contractingMatrix_conjugate` proves that conjugation by this
matrix sends the `(i,j)` transvection with coefficient `x` to the
transvection with coefficient `t²x`. The proof compares the two products
`D(t) Tᵢⱼ(x)` and `Tᵢⱼ(t²x) D(t)` entrywise, using diagonal multiplication
and unit cancellation.

For any actual additive-root point `x` on a scheme `T` over `Spec R`,
`contraction R hij x` is a point of the actual SLₙ scheme on `T × A¹`.
Its matrix is the `(i,j)` transvection with coefficient `s²x`, with both
coordinates pulled back along the appropriate projections.
The point is constructed through the existing SLₙ point equivalence, so
it works for arbitrary relative test schemes.
The theorem `pointsEquiv_comp_contraction` computes its matrix after any
change of test scheme.

The theorem `contraction_isOrbitExtension` restricts this curve along
the actual inclusion `Gm → A¹`. The affine-line coordinate becomes the
underlying global unit, so the matrix conjugation formula identifies this
restriction with the exact conjugation orbit in `Dynamic.IsOrbitExtension`.
The theorem `contraction_evalZero` restricts the same curve along the actual
zero section. Its coefficient becomes zero and its value is the identity.
Together these are the witnesses in the definition of `Dynamic.unipotent`.
Thus `root_range_le_dynamicUnipotent` proves the all-test subgroup-functor
inclusion of the actual `rootMap R hij` image into the dynamic unipotent
subgroup for `cocharacter R hij`.

The provenance is internal: this extends the explicit binary construction
in `SpecialLinearBinaryDynamicRoots` to any pair of positions in a finite
matrix. It uses the actual coordinate-root maps in `SpecialLinearRootGroups`,
the existing all-test point equivalences and the definitions of dynamic
orbit extension and evaluation at zero. It does not identify coordinate-root
images with arbitrary relative-root functors, construct split models of
general factors, or prove the unrestricted local Kneser–Tits theorem.
