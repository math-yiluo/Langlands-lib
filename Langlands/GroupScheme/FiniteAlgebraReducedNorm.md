# Actual polynomial norm characters and norm-one algebra groups

Let `k`, `L`, and `A` lie in arbitrary universe `u`, with `k`, `L` fields
and `A` an associative unital `k`-algebra. Fix a finite basis
`b : Basis (Fin n) k A`, a finite Galois extension `L/k`, and an actual
splitting chart
`e : L ⊗[k] A ≃ₐ[L] Matrix I I L`.
The finite nonempty matrix index type `I` may lie in a separate universe.
This internal unit realizes the existing descended determinant polynomial
as an actual character of `FiniteAlgebraUnits.groupScheme b` and
constructs its actual norm-one group scheme.

The chart is a visible input throughout. The existing algebraic construction
`ReducedNorm.normFromGalois` evaluates the descended determinant polynomial
on every commutative `k`-algebra and proves its multiplicativity and
naturality. Its operation on units is `normFromGaloisUnits`;
its pointwise kernel is `normFromGaloisOne`.
The present unit uses those proved operations, with no added
multiplicativity or naturality premise.

For every scheme `T` over `Spec k`, `normPoints b e T` composes the actual
unit-group point equivalence with the polynomial norm on the actual
relative global-section tensor algebra, then applies the inverse
`Gm` point equivalence. Polynomial naturality and actual section pullback
prove `normPoints_naturality`. The group-valued Yoneda constructor gives
the actual group-scheme homomorphism `norm b e`.
The theorem `norm_points` computes it on every test scheme.

The theorem `norm_affine_points` identifies the same actual character on
every commutative affine coefficient algebra `R` with the original
`normFromGaloisUnits b e R`. The proof transports the all-test identity
along `Corepresented.affineSectionsIso R`.
The source transport is the existing corepresented affine comparison;
polynomial naturality handles the norm; the corresponding ring map is the
usual global-sections/spectrum isomorphism used by the affine `Gm`
comparison. Thus this formula refers to the original polynomial operation.

The group `normOne b e` is the actual group-scheme kernel of `norm b e`;
`normOneι b e` is its canonical inclusion into the algebra-unit group.
The separated target `Gm` makes this inclusion a closed immersion.
Its source is affine because it is closed in the affine unit group, and
its structure morphism is locally of finite type by composition of that
closed immersion with the smooth unit-group structure morphism.
This unit makes no smoothness or connectedness assertion for the kernel.

The multiplicative equivalence `normOnePointsEquiv b e T` identifies actual
kernel points on any relative test scheme with exactly the existing
polynomial norm-one subgroup of tensor units over its relative section
algebra. It combines the actual kernel point equivalence with the proved
unit and norm formulas.
The definition `normOneUnitsRestrict` is the corresponding actual
tensor coefficient pullback restricted to the norm-one subgroup;
`normOnePointsEquiv_naturality` proves naturality on all test schemes.

The equivalence `normOneAffinePointsEquiv b e R` similarly identifies actual
affine kernel points with `ReducedNorm.normFromGaloisOne b e R`.
Specializing the canonical rational/coefficient comparison gives
`normOneRationalPointsEquiv b e`, whose target is
`ReducedNorm.normFromGaloisOne b e k`, a subgroup of `(k ⊗[k] A)ˣ`.
The accompanying value formulas respect the actual inclusion into the
unit group.

The provenance is internal composition of the proved polynomial norm,
the actual finite-algebra unit group, all-test and affine point
comparisons, group-valued Yoneda, and the group-scheme kernel.
It retains the finite Galois chart and basis explicitly. Construction of
an unconditional reduced norm for arbitrary central simple algebras,
identification across all splitting choices, elementary-root geometry,
local SK1 and the unrestricted local Kneser–Tits theorem are separate
obligations.
