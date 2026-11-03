# Fixed-subspace coefficient extraction

This internal helper derives fixed-subspace invariance from the published
all-test normality predicate. It uses matrix algebra, the actual relative
global-section algebra isomorphism, tensor products, and linear dual
separation. No external structural theorem on algebraic groups is used.

The imported `UnipotentMatrixCriterion.scalarMap_affine` identifies the base-ring map on an affine test with the
inverse affine global-section comparison applied to its algebra map.
`affine_fixed_iff` uses this comparison to translate point-matrix fixedness
to the equation in the test algebra. `IsFixedVector.affine` specializes the
all-test fixed-vector predicate. `isFixedVector_iff_affine_model` shows that,
given an isomorphism from an affine scheme to the group scheme, one equation
at that model point implies fixedness on every scheme test. Its proof
pulls the equation back along the test point followed by the model inverse.
These comparison lemmas work over every commutative base ring.

For commutative algebras `A` and `B` over a field `k`, `tensorCoefficient`
applies a `k`-linear functional on `A` to the left factor of `A ⊗[k] B`.
`fixed_tensor_coefficients` starts with a matrix over `B` and a vector over
`A` whose images satisfy a fixed-vector equation in this tensor algebra.
Applying `tensorCoefficient` to each equation gives a fixed-vector equation
over `B` for every extracted coefficient.

Let `i : H → G` have normal all-test image, let `ρ` be a finite matrix
representation of `G`, and let `v` be fixed by its restriction to `H`.
`normal_fixed_affine` proves that, on any affine test, every `H`-point fixes
the translate `ρ(g)v` for every `G`-point `g` on that same test. Normality
lifts `g⁻¹ h g` to an actual `H`-point. Fixedness at this point and the group
matrix laws prove the equation.

`normal_fixed_coefficient` additionally takes a supplied affine model of `H`.
For an `A`-point `g` of `G` and every linear functional `ℓ : A → k`,
the coefficient vector `ℓ(ρ(g)v)` is fixed by `H` on all scheme tests.
The proof applies `normal_fixed_affine` after extending `g` and the model
point of `H` to `A ⊗[k] B`, then uses `fixed_tensor_coefficients` and the
affine-model criterion. There is no assumption that rational points are
dense, and the field can be finite or imperfect.

`linearFunctional_mulVec` commutes coefficient extraction with a matrix
over `k`. `projection_mulVec_eq_of_coefficients` consequently detects a
projection equation over `A` from all its extracted equations over `k`,
using the separating linear dual of the `k`-vector space `A`.

`normal_fixed_coordinates_affine` takes coordinate matrices `B` and `C`,
requires that every column of `B` is fixed by `H`, and requires that `B C`
fixes every `H`-fixed vector. For every affine `G`-point it proves the
coordinate stability equation `ρ(g)B = B(Cρ(g)B)`. It applies
`normal_fixed_coefficient` to the columns and the preceding projection
criterion. No retraction equation `C B = 1` is needed for this particular
invariance result.

Finally, `isStableCoordinates_of_affine_model` takes an affine model of a
group `J` and the stability equation at that model point. Mapping matrix
entries through the affine section isomorphism and then pulling back along
every test point proves the published `IsStableCoordinates` predicate on
all scheme tests. Together these helpers supply the invariance step for
restriction to a normal subgroup's fixed subspace; basis choice, the actual
restriction construction, and product unipotence are separate steps.
