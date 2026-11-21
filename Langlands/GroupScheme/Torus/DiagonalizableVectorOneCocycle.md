# Linear vector one-cocycles on diagonalizable groups are coboundaries

Worker 386. This is an internal construction over a field `k` in an arbitrary universe
`u`. It is the one-cocycle analogue of the two-cocycle averaging in
`Torus.DiagonalizableVectorCocycle`, and a helper for the conjugacy of sections in
trigonalizable groups (Task 7806).

## Setting

`Λ` is any abelian group and `D = D(Λ)` is the actual diagonalizable group scheme
`Diagonalizable.groupScheme (CommRingCat.of k) Λ`. No finite generation, torsion-freeness,
smoothness or characteristic assumption is made. The coefficient group `V` is a group
scheme over `Spec k` that is affine over the base, with an automorphic action `a` of `D`
and vector coordinates `e`: for every test scheme `T`, a multiplicative equivalence from
`T ⟶ V.X` to `Multiplicative (Fin d → Γ(T, ⊤))`. The coordinates satisfy
`IsLinearVectorCoordinates a e`: they are natural, and the action is linear in them.
The cocycle `c` is an actual relative cocycle `a.Cocycle T₀` over the base
`T₀ = Over.mk (𝟙 (Spec k))`, that is, a morphism `T₀ × D ⟶ V` with
`c(h h') = c(h) · h(c(h'))` on every test scheme.

## Statements

- `cocycle_eq_coboundary`: `c = a.coboundary (conjugator Λ a e c)`.
- `exists_coboundary`: there is a rational point `v : T₀ ⟶ V.X` with
  `c = a.coboundary v`. By the Library convention, the coboundary of `v` is the cocycle
  `h ↦ v · h(v)⁻¹`.

The auxiliary definitions are `coordinates` (the coordinate vector of the cocycle at an
affine test point of `D`), `constant` (the degree-zero coefficient of the coordinates at
the universal point of `D`, a vector in `k^d`) and `conjugator` (the rational point of `V`
with coordinates `constant`).

## Proof

An `A`-valued point of `D` corresponds to a homomorphism from `Λ` to `Aˣ`.
The universal point with coefficients in `A[Λ]` sends each `λ` to the basis unit
`e_λ`. The proof takes the degree-zero coefficient, as in
`DiagonalizableVectorCocycle`.

- `coordinates_naturality`: cocycle coordinates commute with extension of coefficients,
  by naturality of affine evaluation and of the coordinates.
- `coeff_zero_point`: hence the degree-zero coefficient of the coordinates at the
  extended universal point `Averaging.point` over `A` is the scalar extension of
  `constant`.
- `coordinates_eq_constant_sub_action`: for every affine point `t` over `A`,
  `coordinates t = constant − t · constant`, in coordinates. This is the cocycle identity
  at `t' · P`, where `t'` is `t` viewed over `A[Λ]` and `P` is the extended universal
  point, after taking degree-zero coefficients. The left side is unchanged by the
  translation `P ↦ t' · P` (`Averaging.translation_point`, `coeff_zero_translation`), so
  it is `constant`. On the right, the first term is constant in the group-algebra
  variable and gives `coordinates t` (`coeff_zero_coefficientInclusion`). The second term
  is `t'` acting on `c(P)`; linearity of the action lets the degree-zero coefficient pass
  through it (`coeff_zero_act`), giving `t · constant`.
- `conjugator_coordinates`: the conjugator, pulled back to an affine test, has
  coordinates the scalar extension of `constant`.
- `cocycle_eq_coboundary`: both cocycles agree at every affine test point
  (`Cocycle.affineEval_ext`, which uses that `D` is affine), because the coboundary of
  the conjugator has coordinates `constant − t · constant` too.

## Provenance

Internal. The coefficient method and the averaging lemmas are those of
`Torus.DiagonalizableVectorCocycle`, `Torus.DiagonalizableVectorExtension` and
`Diagonalizable.Averaging`. Mathematically this is the vanishing of the first cohomology
of a diagonalizable group with coefficients in a linear representation, because such
representations are semisimple (direct sums of characters).
