# Homomorphisms out of binary SL from big-cell relations

This internal module builds group homomorphisms out of the abstract group
`SL₂(E)` of determinant-one `2 × 2` matrices over a field `E`. The input is a
small set of relations in an arbitrary group `H`. It is plain algebra and has no
schemes or functors. Everything is in the namespace
`Langlands.GroupScheme.SpecialLinear.BinaryPresentation`. The field lives in
universe `u` and the target group in universe `v`. The descent theorem also has
a larger field in universe `w` and a larger group in universe `x`; all four are
independent.

## Matrices

- `upper t` is the transvection `1 + t E₀₁`, i.e. `[1, t; 0, 1]`.
  `lower t` is `1 + t E₁₀`, i.e. `[1, 0; t, 1]`. Both are Mathlib's
  `Matrix.SpecialLinearGroup.transvection`.
- `diag u`, for a unit `u`, is `diag(u, u⁻¹)`. It is the Library's
  `Root.contractingMatrix` at the positions `0 ≠ 1`.
- `cellMatrix b u a = lower b * diag u * upper a`. `coe_cellMatrix` gives its
  entries as `[u, u a; b u, b u a + u⁻¹]`.
- `eq_cellMatrix`: a matrix `g` with `g₀₀ ≠ 0` equals
  `cellMatrix (g₁₀/g₀₀) g₀₀ (g₀₁/g₀₀)`.
- `cellMatrix_mul` is the product rule for two cell matrices. Suppose
  `v = 1 + a b'` is a unit. Then the product of `cellMatrix b u a` and
  `cellMatrix b' u' a'` is
  `cellMatrix (b + u⁻² v⁻¹ b') (u v u') (u'⁻² v⁻¹ a + a')`.
- `weylMatrix_eq`: the Library's `BinaryUpper.weylMatrix` (the matrix
  `[0, -1; 1, 0]`) equals `upper (-1) * lower 1 * upper (-1)`.
- `exists_affine_ne_zero` assumes that `E` has, for any two values, a third
  value different from both (a field with at least three elements). Given two
  affine functions `e ↦ p + q e`, neither identically zero, it finds a common
  point where both are nonzero. `exists_ne_ne_of_infinite` gives that
  hypothesis for every infinite field.

## Relations

`BigCellRelations E H` is a structure with these fields:

- maps `x y : E → H` that are additive: `x (a + a') = x a * x a'`, and the same
  for `y`;
- a monoid homomorphism `h : Eˣ →* H`;
- the torus laws `h(u) x(a) h(u)⁻¹ = x(u² a)` and
  `h(u) y(b) h(u)⁻¹ = y(u⁻² b)`;
- the big-cell relation: whenever `u` is a unit with `u = 1 + a b`,
  `x(a) y(b) = y(u⁻¹ b) h(u) x(u⁻¹ a)`.

`matrixRelations E : BigCellRelations E SL₂(E)` shows that the matrices
satisfy these relations: `x = upper`, `y = lower`, and `h` is the Library's
`Root.contractingMatrixHom`, so `h u = diag u`. Here the big-cell relation is
the matrix identity
`upper a * lower b = lower (u⁻¹ b) * diag u * upper (u⁻¹ a)`. It has the same
shape as the split rank-one relation of the Library's
`HasRootRankOneRelations`.

## The lift

For `R : BigCellRelations E H`:

- `R.cell b u a = y(b) h(u) x(a)`. `cell_mul_cell` shows that these values
  multiply by the same rule as `cellMatrix_mul`. The proof uses the big-cell
  relation once and each torus law once.
- `R.cellValue g` is `R.cell (g₁₀/g₀₀) g₀₀ (g₀₁/g₀₀)` when `g₀₀ ≠ 0`, and `1`
  otherwise. `cellValue_mul` says it is multiplicative whenever `g`, `g'` and
  `g g'` all have nonzero top-left entry.
- `R.liftFun g` is `cellValue (g * lower c) * y(-c)` for a chosen `c` with
  `(g * lower c)₀₀ ≠ 0`. Such a `c` always exists because the first row of
  `g` is nonzero. `liftFun_eq` shows that every admissible `c` gives the same
  value.
- `R.lift hE : SL₂(E) →* H` is `liftFun` as a homomorphism, where `hE` is the
  three-element hypothesis above. To prove `liftFun (g ω) = liftFun g *
  cellValue ω`, the argument multiplies on the right by `lower e`. Here `e` is
  chosen with `exists_affine_ne_zero` so that the top-left entries of
  `ω * lower e` and `g ω * lower e` are both nonzero. Every `g'` is a big-cell
  matrix times a lower unipotent, so this gives multiplicativity.
- `lift_upper`, `lift_lower` and `lift_diag` say that the lift sends `upper t`,
  `lower t` and `diag u` to `x t`, `y t` and `h u`. `lift_weylMatrix` says it
  sends the Weyl matrix to `x(-1) y(1) x(-1)`.

## Uniqueness and descent

- `hom_ext`: two homomorphisms `SL₂(E) →* H` are equal if they agree on all
  `upper t` and all `lower t`. The proof uses Mathlib's
  `Matrix.SL2.transvection_induction`, valid over every field.
- `lift_matrixRelations`: over a field with at least three elements, the lift
  of `matrixRelations E` is the identity homomorphism of `SL₂(E)`.
- `map_upper`, `map_lower` and `map_diag`: under a ring map `ι : E →+* E'`, the
  induced map on `SL₂` sends `upper t`, `lower t` and `diag u` to
  `upper (ι t)`, `lower (ι t)` and `diag (ι u)`.
- `exists_hom_of_embedding` covers small fields, including `F₂`, where `lift`
  does not apply. Take relations `R'` over a field `E'` that satisfies the
  three-element hypothesis, a ring map `ι : E →+* E'`, and an injective
  homomorphism `j : H →* H'`. Let `x y : E → H` and `h : Eˣ → H` be functions
  with `j ∘ x = R'.x ∘ ι`, `j ∘ y = R'.y ∘ ι` and `j ∘ h = R'.h ∘ ι`. Then there
  is a homomorphism `φ : SL₂(E) →* H` sending `upper t`, `lower t` and `diag u`
  to `x t`, `y t` and `h u`. It is `R'.lift` composed with `SL₂(ι)`. This lands
  in the image of `j` because `SL₂(E)` is generated by transvections, and is
  then pulled back through `j`. The original field `E` needs no size
  condition.

`lift` needs the three-element hypothesis. The module proves nothing about a
two-element field from relations over that field alone. An informal remark,
not formalized here: over `F₂` the relations hold for two generating
reflections of the infinite dihedral group, so they cannot suffice there. A
typical use of the descent theorem: `E'` is the rational function field
`E(t)`, which is infinite, and `H ⊆ H'` are the points of an algebraic group
over `E` and over `E(t)`.

## Provenance

The construction is internal. It is the standard "big cell" method for
presenting `SL₂` over a field: the Bruhat cell `U⁻ T U` is dense, and a
multiplicative function on it extends uniquely. Here this is done by explicit
matrix arithmetic. The module proves every step in Lean. It cites no
literature theorem and uses no hypotheses beyond the stated relations and the
three-element condition.
