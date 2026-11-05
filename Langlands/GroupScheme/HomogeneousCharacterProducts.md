# Products of covariant functions and the induced regular representation

This internal construction adds three things to the character-covariance API
of `HomogeneousCharacterFinite` and `HomogeneousCharacterCoordinates`. First,
right-covariant functions multiply: the product of two covariant functions is
covariant for the sum of their characters. Second, character coordinates turn
sums of characters into products. Third, on a supplied proper quotient, the
entire finite left-covariant coordinate subspace of a character coordinate
carries an actual matrix representation of `G` by right translation. Its
provenance is the Library's rational-character evaluation, the finiteness
theorem of `HomogeneousCharacterCoordinates`, and the Library's finite regular
representation of an affine group. The facts used are standard; no external
source is cited.

Products of left-covariant coordinates and the equivariance of coordinate
multiplication are not treated here; they are the subject of a separate
contribution, the module `Langlands.GroupScheme.Reductive.CovariantProducts`.

The field `k` and all schemes lie in the arbitrary universe `u`.

## Products of right-covariant functions

These three results hold over an arbitrary base scheme `S`, for group schemes
`G` and `H` over `S` and any morphism `i : H ⟶ G`. They concern the predicate
`IsRightCharacterCovariant i χ f` of `HomogeneousCharacterLineBundle`. It
requires `(a * (b ≫ i)).appTop f = χ(b) * a.appTop f` for every test scheme
`T` and every pair of points `a : T ⟶ G.X` and `b : T ⟶ H.X`.

- `IsRightCharacterCovariant.mul`: if `f` is covariant for `χ` and `g` for
  `ψ`, then `f * g` is covariant for `χ + ψ`. The proof uses that pullback of
  global functions is a ring map. It then applies `characterEval_add`, which
  says the value of `χ + ψ` is the product of the values.
- `isRightCharacterCovariant_one`: the constant function `1` is covariant for
  the zero character, by `characterEval_zero`.
- `IsRightCharacterCovariant.pow`: if `f` is covariant for `χ`, then `f ^ n`
  is covariant for `n • χ`, by induction on `n`.

Now let `G` and `H` be group schemes over `Spec k`, with `i : H ⟶ G`
monomorphic on underlying schemes and `D` a supplied homogeneous quotient. For
these data `rightCharacterCovariantSpace i D χ` is the entire `k`-subspace of
covariant global functions on `G`. `mul_mem_rightCharacterCovariantSpace`,
`one_mem_rightCharacterCovariantSpace` and
`pow_mem_rightCharacterCovariantSpace` restate the three results for these
subspaces. `rightCharacterCovariantMul i D χ ψ` is multiplication as a
`k`-bilinear map from the spaces for `χ` and `ψ` to the space for `χ + ψ`.
`rightCharacterCovariantMul_apply` states that its underlying function is the
product.

## Character coordinates

Let `G` be a group scheme over `Spec k` whose underlying scheme is affine.
`characterCoordinate G χ` is the coordinate in `algebra G` of the actual unit
function of a rational character `χ`. `pointAlgebraHom_id_apply` records that
evaluation at the identity point `𝟙 G.X` is the map `globalAlgHom G` to actual
global functions; this holds by definition.

- `characterCoordinate_add`: the coordinate of `χ + ψ` is the product of the
  coordinates of `χ` and `ψ`.
- `characterCoordinate_zero`: the coordinate of the zero character is `1`.
- `characterCoordinate_nsmul`: the coordinate of `n • χ` is the `n`-th power
  of the coordinate of `χ`.

The first two are proved by injectivity of `globalAlgHom G`, which is
`globalAlgHom_bijective`. Both sides are evaluated at the identity point by
`pointAlgebraHom_characterCoordinate`, and then `characterEval_add` or
`characterEval_zero` applies. The third follows by induction.

## The induced representation

In the last section, `i` is monomorphic on underlying schemes,
`G → Spec k` and `H → Spec k` are affine, and the structure morphism of `D` is
proper.

- `inducedSpace i χ` abbreviates the entire subspace
  `leftCovariantSubspace i (characterCoordinate H χ)`. It does not involve `D`.
  `rightCovariantCoordinateEquiv i D (-χ)` from
  `HomogeneousCharacterCoordinates` identifies it with the entire space of
  functions right covariant for `-χ`.
- `inducedBasis i D χ` is the basis `Module.finBasis` of `inducedSpace i χ`,
  indexed by `Fin` of its `finrank`. It uses the finiteness theorem
  `finite_leftCovariantSubspace_characterCoordinate`, which needs properness.
- `inducedRepresentation i D χ` is the Library's
  `Chevalley.affineRegularRepresentation G` on `inducedSpace i χ` with
  `inducedBasis i D χ`. Its stability hypothesis is that each right action
  `rightAct ψ`, for a linear form `ψ` on `algebra G`, preserves the subspace.
  This is `rightAct_mem_leftCovariantSubspace`. The result is a
  `MatrixRepresentation G` indexed by `Fin (finrank k (inducedSpace i χ))`.
  No finite subspace is substituted for the entire space.
- `inducedRepresentation_pointMatrix` states that at every test point `g` the
  `(a, b)` entry of its matrix is the evaluation at `g` of the corresponding
  entry of `Chevalley.subspaceMatrix` for the chosen basis.
- `inducedRepresentation_mul_basis` states, for test points `g` and `h`, that
  basis vector `b` evaluated at `g * h` equals the sum over `a` of basis vector
  `a` at `g` times the `(a, b)` entry of the matrix at `h`.

The last two results restate `Chevalley.affineRegularRepresentation_pointMatrix`
and `Chevalley.affineRegularRepresentation_mul_basis`.

## Scope

The homogeneous quotient `D` and its properness are hypotheses. Nothing here
chooses a Borel subgroup, proves properness of a Borel quotient, or selects a
dominant character. Nothing here shows that multiplication intertwines the
induced representations. Irreducibility, self-duality and Steinberg modules are
not treated, and the conjugation-map statement is not proved.
