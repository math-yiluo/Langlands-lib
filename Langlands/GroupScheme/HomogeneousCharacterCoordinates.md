# Coordinate form of covariant functions on homogeneous quotients

This internal construction compares two existing descriptions of character
covariance. The first is the space of actual global functions on `G` that are
right covariant on every scheme test, from `HomogeneousCharacterFinite`. The
second is the left-covariant coordinate subspace of `AffineInducedRegular`,
defined by a tensor equation in the coordinate coalgebra. Composition with the
group inversion identifies them, with the character replaced by its negative.
Hence properness of a supplied quotient makes the entire left-covariant
coordinate subspace of each character coordinate finite. Its provenance is the
Library's affine coordinate evaluation, the corepresented group-scheme
isomorphism, and the finite covariant-function theorem. The facts used are
standard; no external source is cited.

The field `k` and all schemes lie in the arbitrary universe `u`. Groups are
actual group schemes over `Spec k`.

## Inversion and coordinates

These declarations need only a group scheme `G`. `inversionAlgHom G` is
pullback of actual global functions `(algΓ k).obj G.X` along the inversion
morphism `ι[G.X]`. `appTop_inversionAlgHom` states that for every test
`g : T ⟶ G.X`, pulling back `inversionAlgHom G f` along `g` equals pulling
back `f` along `g⁻¹`. Applying it to `g = ι` and using `ι⁻¹ = 𝟙` proves
`inversionAlgHom_inversionAlgHom`, an involution. `inversionAlgEquiv` is the
resulting `k`-algebra automorphism.

The remaining declarations assume `G.X.left` affine. `algPoint G φ` is the
point of `G` over `algSpec B` determined by a `k`-algebra map `φ` from the
coordinate algebra `algebra G` to `B`. It applies `algSpec` to `φ`, then the
Library isomorphism `groupSchemeIso G`. `pointAlgebraHom_algPoint` evaluates
coordinates at this point. The result is `φ` followed by the counit of the
`algΓ ⊣ algSpec` adjunction. `counit_unop_injective` proves that this counit is
injective; it is an isomorphism because `algSpec` is fully faithful.

`globalAlgHom G` evaluates coordinates at the identity point `𝟙 G.X`.
`pointAlgebraHom_apply_eq` shows that evaluation at any test point `g` is the
pullback along `g` of this global function. `globalAlgHom_bijective` writes
`globalAlgHom G` as `algΓ` of an isomorphism followed by an isomorphic counit.
`globalAlgEquiv` is the resulting `k`-algebra isomorphism from coordinates to
actual global functions.

For a rational character `χ` of `G`, `characterCoordinate G χ` is the
coordinate whose global function is the actual unit `characterEval χ G.X (𝟙 _)`.
`pointAlgebraHom_characterCoordinate` proves that it evaluates to
`characterEval χ T g` on every test point `g`.

`coordinateEquiv G` is the `k`-algebra isomorphism from global functions to
coordinates given by inversion followed by the inverse of `globalAlgEquiv G`.
In words, the coordinate of `f` is the coordinate of `f ∘ ι`.
`pointAlgebraHom_coordinateEquiv` states that this coordinate evaluates at `g`
to the pullback of `f` along `g⁻¹`.

`characterEval_neg` holds over an arbitrary base scheme. It states that the
negative character takes the inverse unit value on each test point. Its proof
uses `characterEval_zsmul` with exponent `-1`.

## Covariance on every test

In this section `G → Spec k` and `H → Spec k` are affine, and `i : H ⟶ G` is
any morphism of group schemes. Let `χ` be any coordinate of `H`, not
necessarily a character. `leftCovariantSubspace i χ` contains the coordinates
`b` satisfying the tensor equation `(r ⊗ id)(Δ b) = χ ⊗ b`. Here `r` is
restriction along `i` and `Δ` is comultiplication. The Library already proves
that membership implies the equation

`b(i(h) · g) = χ(h) · b(g)`

on every scheme test with points `h` of `H` and `g` of `G`.
`mem_leftCovariantSubspace_of_points` proves the converse. It uses the
universal test `algSpec (algebra H ⊗[k] algebra G)` with the two points given
by `includeLeft` and `includeRight`. Evaluating the hypothesis there and
cancelling the injective counit recovers the tensor equation.
`mem_leftCovariantSubspace_iff_points` combines both directions.

`rightAct_mem_leftCovariantSubspace` restates the existing linear result for
these actual coordinate subspaces. Right translation `rightAct ψ`, for any
linear functional `ψ` on the coordinate algebra, preserves left covariance.
The coalgebra used is the one from the regular corepresentation, as in
`leftCovariantSubspace`.

## Right covariance and finiteness

Now also suppose `i` is monomorphic, `D` is a supplied `HomogeneousQuotient i`,
and `χ` is a rational character of `H`. Recall that
`rightCharacterCovariantSpace i D χ` is the entire space of actual global
functions `f` with `f(a · i(b)) = χ(b) · f(a)` on every scheme test.

`mem_rightCharacterCovariantSpace_iff_coordinate` proves:
`f` lies in this space exactly when `coordinateEquiv G f` lies in
`leftCovariantSubspace i (characterCoordinate H (-χ))`. Writing
`F = coordinateEquiv G f`, so that `F(g) = f(g⁻¹)`, the two conditions match by

`F(i(h) · g) = f(g⁻¹ · i(h⁻¹))` and `(-χ)(h) = χ(h⁻¹)`.

Each direction substitutes inverse test points.
`rightCovariantCoordinateEquiv i D χ` is the resulting `k`-linear
equivalence between these two entire subspaces. `rightCovariantCoordinateEquiv_apply`
records that it acts as `coordinateEquiv G` on underlying elements.

With `IsProper D.scheme.hom`,
`finite_leftCovariantSubspace_characterCoordinate` proves that the entire
subspace `leftCovariantSubspace i (characterCoordinate H χ)` is finite over
`k`. It applies `finite_rightCharacterCovariantSpace` to `-χ`, transports
across the equivalence, and simplifies `-(-χ) = χ`. No finite subspace is
chosen and the space may be zero.

## Scope

Properness of the supplied quotient remains an explicit hypothesis. The
construction does not choose a Borel subgroup or prove its properness. It does
not select a dominant character, construct a Steinberg module, or prove a
conjugation-map result.
