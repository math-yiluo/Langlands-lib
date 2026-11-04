# The general linear group scheme inside the affine space of its coordinates

Author: Worker 1076. The statements were specified together with Worker 1412.

This module places the Library's general linear group scheme
`Langlands.GroupScheme.GeneralLinear.groupScheme n R` inside the affine space
whose coordinates are its matrix entries and inverse matrix entries. It also
records how conjugation by an invertible matrix acts on these coordinates. All
declarations are in the namespace `Langlands.GroupScheme.GeneralLinear`. The
index `n : Type` carries `[Fintype n]` and `[DecidableEq n]`, as in the Library
module `Langlands.GroupScheme.GeneralLinear`.

## Provenance

This is internal helper material. It is not a result from the literature. It
supports the proof of the Library statement
`Langlands.GroupScheme.AutomorphicAction.AffineFiniteTypeCocycleModelStatement`
(task `909c8ce9`). That proof embeds a semidirect product into `GL_N` and then
into an affine space of coordinates, and it defines a conjugation action on
coefficient spaces. Every statement below is elementary matrix algebra, or it
follows directly from the coordinate-ring presentation in the Library module
`Langlands.GroupScheme.GeneralLinear`. There the coordinate ring is the
polynomial ring on the variables `Coordinate n` (`entry i j` and
`inverseEntry i j`) modulo the entries of `X Y - 1` and `Y X - 1`.

## The embedding into affine space

- `coordinateSpace n R` (an `abbrev`) is the affine space over `Spec R` with
  coordinate ring `MvPolynomial (Coordinate n) R`, written as
  `(algSpec R).obj (op (CommAlgCat.of R (MvPolynomial (Coordinate n) R)))`.
- `toSpace n R : (groupScheme n R).X ⟶ coordinateSpace n R` is the spectrum
  `(algSpec R).map (CommAlgCat.ofHom (quotient n R)).op` of the quotient map
  from the polynomial ring onto the coordinate ring of `GL_n`.
- `toSpace_left` states that its underlying scheme morphism is
  `Spec.map (CommRingCat.ofHom (quotient n R).toRingHom)`. This holds by
  definition.
- The instance `isClosedImmersion_toSpace` proves that `(toSpace n R).left` is
  a closed immersion, because the quotient map is surjective
  (`IsClosedImmersion.spec_of_surjective`).
- `toSpace_appTop` holds for every test scheme `T` over `Spec R`, affine or
  not, and every point `w : T ⟶ (groupScheme n R).X`. It states that pulling
  back the coordinate function `X κ` (viewed as a global section through
  `(Scheme.ΓSpecIso _).inv`) along `w ≫ toSpace n R` gives
  `values (pointsEquiv n R T w) κ`. That is the `(i, j)` entry of the matrix
  of `w` when `κ = entry i j`, and the `(i, j)` entry of its inverse when
  `κ = inverseEntry i j`. The proof uses the naturality of
  `Scheme.ΓSpecIso` and the Library lemmas `pointsEquiv_apply_apply` and
  `pointsEquiv_inv_apply`.

## Coordinate values

`values g : Coordinate n → S` is the Library's family of coordinate values of
an invertible matrix `g` (its entries and the entries of `g⁻¹`).

- `values_injective`: an invertible matrix is determined by its values.
- The published `values_map`, imported from
  `Dynamic.GeneralLinearStabilizer`: for a ring homomorphism `φ : S →+* S'`,
  `values (Matrix.GeneralLinearGroup.map φ g) = φ ∘ values g`.

The imported naturality lemma allows `S` and `S'` in independent universes and
in particular supplies the common-universe specialization used here.

## Conjugation of coordinates

Let `U : GL n S` and `v : Coordinate n → S`. Then `conjCoords U v` is the
family with the following entries. Here `M_v` is the matrix
`Matrix.of fun a b => v (entry a b)` and `N_v` is the matrix
`Matrix.of fun a b => v (inverseEntry a b)`:

- `conjCoords U v (entry i j) = (U * M_v * U⁻¹) i j`
  (`conjCoords_entry`);
- `conjCoords U v (inverseEntry i j) = (U * N_v * U⁻¹) i j`
  (`conjCoords_inverseEntry`).

So both coordinate matrices are conjugated by `U`. For conjugation itself, the
module proves:

- `values_conj`: `values (U * g * U⁻¹) = conjCoords U (values g)`. Since
  `(U g U⁻¹)⁻¹ = U g⁻¹ U⁻¹`, this formula covers the inverse entries too.
- `conjCoordsLinear U` is `conjCoords U` bundled as an `S`-linear map
  `(Coordinate n → S) →ₗ[S] (Coordinate n → S)`, and
  `conjCoordsLinear_apply` unfolds it. The consequences are
  `conjCoords_add`, `conjCoords_smul`, `conjCoords_zero` and
  `conjCoords_sum`, the last for sums over a `Finset`.
- `conjCoords_sum_mul`: for `a : ι → S` and `y : ι → Coordinate n → S`,
  conjugating `κ ↦ ∑ l ∈ s, a l * y l κ` gives
  `κ ↦ ∑ l ∈ s, a l * conjCoords U (y l) κ`.
- `conjCoords_map`: for a ring homomorphism `φ : S →+* S'`,
  `conjCoords (Matrix.GeneralLinearGroup.map φ U) (φ ∘ v) = φ ∘ conjCoords U v`.
- `conjCoords_one`: `conjCoords 1 v = v`.
- `conjCoords_mul`: `conjCoords (U * U') v = conjCoords U (conjCoords U' v)`.

In the conjugation section the rings `S` and `S'` may lie in arbitrary,
independent universes.
