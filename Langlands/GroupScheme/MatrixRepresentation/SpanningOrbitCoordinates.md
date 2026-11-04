# A spanning representation with the same coordinate-line stabilizer

Author: Worker 967.

This internal module builds, from a finite matrix representation `ρ` of a smooth
group scheme over an algebraically closed field `k` and a coordinate vector `e_j`,
a second finite matrix representation `σ` with a coordinate vector `e_s` such
that:

1. on every relative scheme test, `σ(x) e_s` is a unit multiple of `e_s` exactly
   when `ρ(x) e_j` is a unit multiple of `e_j`;
2. the vectors `σ(g) e_s`, for `g` a rational point of `G`, span `k^m` over `k`.

This is the reduction asked for by the Library statement
`Langlands.GroupScheme.SpanningLineStabilizerStatement`. The module does not
state or prove that proposition. Its main theorem,
`exists_spanning_sameCoordinateLineStabilizer`, has the same conclusion in a
slightly different form, and a proof of `SpanningLineStabilizerStatement` is
obtained by unpacking it. In the proof of Theorem 17.65 of Milne, *Algebraic
Groups* (2017), the projective embedding `G/B → P(V)` is supposed nondegenerate,
which is used in the form that the vectors `g v` generate `V`. This module
supplies that property for the Library's representations. The construction and
its proof are internal; no literature result is used.

The construction uses the Library's `exists_rationalOrbit_coordinates` (module
`Langlands.GroupScheme.MatrixRepresentation.OrbitCoordinates`). It gives
coordinates for the `k`-span `W` of the rational orbit of `e_j`, consisting of
an inclusion matrix `B : n × Fin d` and a retraction `C : Fin d × n` such that:

- `C * B = 1`;
- every column of `B` has the form `ρ(g) e_j` for a rational point `g`;
- the coordinates are stable on every test (`IsStableCoordinates`);
- some column `s` of `B` is `e_j`.

The representation `σ` is the Library's restriction `restrictCoordinates` of `ρ`
to these coordinates. The material below proves the two properties of `σ`.

## Notation

`R` is a commutative ring and `G` a group scheme over `Spec R`. A test is an
object `Z` of `Over (Spec R)` and a test point is a morphism `x : Z ⟶ G.X`.
`ρ.pointMatrix Z x` is the invertible matrix of `ρ` at `x`, with entries in the
global-section ring `Γ(Z.left, ⊤)`. `scalarMap Z : R → Γ(Z.left, ⊤)` is the
structure map, and `B.map (scalarMap Z)` is `B` with its entries pushed to the
test. `Pi.single j 1` is the standard basis vector `e_j`. `*ᵥ` is matrix-vector
multiplication.

## The stabilizer comparison

`SameCoordinateLineStabilizer ρ j σ s` (a `Prop`) says: for every test `Z` and
every `x : Z ⟶ G.X`, there is a unit `c` of `Γ(Z.left, ⊤)` with
`σ(x) e_s = c • e_s` if and only if there is a unit `c` of `Γ(Z.left, ⊤)` with
`ρ(x) e_j = c • e_j`. Here `ρ : MatrixRepresentation G n`,
`σ : MatrixRepresentation G m` and `j : n`, `s : m`. The two sides are the
unit-scalar stabilizers of the two coordinate lines.

## General ring

Fix `ρ : MatrixRepresentation G n`, matrices `B : Matrix n m R` and
`C : Matrix m n R` with `hCB : C * B = 1`, and `hstable : ρ.IsStableCoordinates B C`.

- `mulVec_single_one_eq_column`: for a matrix `B : Matrix n m α` over any
  non-associative semiring `α`, `B *ᵥ e_s` is the column `fun r => B r s`.
  Mathlib's `Matrix.mulVec_single_one` gives this in the transpose form.
- `restrictCoordinates_pointMatrix_coe`: on every test `T` and point `x`, the
  matrix of the restriction is `C_T * ρ(x) * B_T`, where `C_T` and `B_T` are `C`
  and `B` pushed to `T`. This is the Library's `restrictCoordinates_pointMatrix`
  with the units coercion unfolded.
- `rationalMatrix_restrictCoordinates`: for a rational point `g`, the rational
  matrix of the restriction is `C * ρ(g) * B` over `R`. The proof reads both
  sides through `Scheme.ΓSpecIso R`, which carries the pushed matrices `C_T`,
  `B_T` on the trivial test back to `C`, `B`.
- `sameCoordinateLineStabilizer_restrictCoordinates`: if additionally column `s`
  of `B` is `e_j`, then
  `SameCoordinateLineStabilizer ρ j (restrictCoordinates ρ B C hCB hstable) s`.
  Proof, at a test `Z` and point `x`, with `σ(x) = C_Z ρ(x) B_Z`:
  - `B_Z e_s = e_j`, by the column hypothesis and `scalarMap_single`, and so
    `C_Z e_j = C_Z B_Z e_s = e_s`, since `C_Z B_Z = 1`.
  - If `σ(x) e_s = c • e_s`, then the Library's intertwining identity
    `restrictCoordinates_intertwines`, `ρ(x) B_Z = B_Z σ(x)`, gives
    `ρ(x) e_j = ρ(x) B_Z e_s = B_Z σ(x) e_s = c • B_Z e_s = c • e_j`.
  - If `ρ(x) e_j = c • e_j`, then
    `σ(x) e_s = C_Z ρ(x) B_Z e_s = C_Z ρ(x) e_j = c • C_Z e_j = c • e_s`.

  The same unit `c` works in both directions.

## Over a field

Here `k` is a field and `G` a group scheme over `Spec k`.

- `span_restrictCoordinates_orbit_eq_top`: let `B`, `C`, `hCB` and `hstable` be
  as above over `k`, and let column `s` of `B` be `e_j`. Suppose also that every
  column `t` of `B` equals `ρ(g) e_j` for some rational point `g`. Then the
  rational orbit vectors `σ(g) e_s` of the restriction `σ` span `k^m`. Proof: it
  suffices that each basis vector `e_t` lies in the span. Choose `g` with column
  `t` of `B` equal to `ρ(g) e_j`. Then
  `σ(g) e_s = C ρ(g) B e_s = C ρ(g) e_j = C B e_t = e_t`, using
  `rationalMatrix_restrictCoordinates` and `C * B = 1`.
- `exists_spanning_sameCoordinateLineStabilizer`: let `k` be algebraically
  closed, `G.X.hom` smooth, `ρ : MatrixRepresentation G n` and `j : n`. Then there
  are `d : ℕ`, `s : Fin (d + 1)` and `σ : MatrixRepresentation G (Fin (d + 1))`
  with `SameCoordinateLineStabilizer ρ j σ s` and with the rational orbit vectors
  `σ(g) e_s` spanning `k^(d+1)`. Proof:
  - Smoothness over a field gives that `G.X.left` is reduced (Library
    `SmoothReducedProof.isReduced_of_smooth_over_field`) and that `G.X.hom` is
    locally of finite type (a Mathlib instance).
  - With these, `exists_rationalOrbit_coordinates` gives `d`, `B`, `C` and a
    column `s : Fin d` as described in the introduction. The existence of `s`
    forces `d ≥ 1`, so `d` is rewritten as `d' + 1`.
  - `σ` is `restrictCoordinates ρ B C hCB hstable`. The two properties are the
    two theorems above.

  No affineness, connectedness or reductivity of `G` is assumed. `ρ` is indexed
  by an arbitrary finite type `n` with decidable equality.

## Relation to `SpanningLineStabilizerStatement`

`SpanningLineStabilizerStatement` quantifies over representations on
`Fin (n + 1)`, and assumes in addition that `G.X.hom` is affine. Given its data
`k, G, n, j, ρ`, the theorem `exists_spanning_sameCoordinateLineStabilizer ρ j`
supplies `d`, `s`, `σ` and the two properties. Unfolding
`SameCoordinateLineStabilizer` gives exactly the stabilizer equivalence required
there, in the same order (new representation on the left). So
`⟨d, s, σ, h₁, h₂⟩` proves the statement. This module does not contain that
step.
