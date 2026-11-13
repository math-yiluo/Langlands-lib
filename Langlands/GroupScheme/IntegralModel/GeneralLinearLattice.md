# The general linear integral model on a full lattice

This module states the existence of the general linear integral model
`GL(L)` attached to a full lattice. It also implements the standard model
on the coordinate lattice. The statement isolates a step in the proof of
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Proposition 8.3.1, printed pp. 295–296 / PDF pp. 326–327. The relevant
paragraph is on PDF p. 327 (printed p. 296). The registered source is
`kaletha-prasad-2023-bruhat-tits-new-approach`, content SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The authors' corrections of 1 November 2024 are registered as
`kaletha-prasad-2024-corrections`, content SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
Their PDF p. 37 replaces the first sentence of Section 8.3 with the
assumption that the residue field is perfect. No errata note for either
source was present in the published `notes/errata` directory when this
module was prepared.

## The source paragraph

In the proof of Proposition 8.3.1 the authors reduce to a vertex `x` with
maximal bounded subgroup `K = G(K)^1_x`. They choose a faithful
representation `ρ : G → GL(V)` and use Proposition 2.2.13 to choose a
lattice `L ⊂ V` with `ρ(K) ⊂ K̃ = GL(L)`. They then take the schematic
closure of `ρ(G)` "in the smooth group scheme `GL(L)`". The paragraph
uses, without separate proof, that `GL(L)` is a smooth affine `O`-group
scheme with generic fibre `GL(V)`. Its `O`-points are the stabilizer of
`L` in `GL(V)`. In the source, `O` is the ring of integers of the field
`K` of Section 8.3, and the section assumes the reductive and residue
field hypotheses stated there.

## Scope of the Lean statement

`GeneralLinearLatticeIntegralModelStatement.{u}` is a derived elementary
subresult of that paragraph. It is an unproved existence target. Its
inputs are the following:

- a discrete valuation ring `R : Type u`, with `IsDomain R` and
  `IsDiscreteValuationRing R`;
- a supplied field `K : Type u` with `Algebra R K` and
  `IsFractionRing R K`;
- a natural number `n`;
- an actual submodule `Λ : Submodule R (Fin n → K)` with
  `Submodule.IsLattice K Λ`.

Mathlib's `Submodule.IsLattice K Λ` means that `Λ` is finitely generated
over `R` and spans `Fin n → K` over `K`. Kaletha–Prasad define a lattice
in a vector space over a valued field as a bounded open submodule over
the valuation ring (proof of Proposition 2.2.13, PDF p. 105). For a
discrete valuation ring and its fraction field with the valuation
topology, the two notions agree. This module does not formalize that
comparison; the statement uses the algebraic definition only.

The conclusion asks for an actual
`M : IntegralModel R K (GeneralLinear.groupScheme (Fin n) (CommRingCat.of K))`.
The generic group is the Library's fixed general linear group over `K`.
An `IntegralModel` carries an affine, flat, locally finite type group
scheme `M.group` over `Spec R`. It also carries a specified isomorphism
`M.genericIso` from the base change of `M.group` along
`Spec.algebraMap R K` to the generic group. The conclusion requires
`M.IsSmooth`, which is `Smooth M.group.X.hom`. It also requires that for
every original rational point `g`,
`g ∈ M.integralPoints ↔ GeneralLinear.StabilizesLattice Λ g`.

`M.integralPoints` is the range of `M.integralPointMap`. That map restricts
a section over `Spec R` to `Spec K` through the actual pullback, then
applies `M.genericIso`. The formula therefore uses the generic
identification specified inside `M`. No integral model, change of basis,
generic identification or stabilizer comparison is an input.

`GeneralLinear.StabilizesLattice Λ g` reads the actual matrix of `g` over
`K` through `GeneralLinear.rationalPointsEquiv n (CommRingCat.of K)`.
That equivalence takes the matrix of a point and moves its entries from
the global sections of `Spec K` to `K`. The predicate requires that the
matrix and its inverse both send every `v ∈ Λ` into `Λ` under
matrix-vector multiplication `*ᵥ`, acting on column vectors. The two
inclusions together are equivalent to `g Λ = Λ`. So the predicate is the
source's stabilizer `GL(L)` for `V = Fin n → K`.

The coordinate space `Fin n → K` covers every finite-dimensional
`K`-vector space up to a choice of basis. The statement is stated only in
this coordinate form.

The statement drops these source hypotheses: the base is any discrete
valuation ring, with no completeness, Henselian, topological or
perfect-residue-field hypothesis. It assumes no reductive group, no
faithful representation and no building. These hypotheses are not used by
the elementary general linear construction. The statement does not assert
that every bounded subgroup is a lattice stabilizer. It also does not
assert schematic closure, smoothening or uniqueness of the model.

## The implemented standard construction

`GeneralLinear.standardIntegralModel R K n` is an implemented definition.
It works for any integral domain `R : Type u` with a supplied fraction
field `K : Type u`, and any finite index type `n : Type` with decidable
equality. Its fields are the following:

- `group` is the Library's `GeneralLinear.groupScheme n (CommRingCat.of R)`.
- `affine` is the existing instance `GeneralLinear.isAffineHom_groupScheme`.
- `flat` and `finiteType` are inferred from smoothness. Smoothness is the
  published theorem `GeneralLinear.smoothStatement n (CommRingCat.of R)`.
- `genericIso` is the Library's base-change isomorphism
  `GeneralLinear.baseChangeIso n (Spec.algebraMap R K)` onto
  `GeneralLinear.groupScheme n (CommRingCat.of K)`.

The theorem `GeneralLinear.standardIntegralModel_isSmooth` proves
`(standardIntegralModel R K n).IsSmooth` directly from
`GeneralLinear.smoothStatement n (CommRingCat.of R)`.

This module proves nothing about the integral points of the standard
model. In particular it does not prove that they are the stabilizer of
the coordinate lattice.

## The remaining existence obligation

The arbitrary-lattice statement is not proved here; it is the target of a
separate proof task. The intended proof is the elementary construction
behind `GL(L)`:

1. A full lattice over a discrete valuation ring is free of rank `n`
   (Mathlib's `Submodule.IsLattice.free` and
   `Submodule.IsLattice.finrank_of_pi`).
2. An `R`-basis of `Λ` extends to a `K`-basis of `Fin n → K`
   (`Module.Basis.extendOfIsLattice`).
3. Compose the generic identification of the standard model with the
   change-of-basis automorphism of the general linear group over `K`.
4. Prove that a rational point is integral exactly when its matrix and
   inverse matrix preserve `Λ`. This compares integral matrices in the
   chosen basis with preservation of the original lattice. The Library
   theorem `GeneralLinear.pointsEquiv_comp_baseChangeIso_hom` describes
   the base-change isomorphism on points.

Steps 3 and 4, including the exact integral-point comparison, remain
proof obligations. Independence of the chosen basis is not needed for
this existence statement.

In the source argument, this statement supplies the ambient model. The
consumer still has to construct a stable lattice, embed the generic group
in the general linear group, take a schematic closure and smoothen it.
This statement proves none of those constructions.
