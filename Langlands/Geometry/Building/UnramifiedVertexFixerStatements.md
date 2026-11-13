# Vertex fixers and finite vertex approximation over the unramified field

These two unproved geometric propositions isolate the building inputs to the
full-model part of KP Theorems 8.3.2 and 8.3.13. They do not assume a schematic
subgroup or an integral model. `VertexFixerApproximationStatement` is their
conjunction. All declarations retain the arbitrary universe `u`.

The source is Kaletha--Prasad, *Bruhat--Tits Theory: A New Approach* (2023),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:

- Theorem 4.2.15(1) and its proof, printed pp. 173--174 / PDF pp. 204--205;
- Proposition 7.7.1, printed pp. 267--268 / PDF pp. 298--299;
- Proposition 7.7.5(1)--(3), printed pp. 269--270 / PDF pp. 300--301;
- Proposition 8.3.1 and Theorem 8.3.2 with their proofs, printed
  pp. 295--296 / PDF pp. 326--327.

The registered 1 November 2024 corrections,
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF p. 37, assume a perfect residue field at the start of Section 8.3.
A local field `F` has finite, hence perfect, residue field. Its actual
maximal unramified field is `K = inertiaFixedField F`. The statements use
the published normalized valuation `MaximalUnramified.valuation F` of
this same field.

`G` is an affine group scheme over `K`. `C : BuildingData F G` supplies its
connected reductivity, its maximal split torus and its compatible KP
apartment data. No descent of `G` from `F` is required for these geometric
assertions. The perfect-residue-field assumption gives the quasi-split
setting of Section 8.3 for connected reductive groups over `K`.
The existing `C.IsVertex`, `C.oneStabilizer` and `C.pointwiseFixer` are
used literally, on the original quotient `C.ReducedBuilding`.

## Maximal bounded vertex subgroups

`VertexOneStabilizerMaximalBoundedStatement` asserts that, for every vertex
`y`, the subgroup

```text
C.oneStabilizer y = G(K)^1 ∩ G(K)_y
```

is maximal among the actual algebraically bounded subgroups of `G(K)`.
`Maximal` includes boundedness of this subgroup itself. Boundedness
quantifies over all actual global regular functions of the original
affine group through `IsAlgebraicallyBounded`. The valuation relation on
`K` is explicitly the one induced by `fixedFieldValued F`; it is the
relation used to construct the normalized integer valuation. The private
affineness instance only passes from the affine structural morphism to
the affine total scheme.

This is the maximal-bounded part of KP Theorem 4.2.15(1), specialized to
`K`. Its additional openness conclusion is not asserted. The proof in
the source uses bounded-subgroup fixed points and the fact that the
vertex parahoric fixes only its vertex; neither result is proved here.

## Finite vertex approximation

`FiniteVertexFixerApproximationStatement` starts with a nonempty
`Ωa ⊆ C.Apartment` on which every real affine function is bounded above,
and a rational point `g`. This is the same boundedness convention as
`UnramifiedParahoricModelStatement`. Put

```text
Ω = { g • C.apartmentMap x | x ∈ Ωa },
H = G(K)^1 ∩ Fix(Ω).
```

The proposition supplies a nonempty finite set `Y` of actual building
vertices such that

```text
U = ⋂ (y ∈ Y), C.oneStabilizer y
```

is contained in `H`, and its subgroup inside `H` is normal and of finite
index. Normality and finite index refer to `U.subgroupOf H`; the separate
containment prevents this notation from hiding an intersection with `H`.
The finite set need not contain `Ω`.

This formulation is a derived geometric consequence of the steps in
the proofs of KP 8.3.1--8.3.2. In that route one replaces `Ω` by the
union `Ω'` of the closures of the facets meeting it, and takes the
vertices of those facets. Boundedness in one apartment gives finitely
many such vertices. The vertex-intersection description is the one used
in 8.3.1, with Proposition 7.7.5 identifying the norm-one pointwise
fixer. The inclusions of 8.3.2 place this `U` inside `H` and place `H`
inside the norm-one setwise stabilizer of `Ω'`; Proposition 7.7.1 gives
finite index.

Normality records the elementary compatibility needed to apply
`FiniteIndexEnlargementStatement`: an element fixing `Ω` preserves each
facet that meets `Ω`, since it fixes a point of that facet and facets
partition the building. It therefore preserves `Ω'` and its vertex set.
Conjugation preserves the common character-valuation kernel and
permutes the point fixers, so it preserves their intersection `U`.
The statement does not require choices of facets or vertices to be
canonical, and makes no uniqueness assertion.

The maximality and finite-approximation assertions are separate
obligations. Together with general existence of models for maximal
bounded subgroups, finite intersections of schematic subgroups and
finite-index enlargements, they support the full-model construction.
They identify no relative identity component and assert no equality of
neutral integral points with `G(K)^0 ∩ Fix(Ω)`. None of these existence
or geometric obligations is discharged by this statement file.
