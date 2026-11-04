# Finite-covering trace on smooth direct images of full coefficient sheaves

This internal derived construction equips the existing smooth direct image of
full locally constant coefficient sheaves with the actual unnormalized
finite-covering trace. It uses the full ordinary-open sheaf trace and the
original smooth-image inclusion. Every map remains a morphism of the existing
smooth equivariant sheaf category.

## Inputs and coefficient scope

The commutative ring `R`, topological group `G`, spaces `X`, `Y` (and `Z` for
composition), and coefficient carriers lie in one arbitrary universe `u`, as
required by the existing `SmoothDirectImage.functor` API. This unit does not
remove that universe restriction. Each space has its original `G`-action,
continuous constant group actions, and `HasStableNeighbourhoods`. The group is
an `IsTopologicalGroup`.

The spatial input is an original continuous equivariant map `f : C(X,Y)`, an
actual `IsCoveringMap f` with its evenly covered charts, and finiteness of each
literal original fiber `f ⁻¹' {y}`. No surjectivity, properness or compact-support
hypothesis is needed. Empty fibers are permitted.

Coefficients range over the entire original category `SmoothRep R G` at the
stated universe, with every original intertwiner. There is no topology or
dimension restriction on the coefficient module. The smoothness assumption is
exactly the existing open-stabilizer predicate.

## Construction and original sections

Write `LC_X(M)` for `LocallyConstantSheaf.smoothFunctor R G X` evaluated at `M`,
and `S_f` for `SmoothDirectImage.functor f hf`. The existing proof in
`LocallyConstantSmooth` establishes that the full locally constant coefficient
sheaf is smooth: none of its original sections is removed when it is bundled
in the smooth category. The functor `S_f` is the existing smooth coreflection
of the full ordinary direct image after the smooth-sheaf inclusion.

`coefficientTrace` has type

```text
S_f(LC_X(M)) → LC_Y(M).
```

Its underlying full sheaf morphism is the actual smooth-image inclusion
`S_f(LC_X(M)) → f_*LC_X(M)` followed by
`DirectImage.coefficientTrace f hf h M.representation`.
`coefficientTrace_forget` records exactly this equality. The target is already
the full smooth coefficient sheaf, so the full-subcategory constructor supplies
the smooth morphism without an additional target section or compatibility
input. In particular, all labelled restriction equations follow from those of
the original inclusion and full trace.

A section of `S_f(LC_X(M))` over an original open `U` consists of a full locally
constant section on `f⁻¹(U)` and its local-smoothness proof. The theorem
`coefficientTrace_apply` shows that the output at `y : U` is the literal fiber
sum of the underlying original section. The theorem
`coefficientTrace_apply_sum` reindexes this sum over the entire original fiber
of `f` at `y.val`:

```text
Tr_f(s)(y) = ∑ (x : f⁻¹{y}), s.val(x).
```

Each `x` is inserted into the inverse-image open using its original fiber
equality. The sum is unnormalized; an empty fiber contributes zero. These
formulas reuse the previously proved full-trace formulas, so their meaning is
unchanged by the smoothness proof carried by the source section.

The original smooth coefficient pullback is `coefficientMap` from
`SmoothDirectImage.Coefficients`. Its composite with the new trace satisfies
`coefficientTrace_pullback_apply`:

```text
Tr_f(f* s)(y) = Nat.card(f⁻¹{y}) • s(y).
```

The multiplication is natural-number scalar multiplication. The fiber size may
vary, and no division, invertibility or constant-degree assumption is made.

## Naturality, identity and spatial composition

`coefficientTraceNatTrans` is a natural transformation

```text
smoothFunctor_X ⋙ S_f → smoothFunctor_Y.
```

For each original smooth coefficient morphism `a : M → N`, its square is
`coefficientTrace_naturality`: direct image of the original pointwise
coefficient map followed by trace at `N` equals trace at `M` followed by the
original pointwise coefficient map on `Y`. The proof is the existing linear
finite-sum naturality applied to the underlying source section; no restriction
of the morphism category or assumed trace square is introduced.

For the identity spatial map, finite original fibers are supplied by
`finite_id_fiber`. `coefficientTrace_unit` proves that the existing
`SmoothDirectImage.idIso` unit followed by trace is the identity.
`coefficientTrace_id` then identifies trace with the inverse of that exact
comparison isomorphism. `coefficientTraceNatTrans_id` states this equality
naturally in the entire original smooth coefficient category. The unit law
reduces through the inclusion to the original full identity trace; cancellation
of the isomorphism proves the inverse formula.

For original maps `f : X → Y` and `g : Y → Z`, composition retains genuine
covering hypotheses for `f`, `g` and `g.comp f` and finite literal fibers for
all three maps. Composite finiteness is available from the existing
`finite_comp_fiber`; a covering of the composite remains an explicit input.
`coefficientTrace_comp` proves

```text
compMap(f,g) ≫ Tr_(g∘f) = S_g(Tr_f) ≫ Tr_g.
```

Here `compMap(f,g)` is the existing comparison from the iterated smooth direct
image to the composite smooth direct image. It is not assumed invertible. Its
section map forgets the two nested smoothness proofs and retains the original
section. Evaluating the full trace-composition equality on that section proves
the displayed law. `coefficientTraceNatTrans_comp` packages the same law as an
equality of natural transformations, with the actual whiskered `compMap` on
the left and the original smooth direct-image functor on the right.

## Provenance and retained obligations

This is an internal derivation from `Sheaf.Equivariant.CoveringTrace`,
`SmoothDirectImage`, `SmoothDirectImage.Coefficients` and
`LocallyConstantSmooth`. The full trace supplies the original covering-chart
construction, labelled fiber reindexing and finite-sum laws; the existing
smooth inclusion and full-subcategory construction supply the new morphism.
The intrinsic equalities above are proved, rather than supplied as fields or
comparison assumptions. No external literature theorem is asserted.

This unit concerns ordinary-open coefficient sheaves and their degree-zero
smooth direct images. Instantiation of an original rational or Shimura map as
an actual finite covering is still required. It does not construct an etale or
Godement trace, a higher derived map, a compact-support comparison, arithmetic
Hecke identification or Harris compatibility. The broader Harris framework
remains incomplete.
