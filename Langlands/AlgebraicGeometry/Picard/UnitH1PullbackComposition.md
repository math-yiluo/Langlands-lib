# Intrinsic restriction and transported unit cohomology

This internal construction concerns actual unit sheaves and their actual
abelian-sheaf cohomology in every degree `n : ℕ` and every common universe
`u`. It uses the unchanged definitions and comparisons published in
`NilpotentUnitReduction`, `UnitSheafPushforward`, `UnitH1Pullback`,
`UnitSheafPushforwardNaturality`, `UnitSheafPushforwardComposition`, and
`SquareZeroUnitNaturality`.

Let `i : Y ⟶ X` and `j : Z ⟶ Y` be morphisms of actual schemes of
universe `u`. Initially assume that `i` and `j ≫ i` are closed immersions
with nilpotent ideal sheaves, witnessed by `hi` and `hji`. Write
`E_i` and `E_ji` for the existing additive cohomology comparisons from
pushed unit sheaves to the unit sheaves on `Y` and `Z`, respectively.
The definition
`UnitH1Pullback.transportedRestrictionMap i j hi hji n` is

```text
H^n(Y, O_Y^×) -- E_i⁻¹ --> H^n(X, i_* O_Y^×)
  -- H^n(i_* unitsReduction j) --> H^n(X, (j ≫ i)_* O_Z^×)
  -- E_ji --> H^n(Z, O_Z^×).
```

All groups are written additively. The middle coefficient map is the actual
map on section units induced by `j.c`, pushed to `X`. These endpoints agree
definitionally with the existing `quotientUnitsMap i j`. If `hi` and `hji`
are instead supplied as square-zero equalities, the resulting transported
map is definitionally the existing
`SquareZeroUnitNaturality.quotientUnitCohomologyMap`, as recorded by
`transportedRestrictionMap_squareZero`.

The lemma `transportedRestrictionMap_cohomologyMap` identifies ambient
reduction followed by this transported map with reduction for `j ≫ i`.
It cancels `E_i⁻¹ ∘ E_i`, uses the actual coefficient identity
`unitsReduction i ≫ quotientUnitsMap i j = unitsReduction (j ≫ i)`, and
applies functoriality of the existing `Sheaf.H.map`.

Now also assume that `j` is a closed immersion with nilpotent ideal
sheaf, witnessed explicitly by `hj`. No nilpotence implication is asserted
or needed: the three witnesses are supplied. The lemma
`nilpotentClosedImmersionTopIso_comp` identifies the composite of the
existing topological isomorphisms for `j` and `i` with the existing one
for `j ≫ i`; equality of their forward continuous maps proves this.
The main comparison `transportedRestrictionMap_eq_cohomologyMap` states

```text
transportedRestrictionMap i j hi hji n = cohomologyMap j hj n.
```

This identifies the transported construction with the unchanged intrinsic
unit-cohomology restriction for `j`. For a class `y`, take `a = E_i⁻¹(y)`.
The published composition coherence identifies the successive pushforward
comparisons at the image of `a` with `E_ji`. To substitute the equality of
topological isomorphisms, the implementation first obtains heterogeneous
equality of their cohomology equivalences by equality induction, then
ordinary equality because the two source types agree definitionally.
Coefficient naturality moves the comparison for `i` through
`unitsReduction j`. Finally `E_i(a) = y` completes the calculation.
This argument uses the actual previously defined comparisons throughout.

The corollary `cohomologyMap_comp` gives equality of additive homomorphisms

```text
(cohomologyMap j hj n).comp (cohomologyMap i hi n)
  = cohomologyMap (j ≫ i) hji n.
```

For square-zero `i` and `j ≫ i`, and the same explicit closed-immersion
and nilpotence hypotheses on `j`, the corollary
`SquareZeroUnitNaturality.quotientUnitCohomologyMap_eq_cohomologyMap`
identifies the existing quotient-unit cohomology map with intrinsic
restriction. Substitution into the published boundary naturality gives
`boundaryMap_cohomologyMap`:

```text
boundaryMap (j ≫ i) hji n (cohomologyMap j hj n y)
  = idealCohomologyMap i j (n + 1) (boundaryMap i hi n y).
```

Here the boundary is the existing actual connecting homomorphism, with
its target transported to the existing module cohomology of the actual
structure kernel. The ideal map is the existing actual kernel inclusion
on the common ambient scheme `X`.

The provenance is internal: the construction and proofs combine the
published coefficient maps, comparison naturality and composition coherence.
They introduce no additional external mathematical assertion. No compactness,
properness, field, splitting, or projectivity hypothesis is used. These
results provide composition and intrinsic restriction compatibility for
the nilpotent unit-cohomology part of Picard deformation theory. They do
not prove general scheme base change, scalar stability of boundary images,
representation of a Picard functor, or the host's exact fppf Picard scheme
representability statement.
