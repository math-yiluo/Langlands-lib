# Unit fixation from a maximal residue torus

This internal result derives the character-valuation kernel bound of a
supplied integral split torus from its actual residue maximality and one
bounded generic maximal split torus. The maximal-unramified specialization
then proves the published `IsFixedByUnramifiedTorusUnits` predicate for every
scalar-extended source factoring through this torus, on any subset fixed by
the integral points of the model.

## Closed statement

`Langlands.Geometry.Building.ResidueMaximalTorusUnitsStatement` quantifies over
the following data in arbitrary universe `u`, without a characteristic
restriction:

- A commutative noetherian Henselian valuation domain `R` with algebraically
  closed actual residue field, and its fraction field `K`.
- A linearly ordered commutative group with zero `Γ₀`, a valuation
  `v : Valuation K Γ₀`, and the condition
  `v (algebraMap R K a) = 1` for every `a : Rˣ`.
- A connected reductive `K`-group scheme `G`, and an integral model `M` whose
  group scheme is smooth and whose actual special fibre is connected.
  `IntegralModel` includes the affine, flat, finite-type model and its
  specified generic-fibre isomorphism.
- A commutative generic source `T` with a maximal split torus map
  `i : T.toGrp ⟶ G`, and the bound
  `(characterValuationKernel v T.toGrp).map (rationalPoints.map i) ≤
  M.integralPoints`.
- A supplied commutative integral source `U`, a map `j : U.toGrp ⟶ M.group`,
  splitness of `U`, and maximality of the actual residue map obtained by
  base change of `j` along `R → IsLocalRing.ResidueField R`.

Write `J = M.genericTorusMap U j`, with source the actual scalar extension
`U_K`. The conclusion is the conjunction

```text
IsMaximalSplitTorus J
(characterValuationKernel v U_K.toGrp).map (rationalPoints.map J)
  ≤ M.integralPoints.
```

Thus the second generic maximality and the second kernel bound are derived.
There is no separate closedness premise on the integral map `j`; its supplied
residue maximality already includes a closed torus embedding on that fibre.
The bound is an inclusion in the actual range defining `M.integralPoints`.
The theorem `residueMaximalTorusUnits` proves exactly this closed proposition.
The general helper permits the value group to lie in a separate universe;
the closed statement puts `R`, `K` and `Γ₀` in `Type u`.

## Transfer through actual conjugacy

`Langlands.GroupScheme.map_characterValuationKernel_le_of_conjugacy` works
over any field and ordered value group, with arbitrary source group schemes
`A`, `B` and ambient group scheme `G`. Suppose `e : A ≅ B`,
`g : rationalPoints G`, and

```text
i ≫ (G.innerIso g).hom = e.hom ≫ j.
```

Let `P` be any subgroup of `G(K)` containing `g`. If the image of the
character-valuation kernel of `A` under `i` is contained in `P`, then the
corresponding image for `B` under `j` is also contained in `P`.

For a kernel point `t` of `B`, naturality of the character-valuation kernel,
in the published `map_characterValuationKernel_le`, sends `e.inv(t)` into
the kernel of `A`. Its image under `i` therefore belongs to `P`.
Precomposing the actual conjugacy equality by `e.inv` and evaluating it
at `t` gives

```text
g * i(e.inv(t)) * g⁻¹ = j(t).
```

The proof obtains this identity using the actual rational-point composition,
`comp_innerIso_hom` and `constantPoint_self`. Closure of `P` under
multiplication and inverse gives the desired membership. No normality of
`P`, torus structure, smoothness or characteristic restriction is needed
for this helper.

`IntegralModel.isMaximalSplitTorus_and_characterValuationKernel_le_of_bounded_residueMaximal`
uses
`IntegralModel.exists_integralPoint_conjugacy_of_bounded_residueMaximal`
from `ResidueMaximalTorusApartment`. That result constructs an actual
conjugator in `M.integralPoints`, a generic source isomorphism and the
displayed equality, and proves generic maximality of `J`. It does so by
extending the bounded first torus integrally, specializing its maximality,
lifting conjugacy of the two actual residue tori over the Henselian ring,
and transporting the equality through `M.genericIso`.
The new proof retains that maximality, views the commutative source
isomorphism as an actual group-scheme isomorphism, and applies the transfer
helper with `P = M.integralPoints`. It assumes no second kernel bound.

## Maximal-unramified unit fixation

`Langlands.Geometry.Building.isFixedByUnramifiedTorusUnits_of_residueMaximal`
uses the actual inertia fixed field `K = inertiaFixedField F` of a
nonarchimedean local field `F`, its ring `fixedFieldIntegers F`, and the
normalized valuation `MaximalUnramified.valuation F`. Its inputs are:

- An affine actual scalar extension `G_K` of an `F`-group `G`, supplied
  `MaximalUnramified.BuildingData` `C` for `G_K`, a supplied
  `UnramifiedZeroDatum` `E`, and any subset `Ω` of `C.Apartment`.
- A supplied smooth integral model `M` of `G_K` with connected actual
  special fibre, and `U`, `j`, splitness and actual residue maximality as
  above.
- The inclusion
  `E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) ≤ M.integralPoints`.
- Any subset `Y` of `C.ReducedBuilding` such that
  `M.integralPoints ≤ C.pointwiseFixer Y`.
- Any `F`-group source `A`, map `a : A ⟶ G`, and actual `K`-group
  homomorphism `f : A_K ⟶ U_K` satisfying
  `baseChange(a) = f ≫ J`.

The conclusion gives generic maximality of `J`, its newly derived kernel
bound in `M.integralPoints`, and
`∀ y ∈ Y, IsFixedByUnramifiedTorusUnits F a y`. Neither torus structure
nor maximality of `A`, and no injectivity or surjectivity of `f`, is required.
The subset `Y` need not lie in the apartment image used in the first
inclusion; it may be empty or unbounded. No Galois-fixedness premise on its
points is needed.

The canonical arithmetic inputs `fixedFieldIntegersIsHenselian`,
`fixedFieldResidueIsAlgClosure`, `fixedFieldValuesFromBase` and
`fixedFieldIntegersIsDVR_of_valuesFromBase` supply the Henselian DVR and
algebraically closed actual residue field. The residue algebra is induced
by `residueToFixedField`. The unit equation is the published
`SpecialTorusIntegralModel.valuation_units_eq_one`. No completeness or
local-field structure on `K` is assumed.

The published
`map_characterValuationKernel_le_zeroPoints_inf_pointwiseFixer`, composed
with the first inclusion, bounds the generic maximal split torus supplied
by `C`. The general theorem then proves both assertions about `J`.
For each kernel point of `A_K`, kernel naturality through `f` gives a kernel
point of `U_K`. The newly proved bound places its image under `J` in
`M.integralPoints`. The second inclusion makes that image fix every
`y ∈ Y`, using the actual pointwise-fixer definition in `C.apartment`.
Rewriting the literal factorization identifies this action with that of
`baseChange(a)`. This is exactly the published unit-fixation predicate in
`TorusUnitFixedPoint`, on the original reduced-building quotient.

## Provenance and retained obligations

This is a derived internal composition of the Library constructions and
results named above, rather than a transcription of a separate literature
statement. `ResidueMaximalTorusApartment` supplies the actual integral
conjugacy; `KPZeroNormKernel` supplies kernel naturality; and
`TorusUnitFixedPoint` supplies the precise scalar-extension fixation
predicate. The new content is the transfer of the second kernel bound and
its application to that predicate. The closed statement packages the
general algebraic conclusion; the unramified theorem is a supporting
specialization proved in the same file.

The model, the integral torus with its maximal actual residue map, the first
bound or apartment inclusion, integral-point fixation, and the scalar-source
factorization remain supplied. This unit constructs no maximal `F`-split
torus, coherent descended model or prescribed residue-torus lift. It proves
no facet or segment comparison, Galois stability or specialness. The host
`UnramifiedFixedPointSplitTorusStatement` therefore remains open. No barred
unramified building-descent statement or theorem consuming one is used.
