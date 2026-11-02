# Full locally constant sheaves under spatial induction

The namespace is
`Langlands.Sheaf.Equivariant.SpatialInduction`.
This internal construction identifies the full locally constant coefficient
sheaves under the genuine spatial restriction and right-Kan induction functors
of `SpatialInduction`. It uses the actual balanced quotient
`Langlands.TopologicalInduction.Space H X` and the coefficient sheaves of
`LocallyConstant`; no desired comparison is an input.

The provenance is internal. The unit embedding and its open images come from
`Topology.GroupAction.InducedSpace` and `SpatialInduction`. The section modules,
inverse-coefficient pullbacks, sheaf condition and coefficient functor come
from `Sheaf.Equivariant.LocallyConstant`. Mathlib supplies homeomorphisms onto
images, module limits, representation restriction and composition of natural
isomorphisms. This file makes no new original-literature assertion.

The assumptions are an open subgroup `H` of a topological group `G`, a
topological space `X` with a jointly continuous `H`-action, and an arbitrary
commutative coefficient ring `R`. There is no topology on coefficients and
no finite-dimensionality requirement. No normality, local compactness of `G`,
total disconnectedness, compactness of `X`, or stable-neighbourhood assumption
is imposed.

The openwise constructions retain independent universes: `X : Type u`,
`G : Type v`, `R : Type r`, and the coefficient module `M : Type w`.
The categorical sheaf comparisons explicitly use `G : Type u` and
`X : Type u`. Both local and induced-space sheaves then take values in
`ModuleCat.{max u w} R`. The ring and module universes `r,w` remain independent
of `u`. This is the stated common-space-universe branch; no universe-lifting
comparison of coefficient categories is constructed.

For every `H`-transport open `U`, `unitOpenHomeomorph` is the homeomorphism

```text
U ≃ₜ unit(H) '' U,
```

where the target is the actual open of `Space H X` used by `unitFunctor`.
Its underlying map is `x ↦ [1,x]`, as recorded by
`unitOpenHomeomorph_apply_coe`.
For every subgroup-labelled arrow `f : U ⟶ V`,
`unitOpenHomeomorph_pointMap` proves commutation with the actual continuous
point maps: applying the local label before entering the unit chart equals
applying its original label in `G` after entering that chart. The proof is
the balanced quotient identity `unit(h • x) = h • unit(x)`.

`unitSectionsLinearEquiv` pulls back every locally constant section along this
homeomorphism. Its inverse pulls back along the inverse homeomorphism; the two
inverse identities follow pointwise from the homeomorphism identities. In
particular, it identifies the entire modules

```text
LocallyConstant (unitOpen H hH X U).openSet M
  ≃ₗ[R] LocallyConstant U.openSet M.
```

The forward and inverse evaluation lemmas state these literal pullback
formulas. `unitSectionsLinearEquiv_pullback` proves compatibility with every
subgroup-labelled arrow, including its inverse coefficient operator:

```text
s ↦ (x ↦ τ(h⁻¹)(s(h • x))).
```

The local coefficient action is precisely `τ.comp H.subtype`. The proof
uses the point-map commutation above and leaves the original operator `τ`
unchanged. `unitSectionsLinearEquiv_map` proves commutation with pointwise
application of any original coefficient linear map.

`restrictLocallyConstantPresheafIso` assembles these module equivalences into
an isomorphism of the full transport presheaves. Its naturality proof is the
labelled-pullback compatibility just proved. `restrictLocallyConstantIso`
is its lift to the full equivariant sheaf category. Thus restriction of the
ambient full locally constant sheaf is the local full locally constant
sheaf for the restricted coefficient representation. The lemmas
`restrictLocallyConstantIso_hom_app` and
`restrictLocallyConstantIso_inv_app` give the same forward and inverse
formulas on every open of this sheaf isomorphism.

`restrictLocallyConstantNatIso` records the comparison naturally in all
objects and morphisms of `Rep.{w} R G`:

```text
LocallyConstantSheaf.functor R G (Space H X) ⋙ restrict
  ≅ Rep.resFunctor H.subtype ⋙ LocallyConstantSheaf.functor R H X.
```

Its naturality reduces to pointwise commutation with the original
coefficient intertwiner. No coefficient morphisms are discarded.

`unitChartModuleLimits` constructs the actual limits required by spatial
induction. The structured-arrow indexing categories for `unitFunctor.op`
are small in the universe `max u w`; Mathlib's `ModuleCat.hasLimitsOfShape`
therefore supplies these limits without enlarging the ring or assuming
limit existence as extra data.

`induceLocallyConstantNatIso` gives the converse natural isomorphism:

```text
(Rep.resFunctor H.subtype ⋙ LocallyConstantSheaf.functor R H X) ⋙ induce
  ≅ LocallyConstantSheaf.functor R G (Space H X).
```

The implemented map first applies the genuine right-Kan induction functor
to the inverse of the unit-chart comparison. It then applies
`induceRestrictIso`, the already constructed reconstruction isomorphism
on all ambient equivariant sheaves. Associators and the right unitor
give the displayed functor endpoints. `induceLocallyConstantIso` is its
component at an arbitrary coefficient representation. Thus the converse
isomorphism uses the actual right-Kan object, and is not another
definition of an ambient sheaf by stipulated values.

These are ordinary-open equivariant sheaves and their full morphism
categories. This file does not construct a smooth spatial equivalence,
compact-support or higher-cohomology induction, an analytic or etale
identification, arithmetic towers, or Harris specialization. Those remain
separate obligations of the wider framework.
