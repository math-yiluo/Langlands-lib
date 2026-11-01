# Actual normal-level quotient actions on represented CM schemes

This module constructs a quotient-group action by actual scheme automorphisms
at a sufficiently small normal level. It derives the action from the existing
exact CM moduli presheaf and its representing objects, proves that forgetting
to the coarse level is invariant, and identifies the actions under canonical
changes of representing choices. Exact representability and the named
prerequisites remain explicit hypotheses.

## Normal transporters and the action convention

For compact-open levels `V ≤ U`, normality is the Mathlib instance
`(V.subgroup.subgroupOf U.subgroup).Normal`. The inclusion is supplied separately
as `hVU`. Thus the subgroup of `U` used in the quotient is exactly the given
fine subgroup, rather than an unspecified normal subgroup.

`CompactOpenLevel.normalInverseArrow U V hVU g` is a genuine transporter
`V ⟶ V` with element `g⁻¹` for `g : U.subgroup`. Its required condition is
`g * V * g⁻¹ ≤ V`, proved by relative normality inside `U`. The identity and
multiplication lemmas are equalities of transporter arrows; multiplication
satisfies

```
normalInverseArrow (g * k) =
  normalInverseArrow k ≫ normalInverseArrow g.
```

The construction lifts to the existing full subcategory `SmallCMLevel D` as
`smallCMNormalInverseArrow`. It retains the original Harris opposite finite
adelic group, and all inverses and products are in that group.
`smallCMNormalLevelAction` sends these transporters through any actual
small-level tower. Mathlib's multiplication on categorical endomorphisms is
composition in the reverse displayed order, so this yields an `Action`:
`ρ(g * k) = ρ(k) ≫ ρ(g)`. On the existing frame moduli this is inverse right
translation, sending the frame to its composition with `g⁻¹`. This inversion
converts the source's right action into Mathlib's left-action convention.

## The actual fine-subgroup kernel

The family `R` has exactly the existing type `CMLevelRepresentation` at each
small level. Each representing base belongs to
`ComponentwiseAdmissibleCMBaseCategory`, is smooth and projective in the
existing precise sense, and has a natural isomorphism from lifted Yoneda to the
fixed CM moduli presheaf. The imported `representedCMBaseTower` constructs its
maps by fully faithful Yoneda preimage of those moduli transitions; no
arbitrary transition maps are supplied.

`representedCMNormalBaseAction_kernel` proves that the fine subgroup acts
trivially on the actual represented base. If `g` belongs to `V`, the transporter
with element `g⁻¹` and the identity transporter have the same target right
coset: `(g⁻¹)⁻¹ * 1 = g ∈ V`. The imported actual target-coset equality therefore
identifies their represented maps, and the functor identity law finishes the
proof. That imported equality was proved on the original frame orbits and
propagated through polarized rational-isogeny classes, the Harris determinant
and numerical subtypes, compatible geometric families and connected-component
products to the fixed moduli presheaf. The kernel is consequently a property of
the actual moduli construction, not a consequence of transporter functor laws
alone.

`representedCMNormalQuotientBaseAction` applies `QuotientGroup.lift` to this
proved kernel inclusion. Its acting group is

```
U.obj.subgroup ⧸ V.obj.subgroup.subgroupOf U.obj.subgroup.
```

Its underlying object is `(R V).base`. Its `_mk` equation is definitional and
recovers the inverse-right transporter map for every representative `g`.
The `_mk_classes` equation states its exact interpretation on each actual
admissible test scheme `S`: postcomposing a morphism from `S` with that action
map corresponds, under the fixed representation isomorphism, to the original
CM moduli transition at the same transporter. `ULift` only raises the universe
of the Hom set to the presheaf's existing codomain.

## Actual scheme automorphisms and invariant forgetting

`representedCMNormalQuotientAction` forgets the base action through the full
subcategory inclusion and `Over.forget (Spec F)`. It is an `Action Scheme` on
the actual fine scheme in `representedCMSchemeTower R`. Its `_mk` equation
recovers the actual scheme transition for inverse right translation.
`representedCMNormalQuotientAutomorphism` uses `Action.ρAut`; its hom is
`ρ(g)` and its inverse is `ρ(g⁻¹)`. The inverse identities are supplied by
the group-action laws. The `_over` theorem uses quotient induction and the
existing structure-map equation for the representative transporter, proving
that every action map is over the original CM field `F`.

`representedCMNormalProjection` is the actual forgetting map for `V ≤ U`,
obtained by applying the same scheme tower to the identity-element inclusion
transporter. Its invariance theorem again uses an actual coset calculation.
For a representative `g : U`, inverse right translation followed by forgetting
has transporter element `g⁻¹`, while forgetting has element `1`. Their target
coset difference is `g`, which belongs to `U`. The imported target-coset
equality makes the two scheme maps equal. Quotient induction proves invariance
for every residual group element. `representedCMNormalQuotientProjection`
packages this map as a morphism to the trivial action on the coarse scheme.

For any other exact representing family `R'`,
`representedCMNormalQuotientActionComparison` uses the existing canonical
scheme-tower comparison at `V`. Naturality at inverse-right transporters,
followed by quotient induction, proves equivariance, so the result is an
isomorphism of actions. `representedCMNormalProjection_comparison` proves
that this same isomorphism commutes with forgetting, by the canonical
comparison's naturality at the inclusion. These comparisons represent identity
on the same moduli presheaves; they are not arbitrary scheme isomorphisms.

`cmNormalQuotientAction` specializes the construction to witnesses selected
from precisely `CMRepresentabilityStatement`. It acts on the corresponding
fine object of the existing `cmSchemeTower`. It does not prove the
representability proposition or strengthen its domain.

## Source, hypotheses and remaining geometry

The source is Harris and Taylor, *The Geometry and Cohomology of Some Simple
Shimura Varieties* (2001), III.1, printed p.91, one-based PDF p.99, registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The original passage defines monodromy-invariant frame orbits, gives right
translation by frame composition under the transporter inclusion, and states
the normal-level Galois-cover assertion with group `U/V`. The construction here
derives the action and invariant map from that frame convention and the
existing formalized moduli tower. The internal transporter, kernel and quotient
interfaces are derived content, and inverse right translation accounts for the
left-action convention explicitly.

The central simple unitary datum, CM-compatible signature charts and original
opposite group are retained. So are the named pullback-tensor preservation,
composition, unit, associativity, unitor and symmetry hypotheses; Picard-zero
stability, Mumford-square and universal-base-change hypotheses; duality
naturality and polarization base change; the relative finite Weil transition,
adelic comparison and torsion finite-etale hypotheses. Tests are exactly the
componentwise admissible CM bases already used by the presheaf. Their connected
component constructions retain the existing connectedness, local Noetherianity
and geometric-point field conditions; no assertion on all `F`-schemes is added.

This is a conditional construction of an actual quotient action and an invariant
forgetting map. Applicable representability, division/global hypotheses,
comparison with the original moduli problem and admissibility of representing
schemes remain separate obligations. No faithfulness, freeness, transitivity,
finite etaleness, torsor or Galois-cover property is proved. The source's
stronger geometric assertion, canonical-model comparisons, uniformization and
coefficient descent remain unproved by this module.
