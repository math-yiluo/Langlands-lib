# Ordered charts for an opposite source and a common-Levi middle radical

Author: Worker 200.

## Source and provenance

This is derived support for J.-L. Waldspurger, *La formule de Plancherel
pour les groupes p-adiques (d'après Harish-Chandra)*, J. Inst. Math.
Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082. The registered
original is `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

In the convergence part of the proof of Theorem IV.1.1, printed p.279 /
PDF p.45, the integral (2) over `U' ∩ Ū` is rewritten as an iterated
integral through the product decomposition `U' ∩ Ū = (U'' ∩ Ū)·(U' ∩ Ū'')`,
which the source states without proof. IV.1(12), printed p.283 / PDF p.49,
states the composition `J_{P'|P} = J_{P'|P''} J_{P''|P}` when
`d(P',P) = d(P',P'') + d(P'',P)`, and says that this was proved in the
course of the proof of the theorem. IV.3(1), printed
pp.285–286 / PDF pp.51–52, applies IV.1(12) four times. In each of the four
applications the source parabolic is the opposite of the target parabolic,
and the middle parabolic has the same Levi subgroup.

This module realizes, for actual dynamic radicals, the ordered chart datum
`OrderedSubgroupFactorization` that the published composition theorem
`StandardIntertwining.DynamicSource.comp_hasIntegral` takes as input, in
exactly this opposite-source case. It then specializes that theorem. The
provenance is internal: the charts come from the published product
homeomorphism `MatrixRepresentation.unipotentIntersectionProduct`. No new
translation of a numbered literature result is asserted.

## Generic helpers

For subgroups `A`, `B`, `C` of a topological group `Γ` with
`g ∈ C ↔ g ∈ A ∧ g ∈ B` for every `g`, `subgroupOfHomeomorphOfMem A B C h`
is the homeomorphism `A.subgroupOf B ≃ₜ C` that keeps the ambient element.
Its two simp lemmas record this.

`trivialProdHomeomorph t₀ ht` is the homeomorphism `T × X ≃ₜ X`, the second
projection, for a space `T` all of whose points equal `t₀`.

`HasCompactOpenProduct Q A B C` states that every `g ∈ C` lying in `Q` can
be written `g = a * b` with `a ∈ A`, `a ∈ Q`, `b ∈ B` and `b ∈ Q`. It is used
with `Q` an ambient compact open subgroup. It is an Iwahori-type
factorization of `Q ∩ C` with respect to `A` and `B`.

## Actual setting

`F` is a nonarchimedean local field of arbitrary characteristic. The group
scheme `G` over `F` is smooth, has affine structure morphism and is locally
of finite type. No reductivity, split or quasisplit condition is imposed.
`G(F)` carries the canonical point topology. For a cocharacter `χ`,
`unipotentPoints χ` is the literal radical `U(χ)(F)` of
`BruhatTits.DynamicUnipotentContainment`, and `Dynamic.inverseCocharacter χ`
is `χ⁻¹`.

The two cocharacters `χ` (target) and `ψ` (middle) are arbitrary, subject
to one hypothesis `hZ`: their dynamic centralizers have the same rational
points, `Z(χ)(F) = Z(ψ)(F)`. This is the literal form of "common Levi" for
dynamic parabolics. Under `hZ`:

* `cocharPoint_mem_centralizer_left` and `_right`: every value `ψ(t)` lies in
  `Z(χ)(F)`, and every `χ(t)` in `Z(ψ)(F)`. Each value of a cocharacter lies
  in its own centralizer by the published `cocharPoint_mem_centralizer`.
* `eq_one_of_mem_centralizer_left_of_mem_radical` and `_right`: a point of
  the common Levi lying in `U(ψ)(F)`, respectively `U(χ)(F)`, is `1`. This is
  the published `RationalPoint.levi_inf_unipotent`.

Without `hZ`, `eq_one_of_mem_inverse_radical` proves `U(χ⁻¹) ∩ U(χ) = 1`, from
the published `Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic`.
`inverseRadical_subgroupOf_eq_one` restates this for the actual subgroup
carrier `U(χ⁻¹).subgroupOf U(χ)`.

`contractingUnit` is a unit of `F` whose powers tend to `0`
(`contractingUnit_tendsto`), chosen from the published
`exists_unit_tendsto_pow_zero`. It is needed only to invoke the product
theorem. The charts below are literal multiplication, so this choice does
not affect them as functions.

## The three charts

The published `unipotentIntersectionProduct F χ' ξ t ht hξ hZU` is the
multiplication homeomorphism
`(U(χ') ∩ U(ξ)) × (U(χ'⁻¹) ∩ U(ξ)) ≃ₜ U(ξ)`, with both factors read inside
`U(ξ)`. It requires `ξ(t) ∈ Z(χ')(F)` and `Z(χ')(F) ∩ U(ξ)(F) = 1`.

* `firstChart hZ` applies it with `χ' = χ⁻¹` and `ξ = ψ`. Both premises follow
  from `hZ` and `Z(χ⁻¹) = Z(χ)` (published `centralizer_inverseCocharacter`).
  The second factor `U((χ⁻¹)⁻¹) ∩ U(ψ)` is identified with
  `U(ψ) ⊓ U(χ)` through `inverse_inverseCocharacter`. The result is
  `(U(χ⁻¹).subgroupOf U(ψ)) × (U(ψ) ⊓ U(χ)) ≃ₜ U(ψ)`, `(h, v) ↦ h v`.
* `secondChart hZ` applies it with `χ' = ψ` and `ξ = χ`, and identifies the
  second factor with `U(ψ⁻¹) ⊓ U(χ)`. The result is
  `(U(ψ).subgroupOf U(χ)) × (U(ψ⁻¹) ⊓ U(χ)) ≃ₜ U(χ)`, `(h, w) ↦ h w`.

`factorization hZ` is the datum

```
OrderedSubgroupFactorization U(χ⁻¹) U(ψ) U(χ) (U(ψ) ⊓ U(χ)) (U(ψ⁻¹) ⊓ U(χ)).
```

Its first and second charts are the two charts above. Its composite chart
`(U(χ⁻¹).subgroupOf U(χ)) × ((U(ψ) ⊓ U(χ)) × (U(ψ⁻¹) ⊓ U(χ))) ≃ₜ U(χ)` drops
the trivial first factor by `trivialProdHomeomorph`, identifies
`U(ψ) ⊓ U(χ)` with `U(ψ).subgroupOf U(χ)` and then applies the second
chart. The inclusions are `inf_le_left` and `inf_le_right`. The formulas
`first_eq` and `second_eq` hold by definition. `composite_eq` holds because
the first coordinate is `1`.

## Local product identities

`DynamicSource.comp_hasIntegral` also takes three identities stating that
each chart maps the product of the inverse images of one ambient compact
open `Q` onto the inverse image of `Q` in its target.

* `middle_localProduct` proves the middle identity, for the chart
  `intersectionSubgroupProduct` of `U(ψ) ∩ U(χ)`, with no hypothesis on `Q`.
  The endpoint kernel `U(χ⁻¹) ∩ U(χ)` is trivial, so every element of the
  image is a nested-complement element. Conversely, every element of
  `U(ψ) ∩ U(χ)` lying in `Q` is `1` times itself.
* `first_localProduct_of_hasCompactOpenProduct` derives the first identity
  from `HasCompactOpenProduct Q (U(χ⁻¹) ⊓ U(ψ)) (U(ψ) ⊓ U(χ)) U(ψ)`.
* `second_localProduct_of_hasCompactOpenProduct` derives the second identity
  from `HasCompactOpenProduct Q (U(ψ) ⊓ U(χ)) (U(ψ⁻¹) ⊓ U(χ)) U(χ)`.

In each of the last two proofs, inclusion of the image follows from the
subgroup property of `Q`. The reverse inclusion uses the assumed
factorization, read through the multiplication formula of the chart.

## Composition

The composition section retains every measurable structure on the radicals,
intersections and quotients as an explicit `MeasurableSpace` and
`BorelSpace` instance argument, as in `DynamicSource`. It also takes
semidirect decompositions `h₀ : P₀ = M ⋉ U(χ⁻¹)` and `h₁ : P₁ = M ⋉ U(ψ)` with a
common `M`, and a canonical `SmoothRep.{0,u,uV} ℂ M` named `A`. The
representation-carrier universe `uV` is independent of `u`.
`firstComplement_isClosed` and `secondComplement_isClosed` prove closedness
of the two complements.

`comp_hasIntegral` keeps the first and third local identities `hlocal₀` and
`hlocal₂` in the exact form of the published theorem. Each `HasIntegral`
below is the published predicate: at every `g ∈ G(F)`, absolute scalar
convergence against every smooth functional, with the stated value as a
representing vector in the original carrier of `A`. It assumes:

* `hf`: the integral of `f` over `(U(χ⁻¹) ∩ U(ψ)) \ U(ψ)`, at
  `DynamicSource.quotientMeasure Q hQ χ⁻¹ ψ`, is the evaluation of an
  intermediate induced vector `Φ`;
* `hΦ`: the integral of `Φ` over `(U(ψ) ∩ U(χ)) \ U(χ)`, at
  `DynamicSource.quotientMeasure Q hQ ψ χ`, is the function `J`;
* `ha`: ordered absolute scalar integrability of `f` against every smooth
  functional, for the intrinsic `Q`-normalized Haar measures on the two
  complements.

It concludes that the direct integral of `f`, at
`DynamicSource.quotientMeasure Q hQ χ⁻¹ χ`, is `J`. The proof applies
`DynamicSource.comp_hasIntegral` to `factorization hZ`, the two closedness
results and `middle_localProduct`. All other arguments pass through unchanged.

`comp_hasIntegral_of_hasCompactOpenProduct` is the same statement with
`hlocal₀` and `hlocal₂` replaced by the two `HasCompactOpenProduct`
premises above.

## Use in IV.3(1)

Let `χ` and `χ'` be cocharacters with the same Levi points, for parabolics
`P` and `P'`. The four applications of IV.1(12) in IV.3(1) are the instances
(target, middle) = `(χ', χ)`, `(χ'⁻¹, χ⁻¹)`, `(χ, χ'⁻¹)` and `(χ⁻¹, χ')`.
In the second and fourth the source radical is `U((χ'⁻¹)⁻¹)`,
respectively `U((χ⁻¹)⁻¹)`, equal to `U(χ')`, respectively `U(χ)`, by
`Dynamic.inverseCocharacter_inverseCocharacter`. The
common-Levi hypothesis for each follows from `Z(χ) = Z(χ')` and
`centralizer_inverseCocharacter`. These instantiations, and the passage to
rational operator identities, are not carried out in this module.

## Scope

* The two outer local product identities, equivalently the two
  `HasCompactOpenProduct` factorizations of `Q`, are explicit inputs. They
  are not proved for any compact open subgroup, in particular not for a
  special maximal compact subgroup.
* Ordered absolute convergence, both integral witnesses and original-carrier
  representability are explicit inputs. No convergence domain is shown to be
  nonempty.
* Only the case where the source radical is the radical of the inverse
  target cocharacter is covered. The general case
  `d(P',P) = d(P',P'') + d(P'',P)` of IV.1(12) is not treated.
* No rational continuation, operator identity, scalar `j`, independence of
  `P`, `μ` or Plancherel conclusion is claimed.

Integration uses module-specific names for local instances. Their types, values,
and local instance scopes are unchanged.
