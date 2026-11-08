# Local actions on the finite rational transport site

Author: Worker 13. Built on the generic local action systems of
`Langlands.Sheaf.Equivariant.LocalAction`, Worker 36's published rational
transport category `OpenSubgroupTransport` with its finite covering topology
`finiteTopology ρ` (`OpenSubgroupTransportCovering`), the published operators
and section representations of `OpenSubgroupTransportSections`, and the
published local smoothness of `OpenSubgroupLocallyConstantSmoothSections`.

The hypotheses are those of the transport site: a complete ultrametric normed
field `K`, a presented strict affinoid algebra `P`, a topological group `G` and
a `RationalSpectralAction ρ` of `G` on `P`. An object `X` of
`ρ.OpenSubgroupTransport` carries an open subgroup `X.subgroup` and a rational
locus stable under it. An arrow `V ⟶ X` has a label `g : G`. Labels compose
as `(f ≫ f').label = f'.label * f.label`. The published operator
`X.operator k : X ⟶ X` of `k ∈ X.subgroup` has label `k⁻¹`.

## Definitions

- `OpenSubgroupTransport.operatorAction X` packages the operators as a local
  action `X.subgroup →* (End X)ᵐᵒᵖ`, using the published `operator_one` and
  `operator_mul`. `operatorAction_unop` records that `k` goes to
  `X.operator k`.
- `OpenSubgroupTransport.localActionSystem ρ` is the local action system on
  `ρ.OpenSubgroupTransport` in which a local action `a` of an open subgroup
  `H` on `X` is admissible when every `h ∈ H` acts through an arrow labelled
  `h⁻¹`. This is the convention of the published operators and of
  `ActionOpens.localActionSystem`. It follows Berkovich's convention on printed
  p.7, where `h` acts on sections through the morphism `h⁻¹`.

## Results

- `isAdmissible_operatorAction`: the operator action of each object's own
  subgroup is admissible.
- `IsAdmissible.eq_operatorAction`: an admissible action `a` of `H` on `X`
  agrees with the operator action at each `g ∈ H ⊓ X.subgroup`. Arrows are
  determined by their labels.
- `isDiscreteSection_iff_operatorAction`: for any presheaf `F` with values in
  a concrete category, a section over `X` is discrete for an admissible action
  of `H` exactly when it is discrete for the operator action of `X.subgroup`.
  Both directions use the generic `IsDiscreteSection.of_agree` on the open
  subgroup `H ⊓ X.subgroup`.
- `isDiscrete_iff`: `F` is discrete for `localActionSystem ρ` exactly when
  every section over every object is discrete for that object's operator
  action.
- `admissibleSieve_eq_top` and `covers`: every arrow factors through an object
  with an admissible action, namely its own source with the operator action.
  Hence the admissible sieves cover for every Grothendieck topology.
- `comp_operator_eq`: let `f : V ⟶ X` have label `c` and let `g ∈ X.subgroup`
  with `c⁻¹ g c ∈ V.subgroup`. Then `f ≫ X.operator g` equals
  `V.operator (c⁻¹ g c) ≫ f`. Both arrows have label `g⁻¹ c`.
- `isDiscrete_of_isLocallyDiscrete`: if `F` is separated for `finiteTopology ρ`
  and locally discrete for `localActionSystem ρ`, then `F` is discrete. Let `s`
  be a section over `X`. By the definition of the finite topology, the
  discrete sieve of `s` contains a finite family `f i : D i ⟶ X` whose labelled
  point images cover the locus of `X`. Each `f i` factors as
  `k i ≫ v i`, where `v i : V i ⟶ X` and the restriction of `s` along `v i`
  is discrete for an admissible action on `V i`. By
  `isDiscreteSection_iff_operatorAction`, an open subgroup `N i` of
  `(V i).subgroup` fixes this restriction under the operator action. Let `c i`
  be the label of `v i`. The conjugate `N' i`, the preimage of `N i` under
  `g ↦ (c i)⁻¹ g (c i)`, is open by continuity of multiplication. Take the open
  subgroup `X.subgroup ⊓ ⨅ i, N' i`, a finite infimum. For `g` in it, the
  formula `comp_operator_eq` shows that the operator of `g` applied to `s` and
  `s` itself have the same restriction along every `v i`. The arrows `v i`
  cover the locus of `X`, since the arrows `f i` do and
  `(f i).label = (v i).label * (k i).label`. So their sieve lies in
  `finiteTopology ρ X`, and separatedness gives that `g` fixes `s`.
- `isLocallyDiscrete_iff_isDiscrete`: for separated presheaves on
  `finiteTopology ρ`, local discreteness and discreteness agree. The converse
  direction is the generic `IsDiscrete.isLocallyDiscrete` with `covers`.

For a commutative ring `R`, the remaining results concern the published module
sheaves `ModuleSheaf R`, the sheaves for `finiteTopology ρ` with values in
`ModuleCat R`.

- `moduleSheaf_isSeparated`: the underlying presheaf of a module sheaf is
  separated for `finiteTopology ρ` as a presheaf of elements. Let `x` and `y`
  be sections with equal restrictions along a covering sieve. Let `E` be the
  submodule spanned by `x - y`. The inclusion of `E` and the zero map agree
  after every restriction in the sieve. Since `F` is a sheaf, the sheaf
  condition at the module `E` makes them equal, so `x = y`.
- `isDiscrete_iff_locallySmoothProperty`: a module sheaf is discrete for
  `localActionSystem ρ` exactly when it satisfies the published
  `locallySmoothProperty`, smoothness of the section representation of every
  object at its own open subgroup. This combines `isDiscrete_iff` with the
  generic `isDiscreteSection_iff_isSmoothVector`.
- `isLocallyDiscrete_iff_locallySmoothProperty`: the same for local
  discreteness, by `moduleSheaf_isSeparated` and
  `isLocallyDiscrete_iff_isDiscrete`.
- `discreteSheafProperty_eq` and `smoothSheafProperty_eq`: the generic
  properties `discreteSheafProperty` and `smoothSheafProperty` of
  `localActionSystem ρ` on `ModuleSheaf R` both equal the published
  `locallySmoothProperty`.

## Provenance and scope

This module is derived infrastructure. Berkovich, *Etale equivariant sheaves
on p-adic analytic spaces* (unfinished 1995–1996 manuscript), section 1.4,
printed pp.7–8, which are PDF pages 7–8, describes the canonical actions of
subgroups on sections. Definition 1.4.1 asks that these actions be discrete
over compact `U`. The remark after it, on printed p.8, characterizes this by
open stabilizers on neighbourhoods. Worker 13 read these passages in the
original. On the present site the covering families are finite by definition,
and the finite infimum of fixing subgroups takes the place of a compactness
argument. The equivalence of the two conditions proved here is a statement
about this explicit site only, under separatedness. It is not Berkovich's
equivalence on quasi-étale or étale sites.

The module does not construct analytic, quasi-étale or étale sites or
Berkovich's Key Lemma. The admissible actions are those through inverse-label
arrows on all objects, without a compactness condition. Nothing is asserted
about cohomology of these sheaves.

Source registrations:
Berkovich,
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

The module `Langlands.Sheaf.Equivariant.LocalAction` is the accepted candidate
`c57f69f9-ab17-40c5-82a0-eed09bab751d` awaiting integration. All other imported modules are present in
Library commit `a840796df31e2bbb94ee9b265002f7d19a55aa75`.
