# Nonvanishing of the actual dynamic opposite standard integrals

Author: Worker 200.

## Source and provenance

This is derived support for J.-L. Waldspurger, *La formule de Plancherel
pour les groupes p-adiques (d'après Harish-Chandra)*, J. Inst. Math.
Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082. The registered
original is `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

IV.1(10), printed p.283 / PDF p.49, states `J_{P'|P}(π) ≠ 0`. The module
`StandardIntertwiningNonvanishing` (candidate `fe1d23c6`, approved) proves this
for the actual standard integral at a fully convergent parameter. It needs a
compact open subgroup `Q` with the local product property
`HasSourceLocalProduct` and a nonzero vector fixed by `P ∩ Q`. This module
constructs both for the actual opposite pairs `(P(χ), P(χ⁻¹))` of
`DynamicOppositeStandardIntertwining`, in both directions. So these families
are nonzero at every parameter of their full domains. The provenance is
internal, and no new translation of a numbered literature result is claimed.

## A fixed vector for small subgroups

`exists_nhds_fixedVectors_comp_projection` is generic. Let `P = M U` be a
semidirect decomposition in a topological group `G` with continuous Levi
projection, `τ` a representation of `M`, and `v` a vector fixed by an open
subgroup `S` of `M`. Then there is an identity neighborhood `W` in `G` such
that, for every open subgroup `Q ⊆ W`, the vector `v` is fixed by `τ(m(p))` for
all `p ∈ P ∩ Q`. Here `m` is the Levi projection. The preimage of `S` under
`m` is open in `P`, and `W` is an open set of `G` that cuts it out.

## Iwahori factorization and the local product property

The actual setting is that of `DynamicOppositeStandardIntertwining`: a
nonarchimedean local field `F` of arbitrary characteristic, an affine group
scheme `G` over `F` locally of finite type with its canonical point topology,
and a cocharacter `χ`.

`HasOppositeIwahoriFactorization χ Q` is a `Prop` about an open subgroup `Q` of
`G(F)`. It states that every `k ∈ Q` is `o z w` with `o ∈ Q ∩ U(χ⁻¹)`,
`z ∈ Z(χ)(F)` and `w ∈ Q ∩ U(χ)`.

* `forward_hasSourceLocalProduct`: such a `Q` has
  `HasSourceLocalProduct (P(χ)) (U(χ)) (U(χ⁻¹)) Q`. If `x ∈ U(χ⁻¹)` and
  `x = p k` with `p ∈ P(χ)`, `k ∈ Q`, factor `k⁻¹ = o z w`. Then
  `x o = p w⁻¹ z⁻¹` lies in `P(χ) ∩ U(χ⁻¹)`, which is trivial (published
  `Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic`). Hence
  `x = o⁻¹ ∈ Q ∩ U(χ⁻¹)`.
* `reverse_hasSourceLocalProduct`: such a `Q` also has
  `HasSourceLocalProduct (P(χ⁻¹)) (U(χ⁻¹)) (U(χ)) Q`. For `x ∈ U(χ)` with
  `x = p k`, factor `k = o z w`. Then `x w⁻¹ = p o z` lies in
  `P(χ⁻¹) ∩ U(χ)`, again trivial (with `(χ⁻¹)⁻¹ = χ`), so `x = w ∈ Q ∩ U(χ)`.
* `exists_factored_compactOpen_subset`: if `G` is connected reductive, every
  identity neighborhood contains a compact open subgroup with
  `HasOppositeIwahoriFactorization χ`. Take a compact open subgroup inside the
  neighborhood (published `Jacquet.exists_isCompact_openSubgroup_subset`) and
  apply `CommonLeviSplitting.exists_iwahoriCut` from the module
  `CommonLeviCompactSplitting` (approved candidate `4b938870`). Smoothness of
  `G` comes from reductivity.

## Nonvanishing

The remaining data are those of the actual opposite families: the structural
statements `hRefl` (`RelativeRootReflectionExistenceStatement`) and `hCST`
(`CentralSplitTorusCharacterStatement`) used for their squared-modulus
identities, connected reductivity `hG`, a compact open subgroup `K` normalizing
the source measures, and a canonical `SmoothRep.{0,u,uV} ℂ` of the Levi
`Z(χ)(F)` named `A`.

`conditionalForwardFamily_ne_zero`: for every parameter `z` of
`forwardFullDomainRegion χ K hK A` and every nonzero `v ∈ A`, the published
`conditionalForwardFamily χ K hK hRefl hCST hG A z` is not zero. The proof
proceeds in four steps:

1. The half-modulus twist of the twisted representation `A ⊗ z` is smooth
   (published `isSmooth_twist_iff` with the open kernel of the half modulus),
   so an open subgroup `S` of the Levi fixes `v` under it.
2. The generic lemma gives a neighborhood `W` such that `P(χ) ∩ Q` fixes `v`
   for the Levi-inflated action whenever `Q ⊆ W`.
3. `exists_factored_compactOpen_subset` gives a compact open `Q ⊆ W` with
   `HasOppositeIwahoriFactorization χ Q`, hence the local product property.
4. `standardInductionIntertwinerFamily_ne_zero` of
   `StandardIntertwiningNonvanishing`, applied with the published measures and
   compatibility of the forward family, concludes.

`conditionalReverseFamily_ne_zero` is the same for the reverse family from
`P(χ⁻¹)` to `P(χ)`, with the opposite decomposition and
`reverse_hasSourceLocalProduct`.

The subgroup `Q` only provides the test vector. It is unrelated to the
normalizing subgroup `K` of the measures, and the conclusion holds for the
published `K`-normalized families.

## Scope

* The parameter must lie in the full domain, so convergence is still an
  input; the extension of IV.1(10) to all parameters through continuation is
  not proved.
* The squared-modulus identities of the families keep the explicit
  structural statements `hRefl` and `hCST`, as in
  `DynamicOppositeStandardIntertwining`.
* Nonvanishing of the scalar `j`, positivity, `μ` and the Plancherel formula
  are not addressed.
