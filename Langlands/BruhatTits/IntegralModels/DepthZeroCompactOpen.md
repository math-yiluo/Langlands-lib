# Compact open depth-zero subgroups of supplied KP models

Let `F` be a nonarchimedean local field with valuation ring `𝒪 = 𝒪[F]`, and
give `G(F)` its canonical topology. This module proves that for supplied KP
models over `𝒪`, the radical preimage `G(F)^{0+}` is a compact open subgroup
of `G(F)`. It packages it, and the integral points `G^0(𝒪)` of the neutral
model, as open subgroups. Compactness and openness of `G^0(𝒪)` are already
published, and this module reuses them. It also proves two facts that hold
over any local domain. The level-one
congruence subgroup lies in `G(K)^{0+}`. Under the fppf-quotient hypothesis,
`G(K)^{0+} ∩ G^0(R)` is normal in `G^0(R)`.

## Provenance

The module is derived. Compactness and openness of `G^0(𝒪)` are the
published `Langlands.GroupScheme.IntegralModel.isCompact_integralPoints_localField`
and `isOpen_integralPoints_localField`, applied to `D.neutral`. They are the
instance, for the supplied neutral model, of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Remark 2.10.3 (printed p. 122 / PDF p. 153). The remark says that the
`o`-points of an affine integral model are closed, open and bounded in the
`k`-points, and open and compact when `k` is locally compact. The registered
original is `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. The
authors' corrections of 1 November 2024 (`kaletha-prasad-2024-corrections`,
SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`)
contain Chapter 2 corrections on PDF pp. 24–26. None of them amends
Remark 2.10.3.

For the radical preimage, KP's corresponding subgroup in the depth-zero
quotient of 13.2.6 (printed p. 470 / PDF p. 501) is `P_{x,0+}`. Corrected
Proposition 13.5.2 states that `P_{x,0+}` is open in `G(k)^0`. The Lean
subgroup `Q.positivePoints` is the radical preimage, KP's `G(k)^{0+}_F` of
Axiom 4.1.22(7). It is not compared with `P_{x,0+}` here; that comparison is
KP Corollary 8.4.12. Its openness and compactness are proved directly. The
proof uses the open congruence subgroup and the published compactness of
`G^0(𝒪)`.

## Setting

`R` is a domain in universe `u` with fraction field `K`, and `G` is a group
scheme over `Spec K`. `D : RelativeComponentModelData R K G` and
`Q : SpecialFibreQuotientData D` are the published supplied data of
`Langlands.BruhatTits.IntegralModels.RelativeComponent` and `SpecialFibre`.
For the local-field results, `R = 𝒪[F]` and `K = F` for a field `F` with
`ValuativeRel F`, `TopologicalSpace F` and `IsNonarchimedeanLocalField F`.
`G.X.left` is affine, and `G(F) = rationalPoints G` has the topology
`rationalPointTopology F G.X`. That topology is introduced with `letI` inside
each statement, so it is part of the statement. Nothing identifies
`D.neutral` with a Bruhat–Tits parahoric group scheme.

## Declarations

Over a local domain `R` (`IsLocalRing R`), in namespace
`Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData`:

- `congruenceSubgroup_le_positivePoints`:
  `D.neutral.congruenceSubgroup ≤ Q.positivePoints`. A section reducing to
  the identity reduces into the radical's points, which contain `1`. No
  hypothesis on `Q` is used.
- `positivePoints_subgroupOf_normal hQ`: under the fppf-quotient hypothesis
  `hQ`, `Q.positivePoints.subgroupOf D.neutral.integralPoints` is normal. It
  equals the kernel of `Q.parahoricReduction` by the published
  `ker_parahoricReduction hQ`.

Over `𝒪[F]`, with `[IsAffine G.X.left]`, in namespace
`Langlands.BruhatTits.IntegralModels.RelativeComponentModelData`:

- `localFieldIntegralOpenSubgroup D` (definition): `G^0(𝒪)` as an
  `OpenSubgroup` of `G(F)`. Its openness is the published
  `IntegralModel.isOpen_integralPoints_localField` for `D.neutral`.

No new compactness or openness theorem for `G^0(𝒪)` is declared.

With in addition `[LocallyOfFiniteType G.X.hom]`, which makes `G(F)` a
topological group by `rationalPoint_isTopologicalGroup`, in namespace
`SpecialFibreQuotientData`:

- `localField_isOpen_positivePoints`: `Q.positivePoints` is open in `G(F)`.
  It contains the level-one congruence subgroup, which is open by the
  published `isOpen_congruenceSubgroup_of_congruenceBasis`. A subgroup that
  contains an open subgroup is open (`Subgroup.isOpen_mono`).
- `localFieldPositiveOpenSubgroup` (definition, the unit's selected
  declaration): `Q.positivePoints` as an `OpenSubgroup` of `G(F)`.
- `localField_isCompact_positivePoints`: `Q.positivePoints` is compact in
  `G(F)`. An open subgroup is closed (`Subgroup.isClosed_of_isOpen`), and
  `Q.positivePoints ≤ D.neutral.integralPoints` (the published
  `positivePoints_le_integralPoints`). It is therefore a closed subset of
  the compact set `D.neutral.integralPoints`, compact by the published
  `IntegralModel.isCompact_integralPoints_localField`.

None of the local-field results uses `hrad` or `hQ`.

## Scope

This module supplies no models, radicals, quotients or building points. It
does not prove that `Q.positivePoints` is pro-`p`, does not compare it with
the Moy–Prasad subgroup `P_{x,0+}`, and does not identify `G^0(𝒪)` with a
parahoric subgroup.
