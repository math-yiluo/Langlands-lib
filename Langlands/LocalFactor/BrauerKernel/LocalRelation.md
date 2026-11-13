# Local restrictions of a relation among induced Hecke characters

Author: Worker 5093. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. In Deligne's global
argument (1973, §4.12) a relation among induced characters of a global Weil group restricts
at every finite place `z` to a relation among induced characters of the local Weil group at
`z`. This unit performs that restriction for relative Weil groups `W_{E/F}`. The companion
unit `BrauerKernel.LocalEuler` then cancels the L-factors of the local relation.

Everything is in `Langlands.ClassField.Global.RelativeWeilGroup`. Fix a class family
`c : FundamentalClass.ClassFamily.{u}` with `h : FundamentalClass.Restriction c`, a Galois
extension `E/F` of number fields in universe `u`, a finite type `J`, integers `r j`,
intermediate fields `K j` of `E/F` and Hecke characters `θh j`, `θh' j` of `K j`. `Gal(E/F)`
has the discrete topology (`relativeGaloisTopology`).

For a finite place `z` of `F`, a local map `ιd : W_{F_z} →ₜ* W_{E/F}` is supposed to satisfy
the published local restriction formula `LocalInducedRestriction.{max u uV, u} c F (K j) E h z ιd`
for every `j`. This gives local maps `ιu j u : W_{(K j)_u} → W_{E/K j}` at the places `u` of
`K j` above `z`. They are compatible with transfer and the units of every geometric reciprocity
candidate of `(K j)_u`, and they give a Mackey formula for restricting induced classes along
`ιd`. Finally `eC` is a reciprocity family of `F_z` with `NormalizedReciprocity (padicField z) eC`,
and `hgeo : CommonClosureGeometricStatement.{u, u}`.

## Results

- `continuousRestrict_sum_induce_eq_weilCharacter`: the restriction along `ιd` of

  `Σ_j r_j · Ind_{W_{E/K_j}}^{W_{E/F}} ([θh_j ∘ τ] - [θh'_j ∘ τ])`

  (induction along `restrictionInclusion c F E (K j) h`, characters
  `continuousReciprocityCharacter c (K j) E`) equals

  `Σ_{(j, u)} r_j · Ind_{(K_j)_u}^{F_z} ([weilCharacter e_u (θh_j)_u] - [weilCharacter e_u (θh'_j)_u])`.

  The sum runs over the sigma type of pairs `(j, u)` with `u ∈ FinitePlacesAbove (K j) z`.
  Induction is along `extensionWeilMap (padicField z) (towerPadicField z u) (completionPadicAlgHom z u)`.
  The candidate `e_u` is the transported candidate
  `extensionReciprocityCandidate (padicField z) (towerPadicField z u) (completionPadicAlgHom z u) eC`.
  The quasicharacter is `quasicharacterAt u (residuePrime_eq z u) ((θh j).finiteComponent u)`.
  Proof: distribute the restriction over the sum (`map_sum`, `map_zsmul`) and regroup with
  `Fintype.sum_sigma`. For each `j`, the Mackey formula of `hloc j` writes the restriction as a
  sum over `u` of inductions of `continuousRestrict (ιu j u)`. Clause 2 of `hgeo` says that
  `e_u` is geometric. So the transfer compatibility of `ιu j u` applies to `e_u`, and the
  published `continuousReciprocityCharacter_comp_eq_weilCharacter` identifies
  `continuousReciprocityCharacter c (K j) E (θh j) ∘ ιu j u` with
  `weilCharacter e_u (θh j)_u`, and likewise for `θh' j`. The published
  `continuousRestrict_characterClass` turns restricted character classes into classes of
  composites.
- `sum_induce_weilCharacter_eq_zero` (**local relations**): if moreover the global combination
  is `0` in `ContinuousVirtual.{u, uV} c F E`, then the local combination of the previous item
  is `0`. Proof: rewrite the local combination with the previous item and use
  `continuousRestrict ιd 0 = 0`.

The global universe `u` and the representation universe `uV` are independent.

## Provenance

The Mackey formula is the published `LocalInducedRestriction`, whose source is Tate, *Number
theoretic background* (1979), (2.3.5) with (1.6.1). Its use here follows Deligne, *Les
constantes des équations fonctionnelles des fonctions L* (1973), proof of Lemma 4.12, where
the global relation is restricted to every place. This unit is internal bookkeeping with the
published lemmas of `Global.Factors.RelativeWeilBrauer` and
`Global.Factors.RelativeWeilLocalHecke`. It is the general-index form of the Fin-indexed
decomposition `exists_continuousRestrict_decomposition` in `RelativeWeilBrauer`. No base-field
term occurs, so the local transfer reciprocity statement is not needed.
