# Parabolic-left coverings of good model data from relative parabolic quotients

Author: Worker 1654.

This module connects three published or pending pieces:

- the statement `Langlands.GroupScheme.RelativeParabolicQuotient.ExistenceStatement.{u}`
  (proper quotients of reductive group schemes by parabolic subgroups, over any
  commutative ring);
- the local covering theorem
  `Langlands.GroupScheme.IntegralParabolicCovering.range_mul_integralPoints_eq_univ`;
- the model data `ReductiveParabolicSpreading.ModelData` and Worker 1641's canonical
  completion models and `ModelLocalConditions`.

Every theorem takes the quotient statement as an explicit hypothesis `hQ`. Nothing here
proves that statement, the existence of model data, or local maximality.

## Model data over a general base

Let `R` be a domain with fraction field `K`, `p : P ⟶ G` a homomorphism of group schemes
over `K`, and `D : ModelData R K p`.

- `ModelData.exists_quotient hQ D` applies `hQ` to `D.ambient.group`, `D.parabolic.group`
  and `D.inclusion.hom`. Its four hypotheses are the fields `D.reductive`,
  `D.parabolicSmooth`, `D.closedImmersion` and `D.fieldParabolic`. It gives `Q` over
  `Spec R` and `q : D.ambient.group.X ⟶ Q` with `Q` proper, `q.left` flat, surjective and
  quasi-compact, and the all-test criterion: `g ≫ q = h ≫ q` exactly when `g⁻¹ * h`
  factors through `D.inclusion.hom`.
- `ModelData.quotient hQ D` and `ModelData.quotientMap hQ D` are a chosen such pair, by
  `Classical.choose`. `ModelData.quotientMap_spec` records the five properties. The choice
  is not claimed to be canonical; any two such quotients would be isomorphic, but this is
  not proved here.
- `ModelData.hasConnectedSpecialFibre D` (for local `R`) is connectedness of the special
  fibre of the subgroup model. It is the `connected` part of
  `ModelData.goodFieldFibers.atFieldPoint` at the residue map `IntegralModel.residueBaseMap R`.
- `ModelData.range_mul_integralPoints_eq_univ hQ D`: if moreover `R` is a valuation ring
  with finite residue field that is complete for its maximal ideal
  (`IsAdicComplete (IsLocalRing.maximalIdeal R) R`), then

  ```lean
  Set.range (rationalPoints.map p) * (D.ambient.integralPoints : Set (rationalPoints G)) =
    Set.univ
  ```

  This is `G(K) = P(K) · M(R)` for the actual integral points `M(R)` of the ambient model
  inside the original `G(K)`, with `P(K)` acting through `p`.

  Proof: the closed immersion `D.closedImmersion` gives a monomorphism of schemes, hence
  (`Over.mono_of_mono_left`) a monomorphism over `Spec R`. Then
  `IntegralParabolicCovering.range_mul_integralPoints_eq_univ` applies to
  `D.ambient`, `D.parabolic`, `D.inclusion` and the chosen quotient map. The remaining
  inputs are `D.parabolicSmooth`, `hasConnectedSpecialFibre` and the coset criterion from
  `quotientMap_spec`.

## Canonical completion models

Let `F` be a number field, `S` a finite set of finite places and
`D : ModelData ((S : Set (FinitePlace F)).integer F) F p`. A place outside `S` is given
as `v : {v : FinitePlace F // v ∉ S}`. The completion carries the valuative relation
`FiniteCompletion.valuativeRel v`, as in the consumer modules.

- `canonicalModel_covering F S hQ D v` is exactly the covering premise `hcover` of
  `ModelLocalConditions.of_canonicalModels`:

  ```lean
  Set.range (rationalPoints.map
      ((GroupScheme.baseChange (Spec.algebraMap F (FiniteCompletion F v.1))).map p)) *
    ((IntegralModelCompletions.canonicalModel F S v D.ambient).integralPoints : Set _) =
      Set.univ
  ```

  Proof: install the published local-field certificate
  `FiniteCompletion.isNonarchimedeanLocalField v.1`. Instance search then finds the
  valuation-ring, finite-residue-field and adic-completeness instances for the canonical
  integers `𝒪[FiniteCompletion F v.1]`; the last two are Mathlib's instances for
  nonarchimedean local fields. Apply the previous theorem to
  `IntegralModelCompletions.canonicalModelData F S v D`, whose ambient model is by
  definition `canonicalModel F S v D.ambient`.
- `ModelLocalConditions.of_quotientStatement F S hQ D hmax` (for affine `G.X.left`):
  given only the maximality premise `hmax` of `of_canonicalModels` on the canonical
  models, it proves `ModelLocalConditions F G P p S D.ambient` by supplying the covering
  premise above. With Worker 1641's `isIntegralIwasawaFamily_of_models`, the target
  `IsIntegralIwasawaFamily` then follows from model data, the quotient statement and local
  maximality.

## Provenance and scope

This is an internal derived assembly. The mathematics is the Getz–Hahn proof of
Theorem B.2.5 (printed p. 544, PDF p. 549 of `getz-hahn-2024-automorphic-representations`).
It uses properness of `G/P` over `O_{F_v}` (Conrad 2014, Corollary 5.2.8, the content of
the quotient statement) and lifting of integral points through the torsor `G → G/P`
(published modules). The local-field instances are Mathlib's for nonarchimedean local
fields. No new external result is asserted.

The module does not prove `RelativeParabolicQuotient.ExistenceStatement`,
`ReductiveParabolicSpreading.ExistenceStatement` or local maximality. So it does not
prove `Langlands.Global.IntegralIwasawaFamily.ExistenceStatement`.
