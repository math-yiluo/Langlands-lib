# Opposite factors in smooth connected integral models

Author: Worker 200.

Lean module: `Langlands.BruhatTits.IntegralModels.IntegralOppositeFactorsStatement`.

This module states `IntegralOppositeFactorsStatement.{u}` without proof. It is
Kaletha–Prasad Theorem 8.2.9 specialized to nonarchimedean local fields and to the
Library's supplied relative-component models. It constructs no model, torus,
radical, or quotient, and makes no building assumption.

## Exact data and conclusion

Let `F` be any nonarchimedean local field in universe `u`, in either
characteristic. Let `G` be connected reductive over `F`, and let
`iS : S.toGrp ⟶ G` be a maximal split torus. Supply
`D : RelativeComponentModelData ↥𝒪[F] F G`. Its neutral model is already smooth
and affine with connected fibres and has its specified generic-fibre
identification with `G`. Supply `T : IntegralTorusData D S iS` with
`T.IsClosedSplit`, so its actual closed split integral torus has generic fibre
`iS` through the specified identification.

Supply `Q : SpecialFibreQuotientData D` with `Q.IsReductiveQuotient`. This
predicate requires that its specified radical is the actual unipotent radical
of the neutral special fibre, that the projection represents its fppf quotient,
and that the quotient is connected reductive. The subgroup `Q.positivePoints`
consists of the generic images of neutral integral sections whose reduction lies
in the residue-field points of this radical. It is not the kernel of reduction
to the whole special fibre.

For every relative root `a`, every nonidentity `g ∈ U_a(F)` in the neutral
integral-point image, and every `g', g'' ∈ U_{-a}(F)` with
`g' * g * g'' ∈ N_G(S)(F)`, the statement asserts

```
(g' ∈ D.neutral.integralPoints ∧ g'' ∈ D.neutral.integralPoints) ↔
  g ∉ Q.positivePoints.
```

The two factors are those of KP Proposition 2.11.17 by its uniqueness
assertion. Integrality of their product with `g` then follows from subgroup
closure; it is not an extra conjunct. Quantifying over all such factors avoids
choosing them in this statement.

## Source correspondence and scope

Kaletha and Prasad, *Bruhat–Tits Theory: A New Approach* (2023), source
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:

- Theorem 8.2.9 and its preceding setup, printed pp. 293–295 / PDF pp. 324–326.
- Proposition 2.11.17, printed p. 136 / PDF p. 167, for uniqueness of the
  opposite factors.

The source takes a smooth affine model with connected special fibre containing
a closed integral split torus whose generic fibre is maximal split. Here the
neutral model of `D` supplies these properties, with connectedness on all
fibres. The unused full model and its relative-component inclusion are retained
only to reuse the existing actual torus and special-fibre quotient interfaces.
The source works over a Henselian discretely valued field and uses the maximal
quasi-reductive quotient by the residue-field split unipotent radical. Here
`F` is a nonarchimedean local field, so its finite residue field is perfect and
that radical is the unipotent radical; the corresponding quotient is reductive.
The statement is a specialization, not the source's full generality.

The neutral model's integral-point map is injective by the published
`IntegralModel.integralPointMap_injective`. Thus for an integral generic point,
membership in `Q.positivePoints` expresses precisely the radical-reduction
criterion for its unique integral section. No surjectivity of residue-field
points is silently substituted for this condition.

The authors' *Corrections and additions*, version of 1 November 2024, source
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp. 37–38, do not change Theorem 8.2.9. They replace `f` by `f_s` in
Lemma 8.1.4, a separate result; the local-field specialization here is unchanged.

## Role in the fixed-point depth-zero proof

KP use Theorem 8.2.9 in Proposition 9.4.9(2), printed pp. 349–350 / PDF
pp. 380–381. To apply this statement to the published
`UnramifiedFixedDepthZeroOppositeStatement`, one must still construct the model
and torus at each Galois-fixed upper point, identify its integral root points
with nonnegative restricted values, and show that a prescribed value-zero root
point has reduction outside the radical. Those are separate geometric
obligations. This statement does not discharge them or prove the depth-zero
target. Its provenance is derived from the stated specialization of Theorem
8.2.9.
