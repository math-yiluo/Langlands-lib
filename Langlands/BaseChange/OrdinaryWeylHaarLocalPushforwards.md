# Ordinary local Haar pushforwards for Weyl integration: proof

The module `Langlands.BaseChange.OrdinaryWeylHaarLocalPushforwards` proves
`OrdinaryWeylHaarLocalPushforwardsStatement` as the theorem
`ordinaryWeylHaarLocalPushforwards`. For a nonarchimedean local field `F`, any `n`, a Haar
measure `μ` on `GL_n(F)`, a `WeylTorus` `T` with a right invariant Haar measure `μT` on its
rational points and a quotient measure `ν` compatible with `μ` and `μT`: every point of
`LeftQuotient T × T.regularPoints` has an open neighbourhood `V` on which
`T.ordinaryOrbitMap` is an open embedding, and the pushforward of
`T.weightedOrdinaryOrbitMeasure ν (μT.comap val) T.discriminantWeight` restricted to `V` is
`μ` restricted to the image of `V`. No characteristic hypothesis is made.

Two auxiliary facts about a `WeylTorus` are proved: its rational points commute with each
other (`WeylTorus.val_mul_comm`, from `glCentralizer_mul_comm`), and the Weyl discriminant of a
regular point is nonzero (`WeylTorus.weylDiscriminant_ne_zero`, from the unit determinant in
`det_ordinaryWeylDifferential`).

## Proof

Fix the point `(H g₀, t₀)` with `t₀` regular and write `γ` for its value in `GL_n(F)`.

1. *Analytic structures.* `F` carries the normed field structure `LocalGalois.localNormedField`,
   which is complete, ultrametric and proper and whose topology is the given one. The matrix
   algebra carries the ultrametric algebra norm `finiteAlgebraNormedRing` with the given
   (product) topology; it is complete, being finite dimensional over a complete field. Thus
   `GL_n(F)` is the unit group of a normed algebra as in
   `Langlands.Analysis.Local.WeylChartLocal`. `GL_n(F)` is Hausdorff, second countable and
   locally compact (`LocalFieldTopology`), so `μ` is right invariant
   (`generalLinear_haar_rightInvariant`), and `T` is closed, being a centralizer.
2. *Regular position.* The adjoint defect of `GL_n` coincides with the Library's
   `adjointDefect γ`. Its kernel and image are complementary at a regular semisimple `γ`
   (`isCompl_ker_range_adjointDefect`), so `γ` is in regular position
   (`isRegularPosition_of_isCompl`). Moreover `T = glCentralizer γ`
   (`WeylTorus.glCentralizer_eq_of_regularPoint`), which is the centralizer `torusGroup γ`
   (`glCentralizer_eq_centralizer`).
3. *Chart scale.* By `chartDifferential_eq` the ambient differential of the conjugation
   chart is `P − d`, whose determinant is `weylDiscriminant γ`
   (`det_ordinaryWeylDifferential`). The residue-normalized scaling of additive Haar measure
   by a linear automorphism (`map_linearEquiv_residueAbsolute`) and `chartScale_eq_of_map`
   give `chartScale = |weylDiscriminant γ|⁻¹`. The weight at `t₀` is
   `T.discriminantWeight t₀ = |weylDiscriminant γ|`, which is nonzero, so the weight times
   the chart scale is `1`.
4. *A neighbourhood with constant weight.* The regular semisimple set is open
   (`regularSemisimpleOpenConull`), so `T.regularPoints` is open in `T`. The weight is locally
   constant on the regular points (`WeylTorus.isLocallyConstant_discriminantWeight`, using
   step 3 at every regular point), so the regular points with weight equal to that of `t₀`
   form an open set `U₀`. Let `N` be the product of the whole coset space with the image of
   `U₀` in `T`.
5. *Local pushforward on `T`.* `exists_orbitMap_localPushforward_of_eq` gives an open
   `W ⊆ N` containing `(H g₀, t₀)` on which the orbit map is an open embedding, with
   `((ν.prod μT).restrict W).map orbitMap = chartScale • μ.restrict (orbitMap '' W)`.
6. *Passage to regular points.* Let `ι = id × val` from `LeftQuotient T × T.regularPoints` to
   `LeftQuotient T × T`, an open embedding, and `V = ι⁻¹ W`. Since `W ⊆ N` lies in the range
   of `ι`, `ι '' V = W`. The ordinary Weyl map is `orbitMap ∘ ι`, so its restriction to `V`
   is an open embedding. On `V` the weight is constant, so the weighted measure restricted to
   `V` is the weight at `t₀` times `(ν.prod (μT.comap val))` restricted to `V`. The
   pushforward of `ν.prod (μT.comap val)` under `ι` is `ν.prod (μT.restrict regularPoints)`,
   since `val` is a measurable embedding; restricted to `W` it is `(ν.prod μT).restrict W`.
   Combining with step 5 and step 3 gives the identity of the statement.

## Source

The statement is the local measure input to the ordinary Weyl integration formula of
Henniart–Lemaire, *Changement de base et induction automorphe pour GLₙ en caractéristique non
nulle*, Mém. SMF 124 (2011), II.2.10, formula (2), printed p. 72. The proof is an internal
derivation: additive coordinates near a regular point, the ultrametric local change of
variables (`Langlands.Analysis.local_map_restrict_eq_of_hasStrictFDerivAt`), the Weil formula
for the compatible quotient measure, and the determinant computation of
`det_ordinaryWeylDifferential`.
