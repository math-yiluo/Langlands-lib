# Strict positivity of `j_P` at unitary points (target and reduction)

Worker 5. `Langlands.Plancherel.ConditionalDynamicOppositeUnitaryPositiveStatement`
is a Prop-valued target about the Library's canonical scalar `j_P` of
`J_{P|P̄} J_{P̄|P}` (`conditionalCanonicalRationalScalar`). It says two things:

- `j_P ≠ 0` in the field of rational functions of unramified characters;
- at every unitary unramified character where both chosen continuations are
  regular, `j_P` and `j_P⁻¹` are both regular with positive real values.

The module proves the target from the Hermitian adjunction target
`ConditionalDynamicOppositeHermitianAdjunctionStatement` (module
`DynamicOppositeHermitianAdjunctionStatement`):
`conditionalDynamicOppositeUnitaryPositive_of_hermitianAdjunction`.
It does not prove the Hermitian adjunction. Everything else used in the
reduction is proved in full: the uniform form of IV.1 (10), its extension to
the continuation, positivity of values, and the strict form of the
adjointness argument.

This strengthens `ConditionalDynamicOppositeUnitaryNonnegStatement` (module
`DynamicOppositeUnitaryNonnegativity`), which gives only nonnegativity at the
same points.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082, registered as `waldspurger-2003-plancherel`, PDF
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

- IV.1 (10), printed p.283 / PDF p.49: `J_{P'|P}(π) ≠ 0`. The proof notes
  that, for `f` in the space `F_1` of the proof of IV.1 (sections supported
  near `P`), `[J_{P'|P}(π ⊗ χ) sp_χ f](1) = ∫_{U∩U'\U'} (sp_χ f)(u') du'`.
  This holds by definition on the convergence domain and "se prolonge
  algébriquement à tout χ". One can choose `f` with a nonzero right side
  at `χ = 1`.
- Proof of IV.3 (6), printed p.287 / PDF p.53. Fix `e` with
  `(J_{P̄|P}(π ⊗ χ) e)(1)` regular and nonzero at `χ = 1` (by IV.1 (10)).
  For unitary `χ` the adjunction
  `(J_{P̄|P}(π ⊗ χ) f, f') = (f, J_{P|P̄}(π ⊗ χ) f')` gives
  `j(π ⊗ χ) (e, e) = (J_{P̄|P}(π ⊗ χ) e, J_{P̄|P}(π ⊗ χ) e)`.
  Waldspurger then shows `j(π) ≠ 0` by a limit argument as `χ → 1`.

## Provenance

The target is derived. Waldspurger states no positivity claim for `j`.
The target combines two steps of his proof of IV.3 (6), the choice of `e`
from IV.1 (10) and the displayed identity, at the unitary points where both
continuations are regular. At such a point `z` the module shows
`(J_{P̄|P}(z) e)(1) = c • v ≠ 0`. So `J_{P̄|P}(z) e ≠ 0`, and the identity
gives `j_P(z) = (J e, J e) / (e, e) > 0`. This direct argument replaces
Waldspurger's limit argument. His argument needs only that `J_{P̄|P} e` is
regular at the point, while the target here also needs the continuation of
`J_{P|P̄}` to be regular there. `j_P ≠ 0` then follows because some unitary
point is regular for both continuations.

The uniform form of IV.1 (10) is proved here in the compact picture. The
Library's `DynamicOppositeNonvanishing` (IV.1 (10) on the convergence domain)
uses a test vector that depends on the parameter. Here one vector `e` works
for all parameters at once (see below).

## The test vector is independent of the twist

Section `CompactTwist` is generic. `G` is a locally compact nonarchimedean
group with a semidirect decomposition `P = M ⋉ U` (`h`), `P` and `U` closed,
continuous projection `h.projection : P → M` (`hr`). `K` is a compact open
subgroup. The unramified characters are those of the family `ν` of
continuous norm characters of `M`.

- `compactLeviImage h K` is the image of `P ∩ K` in `M`. It is compact
  (`isCompact_compactLeviImage`), and it contains `h.projection p` for
  `p ∈ P ∩ K` (`projection_mem_compactLeviImage`).
- `leviHalfCharacter_projection_eq_one`: the half modulus of `M` on `U` is
  `1` on that image. The modulus is a continuous character to `ℝ>0`, hence
  trivial on the compact image, and the half modulus has the same kernel.
- `unramifiedCharacter_projection_eq_one`: every unramified character is
  `1` there, for the same reason applied to each `ν i`.
- `leviInflated_twist_apply_of_mem`: on `P ∩ K`, the inflated inducing
  representation of every twist `A ⊗ z` agrees with `A ∘ h.projection`.
- `mem_fixedVectors_twist`: for `Q ⊆ K`, a vector fixed by `A ∘ h.projection`
  on `P ∩ Q` is fixed by the inflated action of every twist.
- `sourceTestVector_twist_eval_eq`: let `Q ⊆ K` be compact open. The test
  sections `sourceTestVector` of the twists (supported on `P Q`, with value
  `v` at `1`) agree on `K`. On `K ∩ P Q` one writes `k = p q` with `p ∈ K`
  and uses `leviInflated_twist_apply_of_mem`. Off `P Q` both vanish.
- `compactTestVector`, for `hδ` (unimodular modulus of `U`) and `hPK`
  (`G = P K`): the image of the untwisted test section under the Library's
  compact-picture isomorphism `unramifiedLeviInductionCompactEquiv`.
- `unramifiedLeviInductionCompactEquiv_sourceTestVector`: for every twist,
  the compact picture of the twisted test section is `compactTestVector`.
- `compactIntertwiningOperator_compactTestVector_eval_one`. Let `P' = M ⋉ U'`
  be a second decomposition with `G = P' K`, and `qν` a measure on the
  quotient by `U ∩ U'`. Let `J` be an intertwiner between the twisted
  inductions that satisfies the standard integral relation `HasIntegral`.
  Assume the local product condition `HasSourceLocalProduct P U U' Q` and that
  the orbit `S = sourceTestOrbit U U' Q` has finite `qν`-mass. Then the
  compact picture of `J` sends `compactTestVector` to a vector with value
  `qν(S) • v` at `1`. The proof combines the previous item with the Library's
  `HasIntegral.eval_one_sourceTestVector` (`StandardIntertwiningNonvanishing`).

## Positive values of rational functions

`RationalFunctionPosAt G hp hG f z` says: there is a presentation `f = m / n`
by regular functions with `n(z) ≠ 0` and `m(z) / n(z) = r` for some real
`r > 0`. It is the strict form of the Library's `RationalFunctionNonnegAt`
(`DynamicOppositeUnitaryScalarStatement`). By `rationalFunction_value_eq`
the value does not depend on the presentation.

- `RationalFunctionPosAt.nonnegAt`: a positive value is nonnegative.
- `RationalFunctionPosAt.inv`: `f⁻¹` has the positive value `r⁻¹`, through
  the presentation `n / m`. Here `m(z) ≠ 0` because `r ≠ 0`.
- `RationalFunctionPosAt.ne_zero`: such an `f` is nonzero. Otherwise
  `0 = 0 / 1` would give the value `0` by `rationalFunction_value_eq`.

## Linear images and positivity of continued operators

This part is generic, in the setting of `continuedOperator_adjoint`
(`DynamicOppositeUnitaryNonnegativity`): `L` is a connected reductive group
scheme over a nonarchimedean local field, and
`p : RationalOperatorContinuationData Ω A` continues `A : Ω → (V →ₗ W)` with
denominator `d_p` and polynomial numerator `N_p = d_p • A` on `Ω`.

- `continuedOperator_map_eq_of_eqOn`. Let `E : W →ₗ X` be linear and `D` a
  nonempty open subset of `Ω`. If `E (A w v) = x` for all `w ∈ D`, then
  `E (p.continuedOperator z v) = x` at every regular point `z` of `p`.

  Proof. Fix a linear functional `ℓ` on `X`. Polynomiality of the numerator
  gives a regular function `a` with `a(w) = ℓ (E (N_p(w) v))`. The regular
  function `a − ℓ(x) d_p` vanishes on `D`, so it is `0` by the identity
  theorem `rationalUnramifiedRegular_eq_zero_of_isOpen`. Evaluating at `z`
  and dividing by `d_p(z) ≠ 0` gives `ℓ (E (cont z v) − x) = 0`. Since `ℓ`
  is arbitrary, `E (cont z v) = x`.
- `continuedCompositeRationalScalar_posAt`. These are the hypotheses of
  `continuedCompositeRationalScalar_nonnegAt`, plus two more: `sW` is
  definite (`sW u u ≠ 0` for `u ≠ 0`), and `p.continuedOperator z v ≠ 0`.
  Then the extracted coefficient `f` has `RationalFunctionPosAt f z`. The
  Library's presentation of `f` has value `(sV v v)⁻¹ sV v (q.cont z (p.cont z v))`
  at `z`. By `continuedOperator_adjoint` and `z† = z` this equals
  `(sV v v)⁻¹ sW (p.cont z v) (p.cont z v)`, a quotient of two positive
  reals.

## Evaluation at `1`

- `compactPictureEvalOne h K A` is `φ ↦ φ(1)` on the compact picture, as a
  linear map, with `compactPictureEvalOne_apply`.
- `CompactInductionPicture.exists_eval_ne_zero`: a nonzero vector of the
  compact picture has a nonzero value at some point of `K`.

## The uniform form of IV.1 (10)

`exists_forwardCompactFamily_eval_one_eq`. Let `χ` be a cocharacter,
`P = parabolic χ`, `P̄ = oppositeParabolic χ`, `M = levi χ`, `K` compact open
with `G = P K = P̄ K`, and `A` a smooth representation of `M(F)`. For every
`v ∈ A` there are `e` in the compact picture of `Ind_P A` and `c ≠ 0` with

`(conditionalForwardCompactFamily … z e)(1) = c • v`

for every `z` in `forwardFullDomainRegion χ K hK A`. The operator is the
compact picture of the Library's forward integral `J_{P̄|P}(z)`.

Proof. Choose a compact open subgroup `Q ⊆ K` that fixes `v` under
`A ∘ projection` on `P ∩ Q` and has a factorization along `χ`
(`exists_factored_compactOpen_subset`, `DynamicOppositeNonvanishing`). Put
`e = compactTestVector … Q v`. Let `c` be the mass of the image of `Q ∩ Ū`
in the quotient `(U ∩ Ū) \ Ū` under the forward quotient measure. It is positive and
finite by `compactOpenQuotientOrbit_mass`. Apply
`compactIntertwiningOperator_compactTestVector_eval_one` with
`forward_hasSourceLocalProduct` and the integral relation
`conditionalForwardFamily_spec`.

## The target

`ConditionalDynamicOppositeUnitaryPositiveStatement` quantifies over the same
data as `ConditionalDynamicOppositeUnitaryNonnegStatement`:

- a nonarchimedean local field `F`, an affine group scheme `G` over `F` of
  locally finite type, a cocharacter `χ`, the structural premises `hRefl`,
  `hCST`, `hG : IsConnectedReductive G`, and `P = parabolic χ`,
  `P̄ = oppositeParabolic χ`, `M = levi χ`;
- a compact open subgroup `K` with `G(F) = P K` (`hPK`) and `G(F) = P̄ K`
  (`hOppK`), and the split hypotheses `_hKsplit`, `_hOppKsplit` of the
  Hermitian adjunction target (the Levi projections send `P ∩ K` and
  `P̄ ∩ K` into `K`);
- a smooth complex representation `A` of `M(F)` with
  `_hA : IsUnitarizable A.representation`;
- the conditional data of `conditionalCanonicalRationalScalar`: forward and
  reverse continuations `p`, `q`, nonempty open sets `DForward` and
  `DReverse` inside the forward and reverse full convergence domains, and a
  nonempty open set `D` of parameters with irreducible induction (`hi`);
- `_hdag`: `z ↦ z† = z̄⁻¹` maps `DForward` into
  `reverseFullDomainRegion χ K hK A`.

The conclusion is the conjunction of

- `conditionalCanonicalRationalScalar … p q … ≠ 0`, and
- for every `z ∈ p.regularRegion ∩ q.regularRegion` whose value lies in
  `unitaryUnramifiedCharacters (normCharacters χ)`, both
  `RationalFunctionPosAt … j_P z` and `RationalFunctionPosAt … j_P⁻¹ z`.

Remarks on the hypotheses.

- The regular regions are those of the supplied data `p` and `q`. The
  target quantifies over all data, so it applies at every unitary point
  where some pair of data is regular.
- Points outside the common regular region are excluded on purpose. `j_P`
  can have poles at unitary points. For `GL₂` and `A = χ₁ ⊗ χ₂` with
  `χ₁ = χ₂` unramified, Harish-Chandra's `μ`, a nonzero constant multiple of
  `j_P⁻¹`, vanishes at the unitary point `s = 0` of the family
  `χ₁|·|^s ⊗ χ₂|·|^{-s}`, so `j_P` has a pole there.
- `_hdag`, `_hKsplit`, `_hOppKsplit` and `_hA` play the same roles as in
  `ConditionalDynamicOppositeUnitaryNonnegStatement`. See
  `DynamicOppositeUnitaryNonnegativity.md` for why `_hdag` is a hypothesis.
  The underscore names are used only in the reduction.
- `A` need not be square-integrable. Waldspurger states IV.3 (6) for
  square-integrable `π`, but the argument at regular unitary points needs
  only a positive definite invariant form.

## The reduction

`conditionalDynamicOppositeUnitaryPositive_of_hermitianAdjunction` takes the
Hermitian adjunction target `H` and proves the target.

- `exists_unitary_mem_regularRegion_inter`: some unitary unramified
  character is regular for both `p` and `q`. The denominators of `p` and `q`
  are nonzero regular functions, since they do not vanish on the nonempty
  domains. By the Library's `rationalUnramifiedRegular_exists_unitary_finset_ne_zero`
  (`RationalUnitaryNonvanishing`), one unitary character avoids the zeros of
  both.
- `conditionalCanonicalRationalScalar_posAt`: positivity at one unitary
  common regular point `z`, for an invariant positive form `b` and a vector
  `v ≠ 0` of `A`. Take `e` and `c` from `exists_forwardCompactFamily_eval_one_eq`.
  By `continuedOperator_map_eq_of_eqOn` with `E = compactPictureEvalOne` and
  the open set `DForward`, `(p.continuedOperator z e)(1) = c • v ≠ 0`. So
  `p.continuedOperator z e ≠ 0` and `e ≠ 0`. Apply
  `continuedCompositeRationalScalar_posAt` with the compact-picture pairings
  `compactPictureSesq` for `P` and `P̄`. Definiteness is
  `compactPictureHermitianPairing_self_ne_zero`. Adjointness on `DForward` is
  `H` with `_hdag`. `conditionalCanonicalRationalScalar_eq_extraction`
  identifies `j_P` with the coefficient extracted by `e` and
  `(e, e)_P⁻¹ (e, ·)_P`. Finally `z† = z`
  (`unramifiedConjInv_eq_self_of_mem_unitary`).
- `conditionalCanonicalRationalScalar_unitaryPositive`: under the same
  hypotheses, `j_P ≠ 0` and both `j_P` and `j_P⁻¹` are positive at every
  unitary common regular point. Nonvanishing follows from positivity at the
  point given by `exists_unitary_mem_regularRegion_inter`, via
  `RationalFunctionPosAt.ne_zero`. The inverse uses
  `RationalFunctionPosAt.inv`.
- The reduction chooses `b` from `_hA`. For `v` it takes a nonzero value of
  the compact-picture vector of a normalized compact coefficient
  (`exists_normalized_compactCoefficient`, `DynamicOppositeCanonicalScalar`),
  found by `CompactInductionPicture.exists_eval_ne_zero`. Any nonzero vector
  of `A` would do; this choice avoids a separate hypothesis `A ≠ 0`.

The module uses the local instances of `DynamicOppositeCanonicalScalar`, and
in the last section also the Borel instances
`hermitianAdjunctionPointMeasurable` and `hermitianAdjunctionPointBorel` of
`DynamicOppositeHermitianAdjunctionStatement`.

## Not proved here

- The Hermitian adjunction target, and the inclusion `_hdag`.
- Waldspurger's IV.3 (6) in full. The target says nothing at unitary points
  where `p` or `q` is not regular, even where `j_P` itself is regular.
- Any statement at unitary points where `j_P` has a pole.

## Axioms

The proved results use only `propext`, `Classical.choice` and `Quot.sound`.
The target is a `def … : Prop` and introduces no axioms.
