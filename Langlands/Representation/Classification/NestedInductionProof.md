# Proof of normalized induction in stages inside a product Levi

Author: Worker 379.

`Langlands.normalizedNestedInduction` proves exactly
`Langlands.NormalizedNestedInductionStatement.{uF,uV,uM,uW}` from
`Langlands.Representation.Classification.NestedInductionStatement`. It is the
pair of `Langlands.NestedInductionProof.comparison :
NestedInduction.Comparison.{uF,uV}` and
`Langlands.NestedInductionProof.quotientTransport :
NestedInduction.QuotientTransport.{uF,uV,uM,uW}`. The theorem has no
hypotheses, and the four universes are independent; its level parameters are
`uF, uV, uM, uW` in that order. The statement pair and its imports are
unchanged. The only axioms used are `propext`, `Classical.choice` and
`Quot.sound`.

## Notation

Fix the prime `p`, the field `F`, its topological data `T`, an ordered shape
`B`, a refinement `Q` of `B`, `D := B.flatten Q`, and a refinement `R` of `D`.
The constructed composite is `S := B.composeRefinement Q R` and
`h := B.flatten_composeRefinement Q R : D.flatten R = B.flatten S`. Write

- `P_Q`, `P_S` for the refined parabolics `refinedParabolic F.Carrier B Q` and
  `refinedParabolic F.Carrier B S` in `B.Levi F.Carrier`, and `P_R` for
  `refinedParabolic F.Carrier D R` in `D.Levi F.Carrier`;
- `ℓ_Q`, `ℓ_S`, `ℓ_R` for the corresponding `refinedLeviProjection`s;
- `e_Q := flattenedLeviEquiv F.Carrier B Q : D.Levi ≃* refinedLevi B Q`, and
  similarly `e_S`, `e_R`;
- `δ_Q`, `δ_S`, `δ_R` for the positive refined half-moduli
  `T.refinedLeviHalfModulus`.

Induced functions satisfy `f(q g) = δ(ℓ(q)) • η(ℓ(q))(f(g))` and the group
acts by right translation, as in `Langlands.Representation.Induction.Definitions`.

## Group-level facts (section `Groups`)

All of these lemmas are stated for an arbitrary commutative ring `K`. They are
proved by passing through the injective block-diagonal embeddings
`X.leviEmbedding K : X.Levi K →* GL_n(K)`, where refined parabolics become
ordinary block parabolics of flattened shapes.

- `composedParabolic_flatten` identifies the composite parabolic of a
  refinement with the parabolic of the flattened shape. It specializes the
  published coordinate lemma `BlockShape.composedParabolic_eq_of_coordinates`
  (`Langlands.Group.GL.RefinementCoordinates`).
- `mem_refinedParabolic_iff`: `g ∈ P_Q` exactly when the block-diagonal
  matrix of `g` lies in `(B.flatten Q).parabolic`.
- `flattenedLeviEquiv_leviProjection` and `flatten_leviProjection_embedding`
  compute the flattened Levi projection of an embedded element of `P_Q` as
  `e_Q⁻¹ (ℓ_Q q)`. They use `composedLeviProjection_parabolicRefinementEquiv`
  and `BlockShape.leviRefinementEquiv_flatten`.
- `leviCast h : X.Levi K ≃* Y.Levi K` is the group transport along a shape
  equality, defined by `subst`. `leviProjection_cast` and
  `leviEmbedding_cast` show that it commutes with Levi projection and with
  the block-diagonal embedding.
- `mem_composeRefinement_iff`: `g ∈ P_S` exactly when `g ∈ P_Q` and
  `e_Q⁻¹ (ℓ_Q g) ∈ P_R`. The proof rewrites along the actual equality `h`.
- `composeRefinement_leviProjection`: for such `g`,
  `e_S⁻¹ (ℓ_S g) = leviCast h (e_R⁻¹ (ℓ_R (e_Q⁻¹ (ℓ_Q g))))`.

## Moduli (section `Modulus`)

- `leviModulus_flatten`: for every `m` in the refined Levi,
  `leviModulus X m.val * refinedLeviModulus X Y m = leviModulus (X.flatten Y) (e⁻¹ m)`.
  This unfolds the published full-modulus calculation
  `PadicField.TopologicalData.composedLeviModulus_flattened`
  (`Langlands.Representation.Parabolic.FlattenedRefinementModulusCalculation`).
- `leviModulus_cast`: `leviModulus` is invariant under `leviCast`.
- `refinedLeviModulus_compose`: for `g ∈ P_S` with middle part `x := ℓ_Q g`
  and fine part `y := ℓ_R (e_Q⁻¹ x)`,
  `refinedLeviModulus B S (ℓ_S g) = refinedLeviModulus B Q x * refinedLeviModulus D R y`.
  The proof applies `leviModulus_flatten` three times, for `(B,S)`, `(B,Q)`
  and `(D,R)`. It identifies the two flattened shapes through
  `composeRefinement_leviProjection` and `leviModulus_cast`. Each outer factor
  is rewritten by `refinedOuterModulus_projection`
  (`Langlands.Representation.Parabolic.RefinementComposition`), and then the
  common factor `leviModulus B g` is cancelled.
- `refinedLeviHalfModulus_compose`: the same product formula for the
  positive half-moduli, `δ_S(ℓ_S g) = δ_Q(x) · δ_R(y)`.

`cast_apply` records that the representation transport `h ▸ ω` satisfies
`(h ▸ ω)(leviCast h x) = ω x`. It is proved by `subst`.

## The comparison (section `Comparison`)

The construction allows an arbitrary representation `ωB` of
`(B.flatten S).Levi` on the same space `V`, together with a hypothesis
`hω : ∀ x, ωB (leviCast h x) = ω x`. The clause itself uses `ωB := h ▸ ω` and
`hω := cast_apply h ω`. The quotient clause uses the same construction for
a twisted representation. The carriers are the actual smooth covariant-function
subtypes `Induction.SmoothFunctions`:

- `Mid`: the carrier of the fine induction from `P_R` to `D.Levi`;
- `Iter`: the carrier of `middleInduced T B Q (middleInduced T D R (Rep.of ω))`;
- `Direct`: the carrier of `middleInduced T B S (Rep.of ωB)`.

`mid_cov`, `iter_cov` and `direct_cov` restate the three covariance laws on
values. The statement places no smoothness assumption on `ω`. Every
function in these carriers is nonetheless smooth because it has an open
right stabilizer, and the construction only uses those carrier properties.

**Forward map.** `forward f := g ↦ f(g)(1)`. For `s ∈ P_S`, write
`s ∈ P_Q` with `e_Q⁻¹ (ℓ_Q s) ∈ P_R` (`mem_composeRefinement_iff`). Outer
covariance of `f` at the middle identity (`iter_cov_one`) and inner
covariance of `f(g)` (`mid_cov_one`) give
`f(s g)(1) = δ_Q(ℓ_Q s) • δ_R(·) • ω(·)(f(g)(1))`. Then `forward_scalar`
converts this into the direct covariance law, using
`composeRefinement_leviProjection`, `hω` and
`refinedLeviHalfModulus_compose`. `forward_scalar` is stated with a free
vector to keep the rewrites small. An open right stabilizer of the
iterated function `f` also stabilizes `g ↦ f(g)(1)`.

**Inverse map.** For `f` in `Direct`, set

```text
inverseValue f g m := δ_Q(e_Q m)⁻¹ • f((e_Q m).val * g).
```

- *Inner covariance* (`inverseValue_cov`). Let `r ∈ P_R`. By
  `section_direct`, `(e_Q r).val ∈ P_S`, with fine Levi part
  `leviCast h (e_R⁻¹ (ℓ_R r))`. Its half-modulus is
  `δ_S = δ_Q(e_Q r) · δ_R(ℓ_R r)`. Direct covariance along this element,
  `hω`, and cancellation of `δ_Q(e_Q r)` against the inverse scalar give the
  covariance law of `m ↦ inverseValue f g m` for `P_R`.
- *Inner smoothness* (`inverseValue_smooth`). Choose an open right stabilizer
  `K` of `f`. For fixed `g`, the map `m ↦ g⁻¹ (e_Q m).val g` is a continuous
  homomorphism `D.Levi → B.Levi`; it is continuous by
  `flattenedLeviEquivContinuous`. Pull `K` back along this map and intersect
  with the pullback, along `e_Q`, of the open kernel of `δ_Q`
  (`isOpen_ker_refinedLeviHalfModulus`). The resulting open subgroup fixes
  the inner function at every argument `m`, including its scalar factor.
  `inverseInner` packages the inner function with `Induction.smoothFunctionOf`.
- *Outer covariance* (`inverseValue_outer`). `direct_projQ` shows
  `f(y g) = f((ℓ_Q y).val g)` for every `y ∈ P_Q`. The element
  `u := y · section(ℓ_Q y)⁻¹` lies in `P_S` with trivial projection `ℓ_S u = 1`,
  so direct covariance along `u` has trivial scalar and action. Apply this to
  `y := section(e_Q m) · q` and cancel `δ_Q` by multiplicativity. This gives
  `inverseValue f (q g) m = δ_Q(ℓ_Q q) • inverseValue f g (m · e_Q⁻¹(ℓ_Q q))`.
  This is the outer covariance law: the middle representation acts on the
  inner function by right translation through `e_Q⁻¹`.
- *Outer smoothness*. The same stabilizer `K` of `f` fixes `inverse f` at
  every `g` and every `m`.

**Inverse laws.** `forward_inverse` is evaluation of `inverse` at `m = 1`,
where `δ_Q(e_Q 1) = 1`. `inverse_forward` uses `iter_section`:
`f((e_Q m).val g)(1) = δ_Q(e_Q m) • f(g)(m)`. This holds by outer covariance
along the refined Levi section of `e_Q m` (`section_scalar`), followed by
`inv_smul_eq_iff₀`. Equality in the nested subtypes is proved by two
`Subtype.ext` steps and function extensionality at each level.

**Equivalence.** `comparisonEquiv` is the `Representation.Equiv` with
underlying maps `forward` and `inverse`. Additivity, scalar compatibility
and intertwining with right translation hold by `rfl` after the subtype
extensionality steps. In `comparison`, both required evaluation formulas
hold by `rfl`: `(E f)(g) = f(g)(1)` is the definition of `forward`, and
`(E.symm f)(g)(m) = δ_Q(e_Q m)⁻¹ • f((e_Q m).val * g)` is the definition of
`inverseValue`. The section raises `maxHeartbeats` to the finite value
1600000.

## The quotient transport (section `Quotient` and `quotientTransport`)

Three helper lemmas are proved first.

- `isClosed_refinedParabolic`: `P_Q` is closed in `B.Levi`, as a product of
  the closed block parabolics `(Q i).isClosed_parabolic`.
- `normalizedRefinedInducedMap_surjective`: for smooth representations `σ`, `τ`
  of the refined Levi and a surjective intertwiner `f`, the map
  `T.normalizedRefinedInducedMap B Q f` is surjective. This specializes
  the published `Induction.smoothInductionSurjectivity`
  (`Langlands.Representation.Induction.SurjectivityProof`) to the group
  `B.Levi F.Carrier` and the closed subgroup `P_Q`. Compact open subgroups
  are cofinal by `T.leviCompactOpen` (`Langlands.Group.GL.CompactOpen`).
  The twisted and inflated inducing representations are smooth by
  `isSmooth_comp` along the continuous projection `ℓ_Q` and by
  `isSmooth_twist_iff` with the open kernel of the parabolic half-modulus.
- `fineTwist_transport`: for any fine shape `X` and any equality
  `h : X = B.flatten S`, a surjection from
  `middleInduced T B S (Rep.of (h ▸ T.leviRealPowerTwist X (-v₀ + 0) ω.ρ))`
  onto `π` gives a surjection from
  `innerInduced T B S (fineTwist T B S (h ▸ ω) (h ▸ v₀) 0)` onto `π`.
  The proof substitutes `h`, generalized over `X`. After the substitution,
  the two induced representations agree by definition. This is the
  compatibility of the shape transports with `fineTwist`: both `ω` and its
  exponent family `v₀` are transported by the same `h`, and the fine
  exponent stays `-v₀ k + 0`, without any sign change.

**Proof of `quotientTransport`.** Let
`ω'' := T.leviRealPowerTwist (D.flatten R) (k ↦ -v₀ k + 0) ω.ρ` and
`M := middleInduced T D R (Rep.of ω'')`. Unfolding `fineTwist` and
`middleInduced`, the source of `qFineMiddle` is by definition `M`, so
`qFineMiddle` is an intertwiner `M → σ`.

1. `M` is smooth by `T.isSmooth_normalizedRefinedInduced`. Then `σ` is smooth
   by `isSmooth_of_surjective`, because `qFineMiddle` is surjective.
   Smoothness is proved here; it is not a premise.
2. The same linear map intertwines the pullbacks of `M` and `σ` along
   `e_Q⁻¹`. Both pullbacks are smooth because `e_Q⁻¹` is continuous. Hence
   `q3 := T.normalizedRefinedInducedMap B Q (·)` is a surjection
   `middleInduced T B Q M → middleInduced T B Q σ` by step 1 and
   `normalizedRefinedInducedMap_surjective`.
3. `E := comparisonEquiv` for `ω''`, with `ωB := h ▸ ω''` and
   `hω := cast_apply h ω''`, identifies `middleInduced T B Q M` with
   `middleInduced T B S (Rep.of (h ▸ ω''))`.
4. `qMiddleCoarse ∘ q3 ∘ E.symm` is a composite of surjections, hence a
   surjection onto `π`. `fineTwist_transport` turns it into the required
   `qFineCoarse`.

`fineTwist_transport` is applied with the explicit composite
`B.composeRefinement Q R` rather than the local name `S`. This keeps the
transported terms syntactically equal to those of the goal. Otherwise
elaboration would attempt a costly definitional unfolding of the two
shapes.

No case distinction on the rank or on empty block families occurs anywhere.
The argument therefore covers rank zero and empty families uniformly.
All helper constructions are internal to this module. The comparison
helpers are private, and the remaining lemmas live in the namespace
`Langlands.NestedInductionProof`.

## Provenance

The original source is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
441–472, registered as `bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Printed pp.443–446 (PDF pages 4–7) were read for this proof:

- §1.2 (p.443) defines algebraic (smooth) representations;
- §1.8(a) (p.444) defines induction with the factor `mod_U^{1/2}`, right
  translation, and one open right stabilizer per function;
- Proposition 1.9(a,c) (p.445) gives exactness and induction in stages, and
  the following paragraph says that the normalizing factors must be checked
  to be compatible;
- §2.2 (p.446) indexes standard Levis of `GL(n,F)` by ordered partitions,
  with subpartitions giving smaller Levis;
- Proposition 2.3(a,c) (p.446) gives exactness and transitivity
  `i_{G,M} ∘ i_{M,N} = i_{G,N}`.

No errata file for this paper was found in the central library or the
literature index.

The source theorem concerns functors on smooth representations. The Lean
theorem is a derived, internal formulation, and the source states none of
the following:

- the inputs `ω` are arbitrary rather than smooth;
- the ordered finite-coordinate transports along `h` and `leviCast`;
- the product-Levi endpoint `B.Levi` rather than an ambient `GL_n`;
- the two explicit evaluation formulas;
- the quotient interface.

Their proofs are the constructions above. The source's normalization
compatibility corresponds here to `refinedLeviHalfModulus_compose`. The
exactness used is only the surjectivity of normalized refined induction on
smooth inputs, obtained from the Library's generic smooth-induction lifting.

The forward/inverse pattern (evaluation at the inner identity, the inverse
half-modulus scalar, and the uniform open stabilizer) follows the private
construction in `Langlands.Parabolic.normalizedRefinementInductionTransitivity`
(`Langlands.Representation.Parabolic.RefinementInductionTransitivityProof`).
That proof treats the ambient `GL_n` endpoint. The present module writes its
own construction for the coarse product Levi and does not use that proof's
private definitions.

## Scope

This module proves no composed-to-flattened induction theorem, no
flattened-modulus statement beyond the internal product formula above, no
tensor compatibility, no general exactness theorem, and no analytic support
or regular-head result. It adds no irreducibility, smoothness, admissibility,
unitarity, finite-length or positive-rank hypothesis.
