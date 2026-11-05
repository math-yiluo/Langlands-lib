# Parabolic-left coverings over complete valuation rings

This module proves the local covering `G(K) = P(K) · G(R)` for an actual
subgroup inclusion `i : P ⟶ G` of group schemes over `Spec R`. Here `R` is
a valuation ring with fraction field `K`, adically complete for a maximal
ideal with finite residue ring. The quotient is not constructed. It is an
explicit morphism `q : G.X ⟶ Q` over `Spec R` with these hypotheses:

* `q.left` is flat, surjective and quasi-compact, and `Q` is proper over `R`;
* `i` is a monomorphism, and `P` is smooth and affine over `R`;
* the special fibre of `P` over `R / I` is connected;
* the exact coset criterion `hfib`: for every `T` over `Spec R` and points
  `g h : T ⟶ G.X`, `g ≫ q = h ≫ q` holds exactly when `g⁻¹ * h` lies in the
  image of `i` on `T`-points.

No integral or rational point of `Q`, of a fibre of `q`, or of `P` is assumed.
All objects share an arbitrary universe `u`.

## Declarations

* `integral_lifts_of_flagQuotient`: every `R`-valued point `p` of `Q` is
  `g ≫ q` for some `R`-valued point `g` of `G`. This needs completeness and
  the finite residue ring, but not a valuation ring or properness.
* `exists_ringPoint_changeRing_eq`: for `R` a valuation ring with fraction
  field `K` and `Q` proper over `R`, every `K`-valued point of `Q` is the
  change of ring of an `R`-valued point.
* `exists_mul_integral` and `range_mul_integral_eq_univ`: every morphism
  `ringTest R K ⟶ G.X` factors as `(h ≫ i) * (ringTestMap (R → K) ≫ k)`,
  with `h` a `K`-point of `P` and `k` an `R`-point of `G`. The second theorem
  states this as an equality of the pointwise product set with `Set.univ`.
* `exists_mul_rationalPoint`: the same factorization for points
  `Over.mk (Spec.algebraMap R K) ⟶ G.X`, where the integral factor is a
  section of `G` over `Spec R` restricted along `Spec K → Spec R`.
* Model form, for `M : IntegralModel R K G`, `N : IntegralModel R K P` and a
  model morphism `φ : N.Hom M f` over a generic morphism `f : P ⟶ G` of
  `K`-groups. Here `R` is a valuation ring whose residue field is finite and
  which is complete for its maximal ideal. `q` is a morphism from `M.group.X`,
  and the hypotheses above are required for `φ.hom`, with `N.IsSmooth` and
  `N.HasConnectedSpecialFibre`. Affineness of `N.group` comes from
  `IntegralModel`.
  * `genericPoint_eq`, `genericPoint_map` and `integralPointMap_eq` are
    transport identities between `rationalPoints G` and fraction-field points
    of the model. They use the supplied `genericIso` and
    `baseChangeBasePointsEquiv`.
  * `exists_parabolic_integral_factor`: every `g : rationalPoints G` equals
    `rationalPoints.map f h * M.integralPointMap x` for some
    `h : rationalPoints P` and some `x : M.integralSections`.
  * `parabolicIntegralFactor` is a chosen such pair `(h, x)`, and
    `parabolicIntegralFactor_spec` states the factorization for it.
  * `range_mul_integralPoints_eq_univ`: `Set.range (rationalPoints.map f) *
    M.integralPoints = Set.univ`. This is exactly the covering hypothesis
    `hcover` that `coefficientIntegralPoints_covering` in
    `Langlands.GroupScheme.IntegralModel.CoefficientPoints` takes.

## Implemented proof

*Lifting.* Let `p₀` be the section of `Q` that corresponds to `p` under
`rationalPointEquiv`. The published `Dynamic.flagQuotientFiber` is the actual
pullback of `q` along `p₀`. `Dynamic.flagQuotientFiberModObj` gives it the
action `h • x = x · i(h)⁻¹` of `P`. With `hfib` and the monomorphism `i`, its
shear is invertible (`Dynamic.flagQuotientFiber_leftSMul_isIso`). The fibre is
flat, surjective and quasi-compact over `R`, because these properties of
`q.left` are stable under base change. `IntegralTorsorPoint.integralTorsorPoint`
therefore gives an `R`-point of the fibre. Composing it with the fibre
inclusion gives the required `R`-point of `G`, because the fibre inclusion
followed by `q` is the structure map followed by `p₀`.

*Properness.* Mathlib's `IsProper.eq_valuativeCriterion` gives the valuative
criterion for `Q.hom`. The square from `Spec K → Q` and `𝟙 (Spec R)` has a
lift `Spec R → Q`, which is a section of `Q`. Its restriction to `Spec K` is
the given point (`fac_left`, via `rationalPointEquiv_left`).

*Covering.* Given `g`, extend `g⁻¹ ≫ q` to an `R`-point `y` of `Q` and lift
`y` to an `R`-point `k` of `G`. Then `g⁻¹ ≫ q` equals the restriction of
`k` followed by `q`, so `hfib` gives `g * k|_K = h ≫ i` for some `K`-point
`h` of `P`. Using `GrpObj.comp_inv`, we get `g = (h ≫ i) * (k⁻¹)|_K`. Applying
the criterion to `g⁻¹` instead of `g` puts the parabolic factor on the left.

*Model transport.* Send `g` to a fraction-field point of `M.group` through
`genericIso.inv` and `baseChangeBasePointsEquiv`, factor it, and transport back.
The generic factor is carried to `G` by `φ.generic_comm`, which is the step
that produces `rationalPoints.map f`. The integral factor becomes
`M.integralPointMap x` by definition. Both transports are monoid
homomorphisms, so the product is preserved. The chosen pair
`parabolicIntegralFactor` is obtained by `Classical.choose` from
`exists_parabolic_integral_factor`.

## Provenance and scope

This module is a derived local step. It follows the proof of Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), Theorem B.2.5,
printed pp.543–544 / PDF pp.548–549, which proves
`G(F_v) = P(F_v) G(𝒪_{F_v})`. That proof uses the valuative criterion for the
proper quotient `G/P`, Lemma B.2.3 over fields, and Lemma B.2.4 for the
torsor fibres of `G(𝒪_v) → (G/P)(𝒪_v)`. Our version differs in three ways.
The quotient's geometry (flatness, surjectivity, quasi-compactness,
properness) and the exact coset criterion `hfib` are explicit hypotheses, not
a construction of `G/P` for reductive `G` and parabolic `P`. Lemma B.2.3 is
not used, because the argument starts from a given `g`. The Henselian
hypothesis of Lemma B.2.4 is replaced by adic completeness of `R`. The
registered October 2026 errata does not correct these passages.

The module does not construct reductive or parabolic models, prove that `G/P`
exists or is proper, specialize to completions of global fields, prove
integral maximality, or prove
`Langlands.Global.IntegralIwasawaFamily.ExistenceStatement`.
