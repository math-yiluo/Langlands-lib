# Restriction of analytic points along an extension of the ground field

This unit works with an extension `K → L` of complete non-Archimedean fields.
It takes a `K`-algebra map `f : A →ₐ[K] B` from a presented `K`-algebra `A` to a
presented `L`-algebra `B`, and constructs the induced continuous map
`Space L Q → Space K P` between the Library's polynomial-locus analytifications.
A point of the analytification of `B` over `L` gives a multiplicative seminorm
on `B`. The image point gives the seminorm on `A` obtained by composing with
`f`. The main case is the base change `B = L ⊗[K] A`, with the map
`a ↦ 1 ⊗ a`. Here the unit gives the canonical continuous map
`(X_L)^an → X^an` for `X = Spec A`. The unit does not identify `(X_L)^an` with
a ground-field extension of `X^an`, and it does not state that the map is
surjective.

## Provenance

Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed
p.19, final paragraph of the proof of Proposition 5.11(3), uses the
analytification of [CT]. It is described as "compatible with … extension of the
ground field", and "since the formation of `X^an` respects extension of the
ground field", Conrad identifies `X(k) → X(k')` with
`X^an(k) → (X^an)_{k'}(k')`. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990), §2.3, printed pp.32–33/PDF pp.46–47, introduces the ground field
extension functor `X ↦ X ⊗̂ K = M(A ⊗̂ K)` for a non-Archimedean field `K`
over `k`. The same passage defines affinoid spaces over `k` as `K`-affinoid
spaces for varying `K` over `k`. A morphism between two of them is a morphism of
locally ringed spaces induced by a bounded `k`-homomorphism of the affinoid
algebras. §3.1, printed
p.48/PDF p.62, gives the ground field extension functor
`k-An → K-An` on `k`-analytic spaces, and treats analytic spaces over varying
ground fields as one category. Remark 3.4.2, printed p.64/PDF p.78, says that
for `X = Spec(A)` the space `X^an` is the set of multiplicative seminorms on `A`
that restrict to the norm of `k`. The same remark describes points of `X^an`
through points of `X` with values in non-Archimedean fields over `k`, which are
compared along embeddings of such fields. For trivially valued `k`,
Theorem 3.5.1(v), printed p.68/PDF p.82, states that `X ↦ X^an` commutes with
extension of the ground field. The registered source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

No source writes the map below as a formula. The seminorm description is
derived from Remark 3.4.2: a point of the analytification of `B` over `L` is a
multiplicative seminorm on `B` that extends the norm of `L`. Composing with `f`
gives a multiplicative seminorm on `A` that extends the norm of `K`, because
`K → L` preserves norms. The chart construction is modelled on the published
`AffineAnalytificationMap` unit, which treats the case `L = K`. The generator
values, the radius levels, the Tate evaluation chart maps and the gluing are
derived implementation choices for the Library's model. So is the presentation
of `L ⊗[K] A` by the same generators.

## Hypotheses

All declarations lie in `Langlands.Analytic.AffineAnalytification`. The fields
`K` and `L` are nontrivially normed, and `L` is ultrametric. `A` is a commutative
`K`-algebra with `P : FinitePolynomialPresentation K A`. `B` is a commutative ring
that is both an `L`-algebra and a `K`-algebra, with
`Q : FinitePolynomialPresentation L B`. The map `f : A →ₐ[K] B` is an arbitrary
`K`-algebra map. The universes of `K`, `L`, `A` and `B` are independent.

The hypotheses are added section by section, as each part needs them. From
`extensionNormedAlgebra` on, `L` is a normed `K`-algebra (`NormedAlgebra K L`).
Since `L` is a normed field, `K → L` then preserves norms. From the chart maps on,
`K` is ultrametric and `L` is complete. From `extensionTateMap_polynomialMap` on,
the `K`-algebra structure of `B` factors through `L` (`IsScalarTower K L B`).
From the continuous map on, `K` is complete, as the spaces over `K` require. No
norm on `A` or `B`, positive arity, nonemptiness, injectivity, surjectivity or
finiteness of `f` is assumed, and `L` need not be finite over `K`.

## Generator values and radius levels

- `extensionValue K L P Q f k t : algebra L Q k` is the image of
  `f (P.map (X t))` in the `k`-th chart algebra of `Q`, under the published
  coordinate-algebra map `PolynomialLocus.algebraMap`.
- `exists_extensionValue_le` gives a radius index `l` of `K` with
  `‖extensionValue K L P Q f k t‖ ≤ radius K l` for all `t`. It applies
  `exists_radius_gt` to the sum of the norms. `extensionMinimalLevel K L P Q f k`
  is the least such index, chosen by `Nat.find` with classical decidability, and
  `norm_extensionValue_le_minimalLevel` records its defining property.
- `extensionLevel K L P Q f k` is the supremum of `extensionMinimalLevel` over
  `0, …, k`. `extensionMinimalLevel_le_level` and `extensionLevel_mono` show that
  it bounds the minimal level and is monotone in `k`. `norm_extensionValue_le`
  bounds the generator values in the `k`-th chart of `Q` by
  `radius K (extensionLevel K L P Q f k)`.
- `extensionValue_hasBoundedMonomials`: for the constant polyradius of `K` at
  this level, the weighted monomials of the generator values have norm at most
  one. The proof uses `GeneralizedTateAlgebra.monomialValue_norm_le_weight`.

## The chart algebras of `Q` over `K`

- `extensionNormedAlgebra K L Q k : NormedAlgebra K (algebra L Q k)` is
  Mathlib's `NormedAlgebra.restrictScalars K L` on the `k`-th chart algebra of
  `Q`. It is an `abbrev`, and it is made an instance only locally in this file.
  Through it the chart algebras of `Q` become normed `K`-algebras, so bounded
  `K`-algebra maps into them can be formed.
- `extensionRestriction K L Q h`, for `k ≤ k'`, is the published radius
  restriction `restriction L Q h` from chart `k'` to chart `k`, viewed as a
  bounded `K`-algebra map. `extensionRestriction_apply` is the `rfl` lemma
  identifying the two.
- `extensionRestriction_extensionValue`: the restriction sends generator values
  at `k'` to generator values at `k`. This uses
  `PolynomialLocus.restriction_algebraMap`.

## The bounded chart maps over `K`

- `extensionTateMap K L P Q f k` is the published bounded evaluation
  homomorphism `GeneralizedTateAlgebra.evaluateHom` over `K`. It goes from the
  generalized Tate algebra of `K` at the constant polyradius
  `polyradius K P.arity (extensionLevel K L P Q f k)` to `algebra L Q k`, and
  evaluates at the generator values. `extensionTateMap_X` evaluates the
  variables.
- `extensionTateMap_polynomialMap`: on a polynomial `p` over `K`, the Tate map
  gives the coordinate-algebra image of `f (P.map p)`. The proof is induction on
  `p`. On constants it uses `IsScalarTower K L B`: the image of `c : K` in `B`
  is the image of `algebraMap K L c`.
- `extensionChartMap K L P Q f k : BoundedAlgHom K (algebra K P
  (extensionLevel K L P Q f k)) (algebra L Q k)` descends the Tate map through
  `PresentedAffinoidAlgebra.descendRelations` to the actual chart algebra of
  `P`. A polynomial in the kernel of `P.map` is sent to the image of
  `f 0 = 0`, so the relations are respected.
- `extensionChartMap_presentationMap` (definitional) computes the chart map on
  the quotient map, and `extensionChartMap_coordinate` computes it on
  coordinates. `extensionChartMap_algebraMap` shows that it sends the
  coordinate-algebra image of `a : A` to the coordinate-algebra image of `f a`.
- `extensionRestriction_comp_chartMap`, for `k ≤ k'`: restricting from chart
  `k'` to chart `k` of `Q` after the chart map at `k'` equals the chart map at
  `k` after the published restriction of `P` from level
  `extensionLevel K L P Q f k'` to level `extensionLevel K L P Q f k`. By the
  published `PresentedAffinoidAlgebra.hom_ext_coordinate` it suffices to compare
  the two maps on coordinates.

## The continuous map of analytic spaces

- `extensionSigmaMap K L P Q f` sends a pair `⟨k, x⟩`, where `x` is a point of
  the Berkovich spectrum of `algebra L Q k`, to the point
  `chart K P (extensionLevel K L P Q f k)` of the pulled-back seminorm
  `BanachSpectrum.comap (extensionChartMap K L P Q f k) x`.
- `comap_extensionChartMap_pull` and `extensionSigmaMap_pull` show that this is
  compatible with the `pull` maps of the published chart system of `Q`. The
  proofs use `extensionRestriction_comp_chartMap` and the published
  `chart_pull`.
- `extensionFun K L P Q f : Space L Q → Space K P` is the quotient lift of
  `extensionSigmaMap`. `continuous_extensionFun` proves continuity: each
  component is the continuous `BanachSpectrum.comapContinuous` of a chart map
  followed by the continuous chart of `P`, and `Continuous.quotient_lift`
  applies.
- `extensionMap K L P Q f : C(Space L Q, Space K P)` is this continuous map.
  `extensionMap_chart` is its `rfl` computation on chart points.
- `pointSeminorm_extensionMap`: for every point `y` and every `a : A`,
  `pointSeminorm K P (extensionMap K L P Q f y) a = pointSeminorm L Q y (f a)`.
  Here `pointSeminorm` is the published multiplicative seminorm of a point. The
  proof reduces to a chart point and uses `extensionChartMap_algebraMap`.

## Base change of the ground field

- `baseChangePresentation K L P : FinitePolynomialPresentation L (L ⊗[K] A)` has
  arity `P.arity`. Its map is Mathlib's
  `(MvPolynomial.algebraTensorAlgEquiv K L).symm`, from polynomials over `L`
  to `L ⊗[K]` polynomials over `K`, followed by
  `Algebra.TensorProduct.map (AlgHom.id L L) P.map`. It is surjective by
  `Algebra.TensorProduct.map_surjective`.
- `baseChangePresentation_map_X`: the `t`-th variable is sent to
  `1 ⊗ P.map (X t)`. So the base change is presented by the generators `1 ⊗ xₜ`.
- `baseChangeMap K L P : C(Space L (baseChangePresentation K L P), Space K P)`
  is `extensionMap` for the inclusion
  `Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A`, `a ↦ 1 ⊗ a`. This is
  the canonical map `(X_L)^an → X^an` for `X = Spec A` in this model.
- `pointSeminorm_baseChangeMap`: the seminorm of `baseChangeMap K L P y` at `a`
  is the seminorm of `y` at `1 ⊗ a`.

## Scope

The unit imports the published `AffineAnalytificationSeminorm` and
`AffineAnalytificationMap` unchanged and edits no published input. It gives
definitions and their computation lemmas only. It does not state that
`baseChangeMap` is surjective, proper or a quotient map, and it does not
identify `(X_L)^an` with a completed ground-field extension `X^an ⊗̂ L`. It does
not compare `extensionMap` for `L = K` with the published `baseMap`. It does
not prove identity or composition laws, independence of presentations, or
compatibility with rational points. It has no scheme-level version and does not
construct maps of atlases or structure sheaves. Conrad's identification of
`X(k) → X(k')` with `X^an(k) → (X^an)_{k'}(k')` and its closedness are
successor obligations of the parent task.
