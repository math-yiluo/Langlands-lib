# Trivial-scalar rational quotients as denominator localizations: proof

Author: Worker 228.

The theorem `Langlands.Analytic.StrictTestDomain.trivialScalarRationalLocalization`
proves `TrivialScalarRationalLocalizationStatement.{u}`, the target stated and
explained in
[`TrivialScalarRationalLocalizationStatement.md`](TrivialScalarRationalLocalizationStatement.md).
Its type is exactly that unapplied proposition. Let `K : Type u` be a complete
ultrametric normed field with `‖c‖ ≤ 1` for every `c : K`. Let `P` be a
presented strict affinoid algebra and `d : RationalData K P`. The actual
rational quotient `d.algebra` is a localization of `P` away from
`d.denominator`. Here `P` acts on `d.algebra` through the local instance
`d.baseMap.toAlgHom.toRingHom.toAlgebra`.

The helper declarations are in the namespace
`Langlands.Analytic.StrictTestDomain.TrivialScalar`.

## Tate algebras under the scalar bound

This part works for an arbitrary index type `σ` in any universe `v`. Only
`norm_eq_one`, `coeff_support_finite`, `one_le_norm`, `isClosed_set`,
`polynomialHom_surjective` and `polynomialEquiv` assume the scalar bound
`hK : ∀ c : K, ‖c‖ ≤ 1`.

1. `norm_eq_one`: every nonzero scalar has norm one. The bound applied to
   `c⁻¹` gives `‖c‖⁻¹ ≤ 1`, so `1 ≤ ‖c‖`.
2. `coeff_support_finite`: an element of `StrictTateAlgebra σ K` is a
   unit-radius restricted series. Its coefficient norms therefore tend to zero
   along the cofinite filter. Eventually they are below `1`. Every nonzero
   coefficient has norm one, so only finitely many coefficients are nonzero.
3. `one_le_norm`: a nonzero series has a nonzero coefficient. That coefficient
   has norm one and is bounded by the Gauss norm (`norm_coeff_le`).
4. `isClosed_set`: by step 3, distinct series have distance at least one. A
   point of the closure of a set `S` lies within distance `1` of some member
   of `S`, so it equals that member. Hence every subset is closed.
5. `polynomialHom` is the K-algebra map `MvPolynomial σ K → StrictTateAlgebra
   σ K` given by `MvPolynomial.aeval` at the coordinates `X σ K`.
   `series_polynomialHom` shows that the underlying power series of
   `polynomialHom p` is the coercion of `p`; this is checked on generators.
   `polynomialHom_X` is the value on a variable. `polynomialHom_injective`
   follows from injectivity of the coercion and needs no bound.
   `polynomialHom_surjective` uses the bound. By step 2 the coefficient
   function of a series is finitely supported, and the polynomial with these
   coefficients maps to the series. `polynomialEquiv` packages the bijection as
   an algebra equivalence.

## Comparison with the ordinary localization

Fix `P`, `m : ℕ`, `g : P` and `f : Fin m → P`. Write
`A = RationalLocalization.algebra K P m g f` and `L = Localization.Away g`.
By the published definitions, `A` is the quotient of
`StrictTateAlgebra (Fin (P.arity + m)) K` by the closure of the ideal spanned
by `RationalPresentation.relations`. The relations are of two kinds: the
images under `adjoinVariables` of the elements of `P.ideal`, and, for each `j`,
`adjoinVariables (seriesLift g) * X (natAdd j) - adjoinVariables (seriesLift (f j))`.

6. `values` lists where the coordinates go in `L`. Old coordinate `i` goes to
   the image in `L` of `modelEquiv (coordinate i)`, the class of the `i`-th
   coordinate in `P`. New coordinate `j` goes to
   `f j * IsLocalization.Away.invSelf g`, that is, `f_j / g`.
7. `evalHom : StrictTateAlgebra (Fin (P.arity + m)) K →+* L` first inverts
   `polynomialEquiv` and then evaluates the polynomial by
   `MvPolynomial.eval₂Hom` at `values`. Coefficients map through
   `K → P → L`. The lemmas `evalHom_polynomialHom`, `evalHom_X` and
   `evalHom_algebraMap` record the evaluation of polynomials, coordinates and
   scalars.
8. `evalHom_adjoinVariables`: for an old-variable series `h`,
   `evalHom (adjoinVariables h)` is the image in `L` of
   `modelEquiv (presentationMap (model K P) h)`. The two sides are ring maps
   of `h`. They agree on scalars and on variables (`MvPolynomial.ringHom_ext`
   after precomposing with `polynomialHom`). Every `h` is a polynomial by
   step 5.
9. `evalHom_relation`: `evalHom` sends every relation to zero. For `h` in
   `P.ideal`, `presentationMap_relation` gives `presentationMap (model K P) h = 0`.
   For the `j`-th rational relation, `modelEquiv_presentationMap_seriesLift`
   turns the value into `g * (f_j * g⁻¹) - f_j`. This is zero by
   `IsLocalization.Away.mul_invSelf`.
10. `quotientEval : A →+* L`. Step 4 makes the relation span closed, so its
    closure equals the span (`Ideal.closure_eq_of_isClosed`). The span lies in the
    kernel by step 9, so `evalHom` descends through `Ideal.Quotient.lift`.
    `quotientEval_presentationMap` says that `quotientEval` composed with the
    quotient map is `evalHom`; this holds by definition.
    `quotientEval_baseMap` proves `quotientEval (baseMap a) = algebraMap P L a`.
    By `presentationMap_surjective`, choose `h` with
    `presentationMap (model K P) h = modelEquiv.symm a`. The published
    `RationalPresentation.baseMap` sends this to the class of
    `adjoinVariables h` by definition, and step 8 finishes the proof.
11. `localizationLift : L →+* A` uses the hypothesis
    `RationalLocalization.GeneratesUnitIdeal K P m g f`. With it,
    `RationalLocalization.isUnit_baseMap_denominator` shows that `baseMap g`
    is a unit in `A`. The universal property `IsLocalization.Away.lift` then
    extends the ring map underlying `baseMap`.
    `localizationLift_algebraMap` states this extension property.
12. `quotientEval_comp_localizationLift`: the composite `L → A → L` is the
    identity. By `IsLocalization.ringHom_ext` it suffices to check this on
    `P`, where it follows from steps 10 and 11.
13. `localizationLift_comp_quotientEval`: the composite `A → L → A` is the
    identity. `Ideal.Quotient.ringHom_ext` and surjectivity of
    `polynomialHom` (`RingHom.cancel_right`) reduce this to polynomials, and
    `MvPolynomial.ringHom_ext` reduces it further to scalars and variables.
    - Scalars: both sides are `algebraMap K A c` (`AlgHom.commutes`).
    - Old variable `i`: by step 11 the composite gives
      `baseMap (modelEquiv (coordinate i))`. Unfolding `baseMap`, this is
      `RationalPresentation.baseMap` of `coordinate i` in the model, which is the
      coordinate `castAdd i` of `A` (`RationalPresentation.baseMap_coordinate`).
    - New variable `j`: the target is `fractionCoordinate j`. Put
      `u = localizationLift (invSelf g)`. Then `baseMap g * u = 1`, and
      `RationalLocalization.coordinate_equation` gives
      `baseMap g * fractionCoordinate j = baseMap (f j)`. A linear combination
      of these two equations gives `baseMap (f j) * u = fractionCoordinate j`.
14. `ringEquiv : L ≃+* A` is `RingEquiv.ofRingHom` applied to steps 12
    and 13.
15. `isLocalization_away` uses the local instance
    `Algebra P A := (baseMap K P m g f).toAlgHom.toRingHom.toAlgebra`. Under
    it, `ringEquiv` is a `P`-algebra equivalence by step 11
    (`AlgEquiv.ofRingEquiv`). `IsLocalization.isLocalization_of_algEquiv` then
    transfers the localization property of `Localization.Away g` to `A`.

## Final theorem

The proof introduces `K`, its instances, `P`, the bound `hK` and `d`. It then
applies `isLocalization_away` with `m = d.arity`, `g = d.denominator` and
`f = d.numerator`. The unit-ideal hypothesis is `RationalData.generatesUnitIdeal d`
from the published `RationalRepresentationProof`. That lemma derives it from
`d.no_common_zero` through
`RationalFactorization.generatesUnitIdeal_iff_no_common_zero`. By definition,
`d.algebra` and `d.baseMap` are `RationalLocalization.algebra` and
`RationalLocalization.baseMap` at these data. The algebra instance used is
therefore exactly the one fixed in the statement.

## Scope

The proof uses the actual quotient `d.algebra` and its actual structural map.
It adds no hypothesis to the target. No nonzero-denominator, injectivity,
reducedness or nonempty-spectrum assumption appears. Zero and nonreduced bases,
empty numerator tuples (then `A` has no new variables) and empty rational loci
are all covered. The polynomial comparison and the closedness of relation
ideals are proved in this module from the scalar bound, not assumed.
`CompleteSpace K` is used because the published `adjoinVariables` and
rational quotient are defined under it; the target statement also assumes it.

The route follows the plan in the statement Markdown, with one difference. The
proof does not build `P[Y₁, …, Yₘ] / (gYⱼ - fⱼ)` as a separate object.
Instead, it evaluates the enlarged Tate algebra, which is a polynomial
algebra under the bound, directly in `Localization.Away g`. The localization
property is then transferred along the resulting ring equivalence.

As in the statement, this is an internally derived specialization of the
rational equations `gTᵢ - fᵢ` in Berkovich, *Non-archimedean analytic spaces*,
Trieste lectures (2009), Exercise 2.2.2(ii), printed/PDF page 9 (registered as
`berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`). Achinger's
standing convention (*Introduction to non-Archimedean Geometry*, 2020,
printed/PDF page 6) excludes trivial valuations. The argument here is the
elementary finite-support and localization argument given above.

The development check reports only the axioms `propext`, `Classical.choice`
and `Quot.sound`. This module does not prove the whole-spectrum rational
gluing target `WholeSpectrumRationalGluingStatement` or any analytic descent,
sheaf or gluing statement.
