# Measurable uniformizer-coset partition of the diagonal torus

`Langlands.RankinSelberg.IwasawaTorusPartitionStatement.{uF}` is a closed
Prop-valued definition in the module
`Langlands.Representation.RankinSelberg.IwasawaTorusPartitionStatement`.
It states that the ordinary diagonal torus is the disjoint union of the
uniformizer cosets of its integral units, and that each coset carries
normalized product Haar mass one. This module supplies the statement only,
with no proof.

## Quantifiers and structures

The proposition quantifies every prime `p` with `Fact p.Prime`, every
`F : PadicField.{uF} p` in an arbitrary universe `uF`, every supplied
`T : F.TopologicalData`, and every natural `m`, including `m = 0`. It installs
`T.topology`, `T.valuativeRel` and `T.localField`, then the Borel measurable
structure `borel F.Carrierˣ` on the field units with its `BorelSpace`
certificate, exactly as in the published `IwasawaTorusSumStatement`. The torus
`A = Fin m → F.Carrierˣ` carries the ordinary function-space measurable
structure `MeasurableSpace.pi` and the pointwise group law. No Borel structure
is installed on `A` itself.

Every `ϖ : F.Carrierˣ` satisfying
`GeneralLinear.Iwasawa.IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ`
is quantified. This predicate says that the valuation of `ϖ` is below one and
that every nonzero field element has the valuation of some integer power of
`ϖ`.

## Local bindings

The following are `let` bindings inside the proposition. Downstream proofs
can introduce them after the quantified variables and the uniformizer
hypothesis.

- `A = Fin m → F.Carrierˣ`.
- `O = (ValuativeRel.valuation F.Carrier).integer`, the actual valuation
  integers.
- `da = Measure.pi (fun _ : Fin m => localMultiplicativeHaar F.Carrier)`, the
  product of the published multiplicative Haar measures normalized so that
  `integralUnits O` has mass one.
- `U = {u : A | ∀ i, u i ∈ integralUnits O}`, the vectors of actual integral
  units, using the published subgroup `integralUnits`.
- `t(lam)(i) = ϖ ^ lam i` for every `lam : Fin m → ℤ`, with integer powers in
  the unit group. This is the same `t` as in `IwasawaTorusSumStatement`, and
  `Iwasawa.torus ϖ lam` is definitionally `Iwasawa.diagonalUnits (t lam)`.
- `C(lam) = (fun u : A => t lam * u) '' U`, the image of `U` under left
  multiplication by `t(lam)`.

## Conclusion

The proposition is the conjunction of:

1. `MeasurableSet U`.
2. `da U = 1`.
3. For every `lam : Fin m → ℤ`: `MeasurableSet (C lam)`,
   `da (C lam) = 1`, and
   `Measure.map (fun u : A => t lam * u) (da.restrict U) = da.restrict (C lam)`.
4. `Pairwise (fun lam lam' => Disjoint (C lam) (C lam'))`.
5. `(⋃ lam, C lam) = Set.univ`.

Every exponent vector is included, with no ordering or dominance restriction.
The scalar is exactly one. The measure equality in item 3 is an equality of
measures with extended nonnegative values. It identifies the translated
restricted measure with the restriction of the same product measure, rather
than with an assumed coset measure. Together, items 4 and 5 say that the
cosets partition the torus.

For `m = 0` the torus is a singleton and the product measure is the unit
Dirac measure. Then `U = C(lam) = Set.univ` for the unique exponent vector,
and every conjunct holds with mass one.

The proposition assumes no partition, Haar decomposition, convergence
hypothesis, quotient compatibility, quotient measure or Iwasawa measure
formula. It does not mention the Iwasawa quotient at all.

## Provenance

This is an internal derived interface about existing Library constructions,
rather than a transcription of an external theorem. It isolates the torus
stratification step named in the future-proof discussion of
`Langlands.RankinSelberg.IwasawaTorusSumStatement`. That discussion
decomposes each diagonal vector uniquely as `t(lam) * u` with `u ∈ U`, and
assigns each coset product Haar mass one. The weighted quotient pushforward
itself remains the separate statement `IwasawaTorusSumStatement`.

The constructions come from two published modules:

- `RankinSelberg.Measures` supplies `integralUnits`, its membership
  characterization `mem_integralUnits` (an element and its inverse are
  integral), its openness `integralUnits_isOpen`, the measure
  `localMultiplicativeHaar` with its Haar instance, and the normalization
  `localMultiplicativeHaar_integerUnits`.
- `Whittaker.Iwasawa` (namespace `GeneralLinear.Iwasawa`) supplies
  `IsUniformizingElement`, the torus maps `diagonalUnits` and `torus`, and
  `valuation_pos`.

## Proof obligations for a future proof

The following describes what a separate proof must establish. It is not
proved here.

- Measurability: `integralUnits O` is open, hence Borel measurable in the
  units, so the finite product `U` is measurable for the product structure.
  Left multiplication by `t(lam)` is a measurable equivalence of `A`, so each
  `C(lam)` is measurable.
- Normalization: `da U = ∏ i, localMultiplicativeHaar (integralUnits O) = 1`
  by the product formula for `Measure.pi` and
  `localMultiplicativeHaar_integerUnits`. The product formula needs
  σ-finiteness of `localMultiplicativeHaar F.Carrier`. With this module's imports it
  is not found by instance inference after the bindings above, so a proof
  must derive it, for example from σ-compactness of the units of the local
  field.
- Haar invariance: the product of left-invariant measures is left invariant.
  Hence `da (C lam) = da U = 1`, and mapping `da.restrict U` by the
  measurable equivalence `u ↦ t(lam) * u` gives `da.restrict (C lam)`.
- Coordinatewise valuation uniqueness: integral units have valuation one.
  If `t(lam) * u = t(lam') * u'` with `u, u' ∈ U`, then
  `v(ϖ) ^ lam i = v(ϖ) ^ lam' i` for every `i`. Since
  `0 < v(ϖ) < 1`, integer powers of `v(ϖ)` are strictly antitone, so
  `lam = lam'`. This gives pairwise disjointness.
- Coordinatewise valuation existence: for `a : A` and each `i`, the
  uniformizer predicate gives `k i` with `v(a i) = v(ϖ) ^ k i`. Then
  `u i = ϖ ^ (-k i) * a i` has valuation one, so it and its inverse are
  integral. By `mem_integralUnits`, `u ∈ U` and `a = t(k) * u`. This gives
  the covering.
