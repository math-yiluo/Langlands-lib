# Proof of the measurable uniformizer-coset partition of the diagonal torus

`Langlands.RankinSelberg.iwasawaTorusPartition :
IwasawaTorusPartitionStatement.{uF}` proves the published closed proposition
`Langlands.RankinSelberg.IwasawaTorusPartitionStatement` from the module
`Langlands.Representation.RankinSelberg.IwasawaTorusPartitionStatement`. The
universe `uF` is arbitrary. The proof keeps every quantified prime `p`, field
`F : PadicField.{uF} p`, supplied realization `T : F.TopologicalData`, natural
rank `m` (including `m = 0`), uniformizing element `ϖ` and exponent vector.
It uses the statement's own measure: the product
`Measure.pi (fun _ : Fin m => localMultiplicativeHaar F.Carrier)` for the
ordinary function-space measurable structure on `Fin m → F.Carrierˣ`. The
measurable structure on the units is `borel F.Carrierˣ`.

The module imports only the target statement module. It uses no partition,
Haar decomposition, convergence, quotient-compatibility, quotient-measure or
Iwasawa-formula hypothesis. It uses no result about the Iwasawa quotient.

## Valuation lemmas

These lemmas hold for any field `E` and any valuation
`v : Valuation E Γ₀` with values in a linearly ordered commutative group with
zero.

- `valuation_eq_one_of_mem_integralUnits`: if `a ∈ integralUnits v.integer`,
  then `v a = 1`. By the published `mem_integralUnits`, both `a` and `a⁻¹`
  lie in `v.integer`. So `v a ≤ 1` and `(v a)⁻¹ ≤ 1`. Since `v a > 0` by the
  published `Iwasawa.valuation_pos`, the second inequality gives `1 ≤ v a`.
- `mem_integralUnits_of_valuation_eq_one`: conversely, if `v a = 1`, then
  `v a⁻¹ = 1` too. Both are integral, so `mem_integralUnits` gives
  `a ∈ integralUnits v.integer`.
- `zpow_eq_of_mul_integralUnits` (uniqueness): let `ϖ` satisfy
  `Iwasawa.IsUniformizingElement v ϖ`, let `u` and `u'` be integral units,
  and suppose `ϖ ^ k * u = ϖ ^ k' * u'`. Apply `v`. The valuations of `u`
  and `u'` are one, so `v ϖ ^ k = v ϖ ^ k'`. Since `0 < v ϖ < 1`, integer
  powers of `v ϖ` are strictly antitone (`zpow_right_strictAnti₀`), hence
  injective, so `k = k'`.
- `exists_zpow_mul_integralUnits` (existence): for every unit `a`, the second
  clause of `IsUniformizingElement` gives `k : ℤ` with `v a = v ϖ ^ k`. Then
  `u = (ϖ ^ k)⁻¹ * a` has valuation `(v ϖ ^ k)⁻¹ * v ϖ ^ k = 1`. So `u` is an
  integral unit by the previous converse lemma, and `a = ϖ ^ k * u`.

## Group-theoretic lemmas

Let `G` be a group with a measurable structure for which multiplication is
measurable (`MeasurableMul G`). Let `μ` be a left-invariant measure on `G`.

- `sigmaFinite_of_zpow_cover`: suppose `μ K ≠ ⊤`, and every element of `G`
  is `ϖ ^ k * u` with `k : ℤ` and `u ∈ K`. Then `μ` is σ-finite. The sets
  `(fun x => (ϖ ^ k)⁻¹ * x) ⁻¹' K` for `k : ℤ` form a countable family.
  By left invariance (`measure_preimage_mul`), each has measure `μ K < ⊤`.
  The hypothesis says that they cover `G`. Mathlib's
  `Measure.sigmaFinite_of_countable` concludes.
- `zpow_coset_partition`: assume in addition that `μ` is σ-finite, that `K`
  is measurable with `μ K = 1`, that every element is `ϖ ^ k * u` with
  `u ∈ K`, and that such an exponent is unique. Then, for every natural `m`,
  the five conclusion groups of the target hold for `A = Fin m → G` and
  `da = Measure.pi (fun _ => μ)`, with
  `U = {u | ∀ i, u i ∈ K}`, `t lam i = ϖ ^ lam i` and
  `C lam = (fun u => t lam * u) '' U`. The statement is written with the same
  `let` bindings as the target. The proof runs as follows.
  1. `U` equals the box `Set.univ.pi (fun _ => K)`, so it is measurable by
     `MeasurableSet.univ_pi`.
  2. `Measure.pi_pi` gives `da U = ∏ i, μ K = 1`. This is where σ-finiteness
     of `μ` is used.
  3. `C lam` equals the preimage of `U` under `a ↦ (t lam)⁻¹ * a`
     (`Set.image_mul_left`). It is therefore measurable by
     `measurable_const_mul`. Mathlib's `Measure.pi.isMulLeftInvariant` makes
     `da` left invariant, so `measure_preimage_mul` gives
     `da (C lam) = da U = 1`. For the translation identity, `restrict_map`
     for the measurable map `u ↦ t lam * u` and the measurable set `C lam`
     gives
     `(da.map (t lam * ·)).restrict (C lam) =
     (da.restrict ((t lam * ·) ⁻¹' C lam)).map (t lam * ·)`.
     Left invariance (`map_mul_left_eq_self`) turns the left side into
     `da.restrict (C lam)`. Injectivity of left multiplication turns the
     preimage into `U`. The result is exactly
     `Measure.map (t lam * ·) (da.restrict U) = da.restrict (C lam)`.
  4. Disjointness: suppose `t lam * u = t lam' * u'` with `u, u' ∈ U`.
     Evaluating at a coordinate `i` gives
     `ϖ ^ lam i * u i = ϖ ^ lam' i * u' i`. The uniqueness hypothesis gives
     `lam i = lam' i`. So `lam = lam'` by function extensionality,
     contradicting `lam ≠ lam'`.
  5. Covering: for `a : A`, choose for each coordinate `i` an exponent `k i`
     and `u i ∈ K` with `a i = ϖ ^ k i * u i`. Then `u ∈ U` and
     `a = t k * u`, so `a ∈ C k`.

## The main theorem

`iwasawaTorusPartition` introduces `p`, `F`, `T` and `m`. It installs
`T.topology`, `T.valuativeRel`, `T.localField`, the measurable structure
`borel F.Carrierˣ` and its `BorelSpace` certificate, which are the target's
own instances. It then introduces `ϖ` and the uniformizer hypothesis.

- `integralUnits (ValuativeRel.valuation F.Carrier).integer` is open, by the
  published `integralUnits_isOpen` together with `Valuation.isOpen_integer`.
  So it is Borel measurable.
- Normalization: the published `localMultiplicativeHaar_integerUnits` says
  that `localMultiplicativeHaar F.Carrier` gives these integral units mass
  exactly one. The proof uses this normalization unchanged; no other scalar
  appears.
- σ-finiteness of `localMultiplicativeHaar F.Carrier` is not found by
  instance inference in this context, so the proof derives it.
  `sigmaFinite_of_zpow_cover` applies with `K` the integral units (mass
  one, hence finite) and the cover from `exists_zpow_mul_integralUnits`. Left
  invariance is the published `IsHaarMeasure` instance. `MeasurableMul` of
  the units is found by instance inference, from continuity of multiplication
  and the Borel structure.
  This derivation needs no topological countability input. The countable
  cover by the integer-power cosets of the integral units suffices.
- Finally, `zpow_coset_partition` is applied with `μ` the normalized
  multiplicative Haar measure, `K` the integral units, the existence lemma
  `exists_zpow_mul_integralUnits` and the uniqueness lemma
  `zpow_eq_of_mul_integralUnits`. Its conclusion agrees with the target's
  body up to unfolding the target's `let` bindings, including
  `O = (ValuativeRel.valuation F.Carrier).integer`.

## Rank zero

The proof treats `m = 0` uniformly, with no case split, and the scalar is
exactly one there as well. Over `Fin 0`, `Measure.pi_pi` evaluates `da U` as
the empty product, which is `1`. The box `U` and every `C lam` are the whole
singleton torus. Disjointness is vacuous, because function extensionality over
the empty index set identifies every pair of exponent vectors. Covering
chooses no coordinates and uses the unique exponent vector.

## Provenance

This is an internal proof of an internal derived interface: the torus
stratification step isolated by `IwasawaTorusPartitionStatement`. It follows
the route recorded in that statement's Markdown, except that σ-finiteness is
derived from the countable integer-power coset cover rather than from
σ-compactness of the units. The arguments are elementary valuation theory and
Mathlib's product-measure and left-invariance results.
