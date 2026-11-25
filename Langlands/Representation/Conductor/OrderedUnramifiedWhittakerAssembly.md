# Assembly of the normalized inverse Whittaker realization

Module `Langlands.Representation.Conductor.OrderedUnramifiedWhittakerAssembly`.

This module combines the glue modules into the conclusion of
`Langlands.Conductor.OrderedUnramifiedWhittakerRealizationStatement` for fixed data
`F, ϖ, n, q, z, ψ`, and then into the whole statement. The intermediate theorems take two
inputs as hypotheses:

* `h411`: Bernstein–Zelevinsky's Theorem 4.11 over all nonarchimedean local fields, as the
  proposition `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNoDegenerateSubmodules`
  for the local-field package `pkg F` and its data `data F`;
* `htop`: the standard coinvariants of the product of the rank-one blocks for the character
  `x ↦ ψ(-x)` are one-dimensional.

The last theorem, `realization_of_h411`, discharges `htop` with
`Langlands.Conductor.OrderedUnramifiedTopLine.finrank_productCoinvariants`
(module `OrderedUnramifiedTopLine`), so only `h411` remains.

The spherical clause is not a hypothesis. It comes from
`Langlands.Conductor.coefficientMap_sphericalSection_apply` in
`Langlands.Representation.Conductor.UnramifiedSphericalWhittaker`.

## Declarations

* `exists_ne_one_of_hasIntegerConductor hϖ hψ`: a unitary additive character with integer
  conductor takes a value different from `1`. Otherwise every `ψ(ϖ⁻¹ y)`, `y ∈ O`, is `1`,
  so the second clause of `HasIntegerConductor` puts `ϖ⁻¹` in `O`, contradicting
  `v(ϖ) < 1`.
* `exists_scale_neg_one_ne_one hϖ hψ`: the same for the character `x ↦ ψ(-x)`, that is
  `ψ.scale (-1)`.
* `productEquiv hϖ n hq z`: the equivalence of `principalSeries hϖ n hq z` with
  `product hϖ n z`, the normalized product of the rank-one blocks `rankOneBlock hϖ (z i)`
  over the singleton block shape. It instantiates `principalSeriesEquiv` with these blocks,
  the identification `lineEquiv` of their tensor product with `ℂ`, and the action formula
  `rankOneBlock_apply`.
* `nontrivial_inverseCoinvariants`: given `h411` and nondecreasing norms `‖z i‖`, every
  nonzero subrepresentation `K` of `I(z)` has nontrivial inverse-character coinvariants
  `InverseCoinvariants n ψ K.toRepresentation`.
* `finrank_inverseCoinvariants`: given `htop`, the inverse-character coinvariants of `I(z)`
  have dimension one.
* `realization_of_product_inputs`: given `h411`, nondecreasing norms, `HasIntegerConductor ψ`
  and `htop`, there is a functional `ℓ` in `glInverseFunctionals ψ n (principalSeries hϖ n hq z)`
  with `ℓ.val ≠ 0`, an injective coefficient map, and coefficient map sending the spherical
  section to `Spherical.sphericalWhittaker hϖ (inverseStandardCharacter ψ n) q z`. This is
  the body of the target statement.
* `realization_of_h411_htop h411 htop`: the full statement
  `OrderedUnramifiedWhittakerRealizationStatement.{uF}`, where `h411` gives
  `OrderedCuspidalProductNoDegenerateSubmodules.{uF, uF} P T` for every local-field package
  `P : LocalFieldPackage.{uF}` and data `T`, and `htop` gives, for every field `F`,
  uniformizer, rank, parameters `z` and unitary additive character `ψ'` of `F`, that the
  standard coinvariants of `product hϖ n z` for `standardCharacter ψ' n` have dimension one.
  It applies `realization_of_product_inputs` with `h411 (pkg F) (data F)` and with `htop`
  at `ψ' = ψ.scale (-1)`.
* `realization_of_h411 h411`: the full statement
  `OrderedUnramifiedWhittakerRealizationStatement.{uF}` from the same `h411` alone. It
  applies `realization_of_h411_htop` with `htop` given by
  `OrderedUnramifiedTopLine.finrank_productCoinvariants hϖ n z ψ'`. That lemma's product
  is `product hϖ n z` by definition: both are the normalized product, over the singleton
  shape, of the blocks `rankOneBlock hϖ (z i)` for the data `LocalFieldData.ofInstances F`.

## Proof

The inverse standard character of `ψ` is the standard character of `ψ.scale (-1)`
(`standardCharacter_scale_neg_one`), so the inverse-character coinvariants are standard
coinvariants for `ψ.scale (-1)`.

* Nondegeneracy: `nontrivial_coinvariants` (module `OrderedUnramifiedNondegeneracy`) turns
  `h411` into nonzero mirabolic standard coinvariants for every nonzero mirabolic
  subrepresentation of the product. `nontrivial_coinvariants_of_equiv` (module
  `OrderedUnramifiedTransport`) moves this along `productEquiv` to nonzero coinvariants
  of nonzero subrepresentations of `I(z)`.
* Dimension: `coinvariantsEquiv (productEquiv …)` identifies the coinvariants of `I(z)` with
  those of the product, and `htop` gives dimension one. In `realization_of_h411`, `htop` is
  `finrank_productCoinvariants` (module `OrderedUnramifiedTopLine`), which computes the top derivative of the
  product of rank-one blocks.
* Conclusion: `realization_of_inputs` (module `OrderedUnramifiedWhittakerReduction`) takes
  the dimension, nondegeneracy and spherical inputs and returns the normalized
  functional.

## Provenance

The route is Jacquet 2012, Lemma 2. Injectivity of the coefficient map comes from
Bernstein–Zelevinsky 1977, Theorem 4.11, through the kernel argument in the reduction
module. Uniqueness comes from the top derivative of the product of characters
(module `OrderedUnramifiedTopLine`). The
spherical comparison (Shintani's uniqueness) is the module `UnramifiedSphericalWhittaker`.
