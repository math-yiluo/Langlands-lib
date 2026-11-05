# The actual maximal unramified field as a Henselian normed field

This module connects the published topologies on the maximal unramified extension
`K = UnramifiedClosure F = inertiaFixedField F` and on intermediate fields `L` of
`F^sep/K` with normed-field structures. It lets the published Henselian smooth-openness
statement be applied to the actual field `K`, which is not complete.

Throughout, `F` is a nonarchimedean local field. It carries the published local instances
`localNormedField F`, `localNormedField_ultrametric F` and `localNormedField_complete F`.
`F^sep = SeparableClosure F` carries the published spectral norm `sepClosureNormedField F`,
and its topology is `sepClosureTopology F`.

## Declarations

In namespace `Langlands.LocalGalois.Separable`:

- `comapValuedTopology_eq_induced`: let `ι : E →+* F^sep` be a field embedding such that
  for every `ε > 0` some `x : E` has `0 < ‖ι x‖ < ε`, where `‖·‖` is the spectral norm.
  Then the `Valued.mk'` topology of the restricted valuation
  `(sepClosureValuation F).comap ι` equals the topology induced from `F^sep` along `ι`.
  This generalizes the published `fixedFieldTopology_eq_induced`, and the proof is the same.
  Both topologies are additive-group topologies. Their zero-neighbourhood bases, valuation
  balls and pulled-back metric balls, refine each other. The value-group embedding turns a
  valuation radius into a positive real radius. In the other direction, the hypothesis gives
  an element whose valuation is a nonzero radius smaller than `ε`.
- `fixedFieldNormedField : NontriviallyNormedField (inertiaFixedField F)`: the normed-field
  structure `SubfieldClass.toNormedField` restricted from `sepClosureNormedField F`. It is
  nontrivial because an element of `F` of norm `> 1` keeps its norm in `F^sep`
  (`spectralNorm_extends`).
- `fixedFieldNormedField_norm`: the norm of `x` is the spectral norm of `x` in `F^sep`
  (by `rfl`).
- `fixedFieldNormedField_topology`: the norm topology equals the published
  `fixedFieldTopology F`. Both are the topology induced from `F^sep`, by
  `fixedFieldTopology_eq_induced`.
- `fixedFieldNormedField_isUltrametricDist`: the restricted norm is ultrametric, because
  the spectral norm is nonarchimedean (`isNonarchimedean_spectralNorm`).
- `fixedFieldNormedField_valuation`: Mathlib's `NormedField.valuation` of this norm is the
  published `fixedFieldValuation F` (by `rfl` pointwise).
- `fixedFieldNormedField_henselian`: the valuation ring of `NormedField.valuation` is a
  Henselian local ring. It is the published `fixedFieldIntegers F`, which is Henselian by
  the published `fixedFieldIntegersIsHenselian F`.

In namespace `Langlands.Geometry.Building`:

- `intermediateValuationTopology_eq_induced`: for `L : IntermediateField K F^sep`, the
  `Valued.mk'` topology of the actual `intermediateValuation F L` equals the topology induced
  from `F^sep`. This is `comapValuedTopology_eq_induced` for `algebraMap L F^sep`, where
  small elements come from `F` (`NormedField.exists_norm_lt` and `spectralNorm_extends`).
- `intermediateValuation_continuousSMul`: scalar multiplication `K × L → L` is continuous
  for `fixedFieldTopology F` on `K` and the `Valued.mk' (intermediateValuation F L)` topology
  on `L`. After both topologies are rewritten as induced from `F^sep`, scalar multiplication
  becomes multiplication in `F^sep`, which is continuous.
- `isOpenMap_rationalPoint_of_smooth`: assume the published proposition
  `HenselianSmoothRationalPointOpenMapStatement.{u}` (an explicit hypothesis here; this
  module does not prove it). Let `f : X ⟶ Y` be a smooth morphism of affine schemes over
  `Spec K`. Then `p ↦ p ≫ f` on actual rational points is an open map for
  `rationalPointTopology`, where `K` has the published `fixedFieldTopology F`. The proof
  installs `fixedFieldNormedField`, its ultrametricity and Henselianity as instances. It then
  applies the hypothesis and rewrites the norm topology to `fixedFieldTopology F` with
  `fixedFieldNormedField_topology`.

## Provenance

These are derived internal adapters, with no new mathematical content. Kaletha–Prasad,
*Bruhat–Tits theory: a new approach* (2023), Section 2.5 (book p. 88, PDF p. 119), work
over a discretely valued Henselian field with perfect residue field and its maximal
unramified extension `K`, which is again Henselian but not complete. The proof of
Lemma 2.5.12 (book pp. 89–90, PDF pp. 120–121) deduces openness of the norm image in
`T(K)` from smoothness of the algebraic norm map, so it uses the open-map property of
smooth morphisms on `K`-points. Definitions 2.5.13 and 2.6.23 then define `T(K)^0` and
`H(K)^0` over this `K`. The module records that the
published field, valuation, Henselianity and topologies of `K` and `L` fit the hypotheses of
the published Henselian statement. It does not prove that statement, and it does not prove
openness of any zero subgroup.
