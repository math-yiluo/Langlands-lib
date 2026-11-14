# Positivity of the Plancherel weight on a dense open set

Worker 5. The module
`Langlands.Representation.Plancherel.PlancherelWeightPositivity` proves that
the Plancherel weight `μ` is a positive real number on a dense open set. This
holds on the unitary unramified characters `Im X(Z_G(ζ ∘ i))` and on the
orbit `O` of a square-integrable representation of a standard Levi
`M_I(F)`. The module also defines a real-valued form of the weight on `O`.
Everything stated is proved. The inputs `j_P ≠ 0`, regularity of `j_P⁻¹` on
the unitary characters and nonnegativity of its unitary values are
hypotheses (see "Not proved here").

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082, registered as `waldspurger-2003-plancherel`, PDF
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

- V.2, printed p.292 / PDF p.58: for `ω ∈ O`,
  `μ(ω) = j(ω)⁻¹ ∏_α γ(M_α|M)²`, with `α` running over the reduced roots of
  `A_M` up to sign.
- Lemma V.2.1, same page, first item: `μ` is a regular rational function on
  `O` and `μ(ω) ≥ 0` for every `ω ∈ O`.
- VII.2, printed p.319 / PDF p.85: for `ψ, ψ' ∈ C^∞(Θ)_inv`, the sum over
  `(O, P)` of `c(G|M)⁻² γ(G|M)⁻¹ |W_M| |W_G|⁻¹ |P(M)|⁻¹ ∫_O μ(ω)
  (ψ'[O,P]_ω, ψ[O,P]_ω) dω`. Waldspurger says that this "définit un produit
  hermitien défini positif".

## Provenance

The results are internal derived content. Waldspurger states only `μ ≥ 0`,
not the positivity on a dense set proved here. At VII.2 he asserts that the
product is positive definite. For that `μ ≥ 0` alone does not suffice, but
density of `{μ > 0}` added to it does. Suppose
the measure on `O` charges every nonempty open set, `μ ≥ 0` is continuous
and `∫_O μ |q|² = 0` for a continuous `q`. Then `q` vanishes on the open set
`{μ > 0}`, and when that set is dense, `q = 0`.

`μ` need not be positive at every point of `O`. It can vanish at a unitary
point where `j_P` has a pole. The Library's orthogonality step
`rationalUnitaryOrbitWeightedProductCore` (module
`RationalInducedOrbitWavePacketOrthogonality`) assumes `0 < u ω` for every
`ω`, so the Plancherel weight does not meet its hypothesis as stated. This
module supplies the substitute hypothesis: `u ≥ 0` continuous and bounded,
with `{u > 0}` dense and open.

The density `μ` is the Library's `plancherelDensity`, the canonical scalar
`j_P` is `conditionalCanonicalRationalScalar`, and the finite product
`∏_α γ(M_α|M)` is `rankOneGammaProduct`. The Plancherel weight
`plancherelWeight` is the value function of `μ` on the unitary characters,
defined under the hypothesis `hreg` that `j_P⁻¹` is regular at every unitary
character (module `RationalUnitaryRegularValue`). The orbit weight
`standardLeviPlancherelWeight` is its transport to `O` (module
`StandardLeviPlancherelWeight`).

## Positive reals

`exists_pos_real_of_nonneg_of_ne_zero` and `exists_pos_real_iff_ne_zero`: a
complex number that is a nonnegative real is a positive real exactly when it
is nonzero. The Library writes "nonnegative real" as
`∃ r : ℝ, 0 ≤ r ∧ w = r`, and the positive versions here use the same form.

## Nonvanishing on a dense open set

Section `Generic`. `G` is a connected reductive group scheme over the
nonarchimedean local field `F`, with `G.X.left` affine and `G.X.hom` locally
of finite type. `f` lies in the field `rationalUnramifiedFunctionField` of
rational functions on `X(G)`. The hypothesis
`RationalFunctionUnitaryRegular G hG f` says that `f` is regular at every
unitary character, and `rationalUnitaryValue G hG f hf` is its value
function on `Im X(G)`.

- `isOpen_rationalUnitaryValue_ne_zero`: `{z | f(z) ≠ 0}` is open. The value
  function is continuous (`continuous_rationalUnitaryValue`).
- `dense_rationalUnitaryValue_ne_zero`: if `f ≠ 0`, then `{z | f(z) ≠ 0}` is
  dense in `Im X(G)`.

  *Proof.* Suppose `f` vanishes on a nonempty open set `U`, and pick
  `z₀ ∈ U`. Regularity at `z₀` gives `f = m / n` with `m, n` regular
  functions and `n(z₀) ≠ 0`. Move to the canonical circle coordinates
  `Φ : Im X(G) ≃ Circleʳ`, in which regular functions are Laurent
  polynomials (`regular_val_unitaryToUnramified_coordinates_symm`). The set
  of `c` near `Φ z₀` where the Laurent polynomial of `n` is nonzero and
  `Φ⁻¹ c ∈ U` is a neighbourhood. It contains a box `∏ tᵢ` of neighbourhoods
  in the circle, and these are infinite (`circle_infinite_of_mem_nhds`). On
  the box `m / n = 0` with `n ≠ 0`, so the Laurent polynomial of `m` vanishes
  there. A Laurent polynomial vanishing on a product of infinite sets is zero
  (`finiteLaurent_eq_zero_of_eval_on_box`). Hence `m = 0` and `f = 0`.
- `rationalUnitaryValue_pos_iff`: where `f` has a nonnegative real value
  (`RationalFunctionNonnegAt`), the value is a positive real exactly when it
  is nonzero.
- `dense_rationalUnitaryValue_pos`, `isOpen_rationalUnitaryValue_pos`: if
  `f` has a nonnegative real value at every unitary character, then the set
  where the value is a positive real is open, and it is dense if `f ≠ 0`.

## The Plancherel weight on the unitary characters

Section `Weight`. The data are those of `plancherelWeight`: a torus
`i : T → G` with a cocharacter `ζ` (`χ = ζ ∘ i`, `M = Z_G(χ)`), the premises
`hRefl` and `hCST`, `hG : IsConnectedReductive G`, the compact open subgroup
`K` with the Iwasawa decompositions `hPK` and `hOppK`, a smooth
representation `A` of `M(F)` and the conditional data of `j_P`.

- `plancherelDensity_ne_zero`: if `j_P ≠ 0` and
  `rankOneGammaProduct i ζ K hK ≠ ⊤`, then `μ ≠ 0`. This is
  `plancherelDensity_eq_zero_iff`.
- `isOpen_plancherelWeight_ne_zero`, `dense_plancherelWeight_ne_zero`: the
  set where the Plancherel weight is nonzero is open. It is dense if
  moreover `j_P ≠ 0` and the product is finite.
- `plancherelWeight_pos_iff`: where `j_P⁻¹` has a nonnegative real value,
  the weight is a positive real exactly when it is nonzero (from
  `plancherelWeight_nonneg`).
- `dense_plancherelWeight_pos`, `isOpen_plancherelWeight_pos`: suppose
  `j_P⁻¹` has a nonnegative real value at every unitary character. Then the
  set where the weight is a positive real is open. It is dense if moreover
  `j_P ≠ 0` and the product is finite.

The torus here is arbitrary, so finiteness of the product is a hypothesis.

## Characters of the standard Levi

Section `Orbit`. `i : S → G` is a maximal split torus, `ν` a generic
cocharacter, `I` a set of simple roots and `ζ` a standard cocharacter of
`I`. `standardLeviParameterIso : Z_G(ζ ∘ i) ≅ M_I` is the isomorphism over
`G` from `StandardLeviPlancherelWeight`, and `standardLeviCharacterRestrict`
is the restriction `z ↦ z ∘ e`.

- `rationalUnitaryUnramifiedCharacterRestrict_inv_hom`,
  `rationalUnitaryUnramifiedCharacterRestrict_hom_inv`: restriction along the
  isomorphism and along its inverse are mutually inverse on unitary
  unramified characters.
- `standardLeviCharacterRestrictHomeomorph : Im X(M_I) ≃ₜ Im X(Z_G(ζ ∘ i))`.
  Its forward map is `standardLeviCharacterRestrict`
  (`standardLeviCharacterRestrictHomeomorph_apply`). Its inverse is
  restriction along the inverse isomorphism, followed by the Library's
  transport `unitaryUnramifiedCharactersHomeomorph` along
  `leviRationalPointHomeomorph`. The transport identifies the characters of
  the scheme `M_I` with those of the subgroup `M_I(F)` of `G(F)`. Only the
  open-map property of this homeomorphism is used below.

## Positivity on the orbit

`π` is an irreducible admissible representation of the subgroup `M_I(F)` of
`G(F)`, square-integrable modulo a central subgroup `C` (hypothesis `hsq`).
`O` is its orbit `discreteSeriesOrbit` under `Im X(M_I)`. `j_P` and the
weight `standardLeviPlancherelWeight` are those of the inducing
representation `π ∘ e` of `Z_G(ζ ∘ i)(F)`.

- `rankOneGammaProduct_ne_top_of_isMaximalSplitTorus`: the product
  `∏_α γ(M_α|M)` is finite. The maximal split torus `i` is a split torus
  (`hi.1.1`), and `G` is smooth and connected (`hG.smooth`,
  `hG.connectedSpace`), so the Library's
  `rankOneGammaProduct_ne_top_of_isSplitTorus` applies. The orbit results
  therefore need no finiteness hypothesis.
- `isOpen_standardLeviPlancherelWeight_ne_zero`: the set of points of `O`
  where the weight is nonzero is open.
- `dense_standardLeviPlancherelWeight_ne_zero`: if `j_P ≠ 0`, it is dense in
  `O`. *Proof.* The orbit map `Im X(M_I) → O` is an open quotient map
  (`isOpenQuotientMap_discreteSeriesOrbitMap`), so a subset of `O` is dense
  iff its preimage is (`IsOpenQuotientMap.dense_preimage_iff`). The value of
  the weight at `π ⊗ z` is the Plancherel weight at `z ∘ e`
  (`standardLeviPlancherelWeight_orbitMap`). So the preimage contains the
  preimage of the dense set of `dense_plancherelWeight_ne_zero` under the
  open map `standardLeviCharacterRestrictHomeomorph`, and that preimage is
  dense.
- `dense_standardLeviPlancherelWeight_pos`: if `j_P ≠ 0` and `j_P⁻¹` has a
  nonnegative real value at every unitary character, the weight is a
  positive real on a dense subset of `O`. This uses
  `standardLeviPlancherelWeight_nonneg_of_forall`.

## The real Plancherel weight

`standardLeviPlancherelWeightReal hreg : O → ℝ` is the real part of
`standardLeviPlancherelWeight hreg`. A weight `u : O → ℝ` of this form is what
the Library's weighted products on `C^∞(O, P)` take.

- `continuous_standardLeviPlancherelWeightReal`: it is continuous.
- `exists_standardLeviPlancherelWeightReal_le`: it is bounded above. The
  orbit `O` is compact (`compactSpace_discreteSeriesOrbit`, with
  `Im X(M_I)` compact through `leviRationalUnitaryCoordinates`).
- `isOpen_standardLeviPlancherelWeightReal_pos`: its positive set is open.
- Suppose `j_P⁻¹` has a nonnegative real value at every unitary character.
  Then `ofReal_standardLeviPlancherelWeightReal` shows that the real weight,
  viewed in `ℂ`, is the complex weight, so taking the real part loses
  nothing. `standardLeviPlancherelWeightReal_nonneg` shows that it is
  nonnegative.
- `dense_standardLeviPlancherelWeightReal_pos`: if moreover `j_P ≠ 0`, its
  positive set is dense in `O`.

## Intended use

Together these give a weight `u = standardLeviPlancherelWeightReal hreg`
on `O` that is continuous, bounded, nonnegative, and positive on a dense
open set. With a weighted product that requires only `u ≥ 0` and
`{u > 0}` dense, rather than `0 < u` everywhere, this is the positive
definite product of VII.2 for the Plancherel weight. That generalization of
`rationalUnitaryOrbitWeightedProductCore` is not made here.

## Not proved here

- `j_P ≠ 0`.
- Regularity of `j_P⁻¹` at the unitary characters (`hreg`). Its Library
  target is `ConditionalDynamicOppositeUnitaryInverseRegularStatement`
  (module `DynamicOppositeUnitaryInverseRegularity`), from IV.3 (5)–(6).
- Nonnegativity of the unitary values of `j_P⁻¹` (`hnn`). This and
  `j_P ≠ 0` are the conclusion of the target
  `ConditionalDynamicOppositeUnitaryInverseNonnegStatement` in the same
  module, which the Library reduces to the Hermitian adjunction and the
  regularity target
  (`conditionalDynamicOppositeUnitaryInverseNonneg_of_regular`).
- In section `Weight`, finiteness of `∏_α γ(M_α|M)` for an arbitrary torus.
- The generalization of the orthogonality step to weights that are positive
  only on a dense set.

## Axioms

The results use only `propext`, `Classical.choice` and `Quot.sound`.
