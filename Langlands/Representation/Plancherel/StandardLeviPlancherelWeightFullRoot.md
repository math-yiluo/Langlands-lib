# The Plancherel weight at the full simple-root index

Waldspurger (2003), V.2, printed p.292 (PDF p.58), defines the Plancherel
density of an orbit `O` of discrete series of a Levi subgroup `M` by
`μ(ω) = j(ω)⁻¹ ∏_α γ(M_α|M)²`. Here `α` runs over the reduced roots of `A_M`
up to sign, and `j = j_P` is the rational scalar of IV.3, printed p.285
(PDF p.51), by which `J_{P|P̄}(ω) J_{P̄|P}(ω)` acts. The Library realizes
this as follows.

- `plancherelWeight` (module `RationalUnitaryRegularValue`) is the value
  function on unitary unramified characters of the Library density. That
  density is the constant `plancherelDensityConstant`
  `= (rankOneGammaProduct)²` times `j_P⁻¹`, where `j_P` is
  `conditionalCanonicalRationalScalar`.
- `standardLeviPlancherelWeight` (module `StandardLeviPlancherelWeight`)
  transports `plancherelWeight` to the orbit of a discrete series `π` of a
  standard Levi `M_I`.

This module evaluates both weights in the case where the Levi is the whole
group. In that case `M = P = G`, the unipotent radicals are trivial, and
`A_M` has no roots. The result is that the weight is the constant `1`. The
Library's actual objects are used throughout: the canonical scalar of the
actual opposite standard integrals at the source Haar scale `K`, and the
actual product of the constants `γ(M_α|M)`. No density or normalization is
assumed to be `1`; both are computed.

Provenance: this is a derived evaluation of the Library's definitions. In
Waldspurger the case `M = G` is implicit: the product over roots is empty
and there are no nontrivial intertwining operators. The module proves this
for the Library's formalization.

## Continued composites acting as the identity

Section `ContinuedIdentity`. Here `L` is a connected reductive group over
the local field `F`, with continuous valuation-image projection. `p` and `q`
are rational continuation data (`RationalOperatorContinuationData`) for
families `A w : V → W` on `Ω` and `B w : W → V` on `Λ` of unramified
characters.

- `continuedComposite_eq_id_of_eqOn`: the hypotheses are
  - an injective linear map `eV : V → X` and a linear map `eW : W → X`;
  - nonempty open sets `D ⊆ Ω` and `E ⊆ Λ`;
  - `eW (A w v) = eV v` for `w ∈ D`, and `eV (B w x) = eW x` for `w ∈ E`.

  Then the continued composite `q ∘ p` is the identity at every common
  regular point. The proof applies the published identity theorem
  `continuedOperator_map_eq_of_eqOn` (module
  `DynamicOppositeUniformNonvanishing`) to `p` and then to `q`, and cancels
  `eV`.
- `continuedCompositeRationalScalar_eq_one_of_eq_id`: if the continued
  composite is the identity at every common regular point, then its
  extracted rational scalar `continuedCompositeRationalScalar` is `1`. This
  holds for every vector `v` and functional `ℓ` with `ℓ v = 1`. The proof
  writes the scalar as `a / b`, with `a(z) = b(z) · 1` on the nonempty
  open common regular region (`continuedCompositeRationalScalar_spec`).
  So `a - b` vanishes there, and
  `rationalUnramifiedRegular_eq_zero_of_isOpen` gives `a = b`.

## Standard integrals over a trivial radical

Sections `TrivialRadical` and `CompactTrivialRadical`. The setting is a
locally compact nonarchimedean Hausdorff group `G`, with a semidirect
decomposition `P = M U`, a second subgroup `U'`, a smooth representation `A`
of `M`, and the published `HasIntegral` relation of standard intertwining
integrals.

- `HasIntegral.eq_eval_of_eq_bot`: the hypotheses are
  - `U' = 1`;
  - Haar measures on `U'` and on `U ∩ U'` that give these trivial groups
    mass `1`;
  - a compatible quotient measure on `(U ∩ U') \ U'`.

  If `Jf g` represents the integral of `u' ↦ f(u' g)` over
  `(U ∩ U') \ U'`, then `Jf g = f(g)`. The integral over the one-point
  quotient is evaluation (`integral_trivialQuotient`,
  `integrable_trivialQuotient_iff`), and weak integrals are unique
  (`SmoothWeakIntegral.HasIntegral.unique`).
- `compactPictureValues h K A` (definition): the linear map sending a
  section in the compact picture `CompactInductionPicture h K A` to its
  values on `K`. `compactPictureValues_injective` says that this map is
  injective.
- `compactIntertwiningOperator_values_of_eq_bot`: let `J` be an
  intertwiner between the unramified inductions from `P = M U` and
  `P' = M U'`. Suppose each value of `J f` represents the standard integral
  over `(U ∩ U') \ U'`, with the hypotheses above on `U'` and the measures.
  Then the compact picture `compactIntertwiningOperator … J` keeps the
  values on `K` of every section. The proof combines
  `HasIntegral.eq_eval_of_eq_bot` with
  `unramifiedLeviInductionCompactEquiv_eval`.
- `subgroupCompactOpenHaar_univ_of_eq_bot`: the Haar measure
  `subgroupCompactOpenHaar Q hQ U hU` of a trivial closed subgroup `U`
  gives `U` mass `1`. Indeed `U ∩ Q = U` has mass `1` by
  `subgroupCompactOpenHaar_mass`.

## The canonical scalar of a central cocharacter

Section `DynamicCentral`, for a cocharacter `χ` of `G` over the local
field `F`, with the notation of `DynamicOppositeStandardIntertwining`
(`levi χ` is the group of rational points of the dynamic centralizer).

- `radical_eq_bot_of_levi_eq_top`, `oppositeRadical_eq_bot_of_levi_eq_top`:
  if `levi χ = ⊤`, the radicals of `P_G(χ)` and of `P_G(χ⁻¹)` are trivial.
  These follow from `unipotent_eq_bot_of_levi_eq_top` for the two
  semidirect decompositions.
- `conditionalForwardCompactFamily_values_of_levi_eq_top`,
  `conditionalReverseCompactFamily_values_of_levi_eq_top`: if
  `levi χ = ⊤`, then at every point of the full domain regions, the
  compact pictures of the actual forward and reverse standard integrals
  (`conditionalForwardCompactFamily`, `conditionalReverseCompactFamily`)
  keep the values on `K`. They are `compactIntertwiningOperator_values_of_eq_bot`
  with the measures of the Library families. Those are
  `subgroupCompactOpenHaar` on the opposite radical, the source
  intersection Haar measure on the trivial intersection
  (`sourceIntersectionHaar_univ`), and the compatible quotient measure.
- `conditionalCanonicalRationalScalar_eq_one_of_levi_eq_top`
  (**`j_P = 1`**): if `levi χ = ⊤`, then the Library's canonical rational
  scalar `conditionalCanonicalRationalScalar χ … K … p q … hirr` equals
  `1`. This holds for every choice of continuations `p`, `q`, of nonempty
  open loci `DForward`, `DReverse`, `D`, and of the irreducibility input
  `hirr`. The proof rewrites the scalar by
  `conditionalCanonicalRationalScalar_eq_extraction`, with a normalized
  compact coefficient from `exists_normalized_compactCoefficient`. The two
  value statements above give, through the injective `compactPictureValues`,
  the hypotheses of `continuedComposite_eq_id_of_eqOn`. Then
  `continuedCompositeRationalScalar_eq_one_of_eq_id` applies.

## No positive roots at the full simple-root index

Section `FullRootSigns`, over any field.

- `latticePairing_eq_zero_of_isStandardCocharacter_simple`: let `ν` be
  generic and the relative roots stable under negation. If `ζ` is a
  standard cocharacter for the full set `simpleRelativeRoots i ν`, then
  every relative root pairs to `0` with `ζ`. Indeed `ζ` and the zero
  cocharacter (`isStandardCocharacter_simple_zero`) are standard for the
  same index, so they have the same relative-root signs
  (`IsStandardCocharacter.haveSameRelativeRootSigns`).
- `positiveRelativeRoots_eq_empty_of_isStandardCocharacter_simple`: under
  the same hypotheses, `positiveRelativeRoots i ζ = ∅`.

## The Plancherel weight of a central cocharacter

Section `FullRootWeight`, with the variables of the `Weight` section of
`RationalUnitaryRegularValue` and `χ = ζ ∘ i`.

- `rankOneGammaProduct_eq_one_of_positiveRelativeRoots_eq_empty`,
  `plancherelDensityConstant_eq_one_of_positiveRelativeRoots_eq_empty`:
  if `positiveRelativeRoots i ζ = ∅`, then the index set
  `rankOneCocharacterSet i ζ` is empty. So `∏_α γ(M_α|M) = 1` and
  `plancherelDensityConstant i ζ K hK = 1`.
- `rationalFunctionUnitaryRegular_inv_of_levi_eq_top`: if
  `levi χ = ⊤`, then `j_P⁻¹ = 1` is regular at every unitary unramified
  character. This is the hypothesis `hreg` of `plancherelWeight`.
- `plancherelWeight_eq_one_of_levi_eq_top`: if `levi χ = ⊤` and
  `positiveRelativeRoots i ζ = ∅`, then for every `hreg` and every
  unitary unramified character `z`, `plancherelWeight … hreg z = 1`. The
  proof uses `plancherelWeight_eq`, the two constants above, and the
  presentation `j_P⁻¹ = 1 / 1` in `rationalUnitaryValue_eq`.

## The weight on the orbit at the full simple-root index

Section `StandardFullRoot`, with the variables of the `Standard` section of
`StandardLeviPlancherelWeight`. These are:
- `hG`, connected reductive `G`;
- `hi`, `i` a maximal split torus;
- `hν`, `ν` generic;
- an index `I`, with `ζ` standard for `rootSet i ν I`;
- a discrete series `π` of `M_I(F)` modulo a central subgroup `C`;
- the Library inputs `hRefl`, `hCST`, `K`, `hPK`, `hOppK`, `p`, `q`, and
  the loci `DForward`, `DReverse`, `D`, with `hirr`.

The extra hypothesis is
`hI : RationalPointFamily.rootSet i ν I = simpleRelativeRoots i ν`. At
`I = Finset.univ` it is `RationalPointFamily.rootSet_univ i ν`, which needs
a `Fintype (SimpleRoot i ν)` instance.

- `levi_eq_top_of_rootSet_eq_simpleRelativeRoots`: under `hI`,
  `levi (ζ ∘ i) = ⊤`. By `Jacquet.standardLevi_eq_dynamic`, the standard
  Levi of the index is the dynamic centralizer of `ζ ∘ i`. It is also the
  dynamic centralizer of the zero cocharacter, and that centralizer is
  everything (`groupHom_zero_comp_eq_trivialCocharacter`,
  `Dynamic.centralizer_trivialCocharacter`).
- `positiveRelativeRoots_eq_empty_of_rootSet_eq_simpleRelativeRoots`:
  under `hI`, `positiveRelativeRoots i ζ = ∅`. Negation stability is the
  Library's `relativeRootNegation`.
- `rationalFunctionUnitaryRegular_inv_of_rootSet_eq_simpleRelativeRoots`:
  under `hI`, the regularity hypothesis `hreg` of
  `standardLeviPlancherelWeight` holds.
- `standardLeviPlancherelWeight_eq_one_of_rootSet_eq_simpleRelativeRoots`
  (**main result**): under `hI`, for every `hreg` and every `ω` in the
  orbit `O` of `π`,
  `standardLeviPlancherelWeight hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK hOppK p q … hirr hreg ω = 1`.
  Every `ω` is `orbitMap z` for some `z`, because the orbit map is a
  quotient map (`isOpenQuotientMap_discreteSeriesOrbitMap`). Then
  `standardLeviPlancherelWeight_orbitMap` reduces the claim to
  `plancherelWeight_eq_one_of_levi_eq_top`.
