# Values on the unitary characters of rational functions regular there

Worker 5. Module `Langlands.Representation.Plancherel.RationalUnitaryRegularValue`,
namespace `Langlands.Plancherel`.

Waldspurger's density `μ` is a rational function on the unramified characters
of `M`. By Lemma V.2.1 it is regular on the unitary orbit, so it has a value
`μ(ω)` at each point of that orbit. Chapter VI integrates this function against
smooth sections. The Library defines `μ` only as an element of the field of
rational functions (`plancherelDensity`, module `RationalPlancherelDensity`).
This module supplies the value function:

1. A generic part. For any rational function `f` on the unramified characters
   of a connected reductive group that is regular at every unitary character,
   it defines the function `z ↦ f(z)` on the unitary characters. It proves
   that the value does not depend on the presentation, that the function is
   smooth in the Library's circle coordinates and continuous, and that the
   construction respects sums, products, translation and nonnegative values.
   Nothing in this part is specific to `j_P` or `μ`.
2. A part for `μ`. Under the hypothesis that `j_P⁻¹` is regular at every
   unitary character, it defines the Plancherel weight
   `plancherelWeight : Im X(M) → ℂ`, the value function of `μ`. The weight is
   smooth in circle coordinates, continuous, a nonnegative real number wherever
   `j_P⁻¹` has a nonnegative real value, and invariant under translation by
   unitary self-twists of the inducing representation.

Every result in the module is proved; the module has no Prop-valued target.
The regularity of `j_P⁻¹` on the unitary characters, the part of
Waldspurger IV.3 (6) that the weight needs, is a hypothesis of the
definition. It is not proved here.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082, registered as `waldspurger-2003-plancherel`, PDF
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

- V.2, printed p.292 / PDF p.58: `μ(ω) = j(ω)⁻¹ ∏_α γ(M_α|M)²` for `ω ∈ O`,
  where `α` runs over the reduced roots of `A_M` up to sign.
- Lemma V.2.1, printed p.292 / PDF p.58: `μ` is a rational function regular
  on `O`, and for every `ω ∈ O`, `μ(ω) ≥ 0`. The proof (printed p.293) refers
  to IV.3 (2), (3), (5) and (6).
- IV.3 (6), printed p.287 / PDF p.53: `j(π) ≠ 0` for square-integrable `π`.
- VI.3, printed p.302 / PDF p.68: `f_ψ(g) = ∫_O μ(ω) (E^G_P ψ_ω)(g) dω`, the
  use of `μ` as a function on `O`.

## Provenance

Derived. Waldspurger treats `μ` as a function on `O` without discussing how a
regular rational function defines one. The generic part is the standard
construction: at a point where `f = m / n` with `n(z) ≠ 0`, the value is
`m(z) / n(z)`. The Library's `rationalFunction_value_eq` (module
`DynamicOppositeUnitaryScalarStatement`) shows that this does not depend on the
presentation. Smoothness uses the Library's circle coordinates
(`rationalCanonicalUnitaryUnramifiedCharacterCoordinates`) and the Laurent
description of the regular functions (`rationalCanonicalUnramifiedLaurentAlgebraEquiv`,
`rationalUnramifiedLaurentAlgebraEquiv_eval_unitary`), both in module
`RationalUnitaryNonvanishing` and the modules it imports.

The weight is the value function of the Library's `plancherelDensity`, with
three differences from Waldspurger:

- It is a function on `Im X(M)`, the unitary unramified characters of `M`,
  and not on the orbit `O = {π ⊗ χ}`. Descending it to `O` uses its invariance
  under the stabilizer of `π`, proved here; the descent itself is not done
  here.
- It is defined only under the hypothesis `hreg` that `j_P⁻¹` is regular at
  every unitary character. In Waldspurger this follows from IV.3 (6) and
  IV.3 (5).
- Nonnegativity is proved at each unitary point where `j_P⁻¹` has a
  nonnegative real value. The Library proves this at the unitary points where
  both chosen continuations are regular, assuming the open Hermitian
  adjunction target (module `DynamicOppositeUniformNonvanishing`). It does not
  yet have it at every unitary point.

## Laurent evaluation along the angle covering

`finiteTorusExp θ` is the point `(e^{iθ_j})_j` of a product of circles.

- `finiteLaurentEvaluation_finiteTorusExp_single`: the Laurent monomial
  `a · x^m` takes the value `a · ∏_j exp(i m_j θ_j)` at `finiteTorusExp θ`.
- `contDiff_finiteLaurentEvaluation_finiteTorusExp`: for every Laurent
  polynomial `p`, `θ ↦ p(finiteTorusExp θ)` is smooth (`ContDiff ℝ ∞`).
  Proof: induction on `p` over sums and monomials; a monomial is a constant
  times a finite product of `exp` composed with real linear functions.

A private lemma `circleToUnits_zpow_coe` identifies integer powers in `Circle`
and in `ℂˣ`.

## The value function

Throughout, `G` is a group scheme over a nonarchimedean local field `F`,
affine and locally of finite type, with `hG : IsConnectedReductive G`. `RG`
are the regular functions on the unramified characters `X(G)`, `KG` its
fraction field `rationalUnramifiedFunctionField`, and `UG` the unitary
unramified characters `unitaryUnramifiedCharacters`.

- `unitaryToUnramified z`: a unitary unramified character viewed as an
  element of `X(G)`.
- `RationalFunctionUnitaryRegular G hG f`: for every unitary `z`,
  `RationalFunctionRegularAt … f z`, that is `f = m / n` with `m, n ∈ RG` and
  `n(z) ≠ 0`.
- `rationalUnitaryValue G hG f hf z`: `m(z) / n(z)` for the presentation
  chosen by `Classical.choose` from `hf z`.
- `rationalUnitaryValue_eq`: for every presentation `f = m / n` with
  `n(z) ≠ 0`, the value is `m(z) / n(z)` (by `rationalFunction_value_eq`).
- `rationalUnitaryValue_congr`: equal functions have equal value functions,
  whatever the regularity proofs.

## Smoothness and continuity

- `regular_val_unitaryToUnramified_coordinates_symm`: in the circle
  coordinates `Φ`, a regular function `b` at the unitary point `Φ⁻¹(c)` is the
  Laurent evaluation of `Λ⁻¹(b)` at `c`, where `Λ` is the canonical Laurent
  algebra equivalence.
- `isSmoothFiniteTorusFunction_rationalUnitaryValue`: the function
  `c ↦ rationalUnitaryValue … (Φ⁻¹ c)` on the product of circles is smooth in
  the sense of `IsSmoothFiniteTorusFunction`, that is its pullback along
  `finiteTorusExp` is `ContDiff ℝ ∞`. Proof: smoothness is checked at each
  angle `θ`. Choose `f = m / n` with `n` nonzero at the point `Φ⁻¹(e^{iθ})`.
  Along the angle covering `m` and `n` are smooth Laurent evaluations, and `n`
  stays nonzero near `θ`. There the value function equals
  `m · n⁻¹`, which is smooth at `θ`.
- `continuous_rationalUnitaryValue`: the value function is continuous on
  `UG`. It is the composite of the continuous function of the previous item
  with the homeomorphism `Φ`.

## Algebra, translation, nonnegativity

- `rationalFunctionUnitaryRegular_algebraMap`, `rationalUnitaryValue_algebraMap`:
  a regular function `b` is regular on the unitary characters, with value
  `b(z)`.
- `RationalFunctionUnitaryRegular.mul`, `.add`, `rationalUnitaryValue_mul`,
  `rationalUnitaryValue_add`: products and sums, with the value of a product
  (sum) the product (sum) of the values. Proof: multiply (add) presentations;
  the denominators `n n'` do not vanish at `z`.
- `RationalFunctionUnitaryRegular.translation`, `rationalUnitaryValue_translation`:
  for a unitary `τ`, the translate of `f` by `τ`
  (`rationalUnramifiedFunctionFieldTranslation`) is regular on the unitary
  characters, and its value at `z` is the value of `f` at `τ z`.
- `rationalUnitaryValue_mul_left_of_translation_eq`: if the translate of `f`
  by a unitary `τ` is `f`, the value function is invariant under `z ↦ τ z`.
- `RationalFunctionUnitaryRegular.of_nonnegAt`: if `f` has a nonnegative real
  value (`RationalFunctionNonnegAt`) at every unitary point, `f` is regular on
  the unitary characters.
- `rationalUnitaryValue_nonneg`: at a unitary point where `f` has a
  nonnegative real value `r`, the value function equals `r`.

## Characters of finite order

`mem_unitaryCharacters_of_isOfFinOrder`: a continuous character
`τ : M →ₜ* ℂˣ` of finite order is unitary. Proof: if `τⁿ = 1` with `n > 0`,
then `‖τ(g)‖ⁿ = 1`, so `‖τ(g)‖ = 1`.

## The Plancherel weight

The section uses the setting of `plancherelDensity`: `χ = ζ ≫ i`,
`P = P_G(χ)`, `P̄ = P_G(χ⁻¹)`, `M = Z_G(χ)` (`parameterScheme χ`), compact
open `K` with `G(F) = P K = P̄ K`, a smooth representation `A` of `M(F)`,
continuation data `p, q`, nonempty open `DForward`, `DReverse` in the full
convergence domains, and a nonempty open irreducibility locus `D`. Write `j_P`
for `conditionalCanonicalRationalScalar … A p q …` and
`μ = plancherelDensity …`, which is by definition
`(∏_α γ(M_α|M)²) · j_P⁻¹`, the constant being `plancherelDensityConstant`.
Let `hreg : RationalFunctionUnitaryRegular (parameterScheme χ) … j_P⁻¹`.

- `plancherelDensity_unitaryRegular`: `hreg` implies that `μ` is regular on
  the unitary characters (a constant times `j_P⁻¹`).
- `plancherelWeight … hreg : Im X(M) → ℂ`: the value function of `μ`.
- `plancherelWeight_eq`: `plancherelWeight … hreg z = c · j_P⁻¹(z)` with
  `c = plancherelDensityConstant` and `j_P⁻¹(z)` the value function of `j_P⁻¹`.
- `isSmoothFiniteTorusFunction_plancherelWeight`,
  `continuous_plancherelWeight`: smoothness in the circle coordinates and
  continuity.
- `plancherelWeight_nonneg`: at a unitary `z` where `j_P⁻¹` has a nonnegative
  real value `r`, the weight is the nonnegative real number `c · r` (the
  constant is a square, `plancherelDensityConstant_nonneg`).
- `plancherelWeight_stabilizer_invariant`: for `τ` in the twist stabilizer
  `smoothRepUnramifiedTwistStabilizer` of the inducing representation, with
  `τ` unitary, `plancherelWeight … (τ z) = plancherelWeight … z`. Proof: the
  Library's `plancherelDensity_stabilizer_fixed` and
  `rationalUnitaryValue_mul_left_of_translation_eq`.
- `plancherelWeight_stabilizer_invariant_of_isOfFinOrder`: the same for `τ` of
  finite order in the stabilizer, which is then unitary by
  `mem_unitaryCharacters_of_isOfFinOrder`. Every element of a finite
  stabilizer has finite order.

## Not proved here

- `hreg`, the regularity of `j_P⁻¹` at every unitary character. In
  Waldspurger it follows from IV.3 (5) and (6). For the Library's `j_P` it is
  part of the conclusion of the open target
  `ConditionalDynamicOppositeUnitaryScalarStatement` (module
  `DynamicOppositeUnitaryScalarStatement`, `A` square-integrable modulo a
  central subgroup), since a
  nonnegative real value includes regularity.
- Nonnegativity of `j_P⁻¹` at every unitary point, and so of the weight at
  every point.
- The descent of the weight to the orbit `O`, and the identification of the
  Library's `j_P` and `rankOneGammaProduct` with Waldspurger's `j` and
  `γ(M_α|M)`.
