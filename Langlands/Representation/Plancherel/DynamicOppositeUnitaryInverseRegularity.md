# Nonnegativity of `j_P⁻¹` on the unitary axis, reduced to regularity

Worker 5. The module states two Prop-valued targets about the Library's
canonical scalar `j_P` of `J_{P|P̄} J_{P̄|P}`
(`conditionalCanonicalRationalScalar`, module `DynamicOppositeCanonicalScalar`).
Both use the hypotheses of `ConditionalDynamicOppositeUnitaryPositiveStatement`
(module `DynamicOppositeUniformNonvanishing`):

- `Langlands.Plancherel.ConditionalDynamicOppositeUnitaryInverseRegularStatement`:
  `j_P⁻¹` is regular at every unitary unramified character.
- `Langlands.Plancherel.ConditionalDynamicOppositeUnitaryInverseNonnegStatement`:
  `j_P ≠ 0`, and at every unitary unramified character `j_P⁻¹` is regular
  with a nonnegative real value.

The module proves the second target from the first and the Hermitian
adjunction target `ConditionalDynamicOppositeHermitianAdjunctionStatement`
(module `DynamicOppositeHermitianAdjunctionStatement`):
`conditionalDynamicOppositeUnitaryInverseNonneg_of_regular`. It proves neither
the regularity target nor the Hermitian adjunction. So the positivity part of
IV.3 (6) is reduced to regularity. Everything else in the module is proved in
full, including a generic density lemma for nonnegative values.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082, registered as `waldspurger-2003-plancherel`, PDF
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

- IV.3, printed p.285 / PDF p.51: definition of the rational function `j_P`
  by `J_{P|P̄}(π') J_{P̄|P}(π') = j_P(π')` on the irreducibility locus.
- IV.1, just after (13), printed p.283 / PDF p.49: for `P` proper maximal,
  `λ ↦ J_{P̄|P}(π ⊗ χ_λ)` depends only on the coordinate `⟨λ, α^∨⟩`
  (used only in the description of the open regularity route below).
- IV.3 (4)–(5), printed pp.286–287 / PDF pp.52–53: the product formula
  `j(π) = ∏ j_α(π)` over the reduced roots of `A_M`.
- IV.3 (6) and its proof, printed p.287 / PDF p.53: "si π est de carré
  intégrable, j(π) ≠ 0". The proof first reduces to `M` maximal by (5). It
  then fixes `e` with `(J_{P̄|P}(π ⊗ χ) e)(1)` regular and nonzero at
  `χ = 1`. For unitary `χ` the Hermitian adjunction gives
  `j(π ⊗ χ) (e, e) = (J_{P̄|P}(π ⊗ χ) e, J_{P̄|P}(π ⊗ χ) e)`.
- V.2.1, printed p.292 / PDF p.58: `μ(ω)` is a nonzero constant multiple of
  `j(ω)⁻¹` and is regular and nonnegative on the unitary orbit.

## Provenance

Both targets are derived. As in the Library's
`ConditionalDynamicOppositeUnitaryScalarStatement` (module
`DynamicOppositeUnitaryScalarStatement`), "j(π) ≠ 0" in IV.3 (6) is read as:
`j⁻¹` is regular at every unitary point. This is how V.2 uses it, to make `μ`
regular on the unitary orbit. Nonnegativity comes from the displayed identity
in the proof of IV.3 (6). Waldspurger does not state it separately.

The regularity target is the regularity half of that reading. It is stated
under the hypotheses of the strict positivity target of
`DynamicOppositeUniformNonvanishing`, not under square-integrability (see
"The targets" below). The nonnegativity target is the conclusion of
`ConditionalDynamicOppositeUnitaryScalarStatement` under those same
hypotheses.

The reduction replaces nothing in Waldspurger's argument. It separates the
positivity, which is proved here at all unitary points from the positivity at
the common regular points, from the regularity, which needs the product
formula (see "Not proved here").

## Laurent evaluation on circle tuples

Section `Circle` is generic.

- `circleToUnits_zpow_val`: `Circle.toUnits z ^ k` and `z ^ k` have the same
  complex value.
- `continuous_finiteLaurentEvaluation_circle`: for a Laurent polynomial
  `p ∈ ℂ[ℤⁿ]`, the map `c ↦ p(c)` on `(S¹)ⁿ` is continuous. Proof by
  induction on `p`: a monomial is the product of the continuous maps
  `c ↦ c_i ^ m_i`, and sums and scalar multiples are continuous.
- `circle_infinite_of_mem_nhds`: every neighbourhood of a point of `S¹` is
  infinite. `S¹` is infinite (it is in bijection with `(-π, π]`), path
  connected and T1, so no point is isolated (Mathlib's
  `infinite_of_mem_nhds`).

## Nonnegative values by density

Section `Density` works with a connected reductive group scheme `G` over a
nonarchimedean local field `F`, with the rational-point topology and the
continuity proof `continuous_rationalValuationImageProjection G`.

- `rationalUnitaryRegularRestriction_coordinates_symm`: let `Φ` be the
  Library's circle coordinates `rationalCanonicalUnitaryUnramifiedCharacterCoordinates`
  of the unitary unramified characters, and `a` the Library's Laurent
  algebra isomorphism `rationalCanonicalUnramifiedLaurentAlgebraEquiv`. For a
  regular function `b` and `c ∈ (S¹)ⁿ`, `b(Φ⁻¹ c)` is the Laurent evaluation
  of `a⁻¹ b` at `c`. This is the Library's
  `rationalUnramifiedLaurentAlgebraEquiv_eval_unitary` applied to `a⁻¹ b`.
- `isClosed_nonnegReal_complex`: the set
  `S = {w ∈ ℂ | 0 ≤ Re w ∧ Im w = 0}` is closed.
- `exists_nonneg_real_iff`: `w = r` for some real `r ≥ 0` if and only if
  `w ∈ S`.
- `RationalFunctionRegularAt.nonnegAt_of_unitary`. Let `f` be a rational
  function regular at a unitary point `z`. Let `g` be a nonzero regular
  function such that `f` has a nonnegative real value
  (`RationalFunctionNonnegAt`) at every unitary point `w` with `g(w) ≠ 0`.
  Then `RationalFunctionNonnegAt f z`.

  Proof. Write `f = m / n` with `n(z) ≠ 0`. It suffices to show
  `m(z) / n(z) ∈ S`. Suppose not. The map `c ↦ m(Φ⁻¹ c) / n(Φ⁻¹ c)` is
  continuous at `Φ z`, since the denominator is nonzero there. So the set of
  `c` with `n(Φ⁻¹ c) ≠ 0` and `m(Φ⁻¹ c) / n(Φ⁻¹ c) ∉ S` is a neighbourhood of
  `Φ z`. It contains a box `∏ t_i` of neighbourhoods `t_i` of the coordinates
  of `Φ z`, and each `t_i` is infinite. The ring of regular functions is a
  domain, so `g n ≠ 0`. By the Library's `finiteLaurent_eq_zero_of_eval_on_box`
  (`RationalUnramifiedDensity`), the Laurent polynomial `a⁻¹ (g n)` does not
  vanish at some point `c` of the box. Put `w = Φ⁻¹ c`, a unitary point with
  `g(w) n(w) ≠ 0`. By hypothesis `f` has a nonnegative real value at `w`
  through some presentation. By the Library's `rationalFunction_value_eq`,
  `m(w) / n(w)` is that value, so it lies in `S`. This contradicts the choice
  of the box.

## The targets

`ConditionalDynamicOppositeUnitaryInverseRegularStatement` and
`ConditionalDynamicOppositeUnitaryInverseNonnegStatement` quantify over
exactly the data of `ConditionalDynamicOppositeUnitaryPositiveStatement`:

- a nonarchimedean local field `F`, an affine group scheme `G` over `F` of
  locally finite type, a cocharacter `χ`, the structural premises `hRefl`,
  `hCST`, `hG : IsConnectedReductive G`, and `P = parabolic χ`,
  `P̄ = oppositeParabolic χ`, `M = levi χ`;
- a compact open subgroup `K` with `G(F) = P K` (`hPK`) and `G(F) = P̄ K`
  (`hOppK`), and the split hypotheses `_hKsplit`, `_hOppKsplit` (the Levi
  projections send `P ∩ K` and `P̄ ∩ K` into `K`);
- a smooth complex representation `A` of `M(F)` with
  `_hA : IsUnitarizable A.representation`;
- the conditional data of `conditionalCanonicalRationalScalar`: forward and
  reverse continuations `p`, `q`, nonempty open sets `DForward` and
  `DReverse` inside the forward and reverse full convergence domains, and a
  nonempty open set `D` of parameters with irreducible induction (`hi`);
- `_hdag`: `z ↦ z† = z̄⁻¹` maps `DForward` into
  `reverseFullDomainRegion χ K hK A`.

Conclusions, with `j_P = conditionalCanonicalRationalScalar … p q …` in the
field of rational functions of `parameterScheme χ`:

- regularity target: for every `z` whose value lies in
  `unitaryUnramifiedCharacters (normCharacters χ)`,
  `RationalFunctionRegularAt … j_P⁻¹ z`, that is, `j_P⁻¹ = m / n` for regular
  functions `m`, `n` with `n(z) ≠ 0`;
- nonnegativity target: `j_P ≠ 0`, and for every such `z`,
  `RationalFunctionNonnegAt … j_P⁻¹ z`, that is, a presentation as above
  with `m(z) / n(z)` a nonnegative real number.

Remarks.

- Unlike `ConditionalDynamicOppositeUnitaryPositiveStatement`, the
  conclusions hold at every unitary point, not only where both chosen
  continuations are regular.
- The value can be `0`, so positivity cannot be expected. For `GL₂` and
  `A = χ₁ ⊗ χ₂` with `χ₁ = χ₂` unramified, `μ`, a nonzero constant multiple
  of `j_P⁻¹`, vanishes at the unitary point `s = 0` of the family
  `χ₁|·|^s ⊗ χ₂|·|^{-s}`.
- `A` is unitarizable, not necessarily square-integrable. Waldspurger states
  IV.3 (6) for square-integrable `π`. His argument for `M` maximal uses only
  an invariant positive definite form, the adjunction and IV.1 (10), and the
  reduction to maximal `M` uses the product formula IV.3 (5). The split
  hypotheses on `K` and `_hdag` are kept as in the strict positivity target,
  so that the Library's Hermitian adjunction target applies. With them the
  targets are weaker, not stronger.
- The Library's `ConditionalDynamicOppositeUnitaryScalarStatement` has the
  same conclusion as the nonnegativity target under different hypotheses
  (square-integrability modulo a central subgroup, no split hypotheses, no
  `_hdag`). Neither target implies the other as stated.

## The reduction

`conditionalDynamicOppositeUnitaryInverseNonneg_of_regular` takes the
Hermitian adjunction target `H` and the regularity target `R` and proves the
nonnegativity target.

- `conditionalDynamicOppositeUnitaryPositive_of_hermitianAdjunction H`
  (module `DynamicOppositeUniformNonvanishing`) gives `j_P ≠ 0`, which is the
  first conjunct. It also gives `RationalFunctionPosAt … j_P⁻¹ w` at every
  unitary `w ∈ p.regularRegion ∩ q.regularRegion`.
- The denominators of `p` and `q` are nonzero regular functions, since they do
  not vanish on the nonempty domains `DForward` and `DReverse`. Their product
  `g` is nonzero because the regular functions form a domain
  (`rationalUnramifiedRegularFunctions_isDomain`). If `g(w) ≠ 0`, then both
  denominators are nonzero at `w`, so `w` lies in both regular regions.
- At a unitary `z`, `R` gives regularity of `j_P⁻¹`. The positive values at
  the unitary points with `g(w) ≠ 0` are nonnegative
  (`RationalFunctionPosAt.nonnegAt`). `RationalFunctionRegularAt.nonnegAt_of_unitary`
  then gives `RationalFunctionNonnegAt … j_P⁻¹ z`.

The last section uses the local instances of `DynamicOppositeCanonicalScalar`
and the Borel instances `hermitianAdjunctionPointMeasurable` and
`hermitianAdjunctionPointBorel` of `DynamicOppositeHermitianAdjunctionStatement`.

## Not proved here

- The Hermitian adjunction target (a separate proof task exists for it).
- The regularity target. The Lean target quantifies over the full space
  `X(M)` of unramified characters of the actual Levi, with no quotient by
  central twists; it is not restricted to a one-dimensional family.
  Waldspurger's route has three steps, none of which is in the Library:
  1. Product formula. By IV.3 (4)–(5), `j = ∏ j_α` over the reduced roots
     `α` of `A_M`, where `j_α` is the scalar of `M` as a maximal Levi of
     `M_α`. This rests on IV.1 (12) for the actual radicals and on IV.1 (14).
  2. One-coordinate dependence. Even for `M` maximal, `X(M)` is not
     one-dimensional in general: for `G = GL₂` and the diagonal Levi
     `M = G_m × G_m`, `X(M) ≅ (ℂˣ)²`. What makes a one-variable argument
     possible is IV.1, just after (13) (printed p.283 / PDF p.49): for `P`
     maximal and `λ ∈ a*_{M,ℂ}`, the function
     `λ ↦ J_{P̄|P}(π ⊗ χ_λ)` depends only on the single coordinate
     `⟨λ, α^∨⟩`, where `α` is the unique element of `Δ(P)`. For the actual
     Library operators this has to be proved, for instance as
     `j(z · χ) = j(z)` for every unramified character `χ` of `M` that is
     the restriction of an unramified character of `G` (respectively of
     `M_α` in step 1), so that `j⁻¹` is the pullback of a rational function
     of one variable along a monomial map.
  3. One-variable pole argument (proof of IV.3 (6)). Near a unitary point,
     `j(z) = ‖J_{P̄|P}(z) e‖² / ‖e‖²` on the unitary characters, by the
     Hermitian adjunction, and it is bounded below there, because the
     vectors `J_{P̄|P}(z) e` lie in a fixed finite-dimensional space and
     their values at `1` are a fixed nonzero vector (IV.1 (10)). A rational
     function of one variable that is bounded on an arc through a point has
     no pole there, and regularity then pulls back to `X(M)` by step 2.
  Steps 1 and 2 are both needed: in several variables, boundedness on the
  unitary points does not imply regularity (`x² / (x² + y²)`).
