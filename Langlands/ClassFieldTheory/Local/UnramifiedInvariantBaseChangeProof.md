# Finite base change of the unramified `H²` invariant

Authors: Worker 279, with code adapted from a public draft by Worker 28 (see
Credits).

The theorem
`Langlands.ClassFieldTheory.Local.unramifiedInvariantBaseChangeCompatibility.{u}`
proves exactly the published proposition
`Langlands.ClassFieldTheory.Local.UnramifiedInvariantBaseChangeCompatibility.{u}`
from [`UnramifiedInvariantCompatibilityStatement`](UnramifiedInvariantCompatibilityStatement.md).
For a compatible square `F ⊂ L ⊂ M`, `F ⊂ E ⊂ M` of `PadicField.{u} p`
carriers, with `L/F` and `M/E` finite Galois and canonically unramified, and
arithmetic coordinates `χL`, `χM`, it shows for every
`x : relativeCohomology F L 2` that

```text
inv(E,M)(relativeRestriction F E M 2 (relativeInflation F L M 2 x))
  = [E:F] • inv(F,L)(x).
```

The proof is unconditional. It uses no premise beyond the statement's
hypotheses and changes no published statement or construction. It covers
degree one, needs no Galois or unramified condition on `E/F`, and does not
require `M` to be the compositum `LE`. It does not use the separate
statements `CyclicClassNormNormalization` or
`UnramifiedInvariantInflationCompatibility`, nor any absolute invariant. The
only external theorem from the cohomology library is the published
`Langlands.Cohomology.CyclicH2.cocycleSumComparison`.

All auxiliary lemmas are in the namespace
`Langlands.ClassFieldTheory.Local.UnramifiedBaseChange`. The final theorem
only unpacks the binders and applies `invariant_restriction_inflation`. The
statement's local `NeZero` instances are inlined `letI`s, so the proof
re-derives them from `Module.finrank_pos`. `NeZero` is a proposition, so the
two instances agree by proof irrelevance.

## Notation

Write `n = [L:F]`, `m = [M:E]` and `N = [E:F]`. Let `f = residueDeg F E` be
the dimension of the actual residue extension of `E/F`. Here the residue
rings are those of `LocalGalois.baseIntegers` and
`LocalGalois.extensionIntegers`, defined by the spectral norm. Let
`σL = cyclicCoordinateGenerator χL = χL⁻¹(+1)`, and similarly `σM`. Let
`ρ = squareRestriction F E L M : Gal(M/E) → Gal(L/F)` be
`σ ↦ (σ.restrictScalars F).restrictNormal L`. This is exactly the group map
along which the composite `relativeRestriction ∘ relativeInflation` pulls
back.

## Generic cyclic lemmas

- `carry_sum_telescope`: for `t : ZMod n` and every `m`,
  `n · Σ_{i<m} cyclicCarry (i•t) t + (m•t).val = m · t.val`. The proof is by
  induction from `cyclicCarry_spec`.
- `carry_sum_one`: for `n > 1`, `Σ_{i<n} cyclicCarry (i•1) 1 = 1`. This is the
  case `t = 1`, `m = n` of the telescope.
- `baseUnit_pow`, `cyclicUnitCocycle_sum`: the generator sum
  `Σ_{i<m} cyclicUnitCocycle χ a (σ^i, σ)` equals
  `baseUnit (a ^ Σ_{i<m} cyclicCarry (i•χ(σ)) χ(σ))`.
- `cyclicH2NormEquiv_H2π_of_sum`: suppose a cocycle `c` has generator sum
  `Σ_{i<[L:K]} c(σ^i, σ)` equal to the base unit of `b`. Then
  `cyclicH2NormEquiv` sends its class to the norm-quotient class of `b`. The
  proof applies `cocycleSumComparison` to `c` and to the invariant element
  `baseUnit b`. It then unfolds `cyclicH2InvariantsEquiv` (Mathlib's
  even-degree periodicity isomorphism) and inverts
  `invariantsModNormEquiv` with `invariantsModNormEquiv_symm_projection`.
  This proof is adapted from the `n > 1` branch of Worker 28's unpublished
  draft for `CyclicClassNormNormalization` (task 10d6ec1c). There the cocycle
  is the specific carry cocycle; here it is an arbitrary cocycle with the
  given generator sum. It uses a finite
  heartbeat limit, `800000`, and
  `backward.isDefEq.respectTransparency false`.
- `exists_cyclicClass_eq`: for `[L:K] > 1`, every relative `H²` class is a
  carry class `cyclicClass K L χ a`. Choose `a` lifting the
  norm-quotient image of `x`. By `carry_sum_one`, the carry cocycle of `a` has
  generator sum `a`. Injectivity of `cyclicH2NormEquiv` gives `x`.
- `coordinateGenerator_pow_card`: `σ^d = 1` for the generator of a cyclic
  coordinate of order `d`.

## Restriction after inflation

`restriction_inflation_cyclicClass` computes

```text
relativeRestriction K E M 2 (relativeInflation K L M 2 (cyclicClass K L χ a))
  = cyclicClass E M (χ ∘ ρ) (image of a in E).
```

Both sides are `H2π` of explicit cocycles, and
`groupCohomology.H2π_comp_map_apply` moves the two maps onto cocycles. The
cocycles then agree pointwise (`groupCohomology.cocycles₂_ext`). The
inflation coefficient map `unitInclusionLinear L M` sends
`k • baseUnit K L a` to `k • baseUnit E M (image of a)`
(`unitInclusion_nsmul_baseUnit`). The reason is that both scalar towers
`K → L → M` and `K → E → M` give the same embedding of `K`
(`unitInclusion_baseUnit`). The carry arguments agree definitionally,
because the group map of the composite is `ρ`.

## Frobenius restriction

`coordinate_restriction` proves `χL(ρ(σM)) = ofAdd (f mod n)`, using the
arithmetic-coordinate hypotheses only.

- `padic_tower` derives the `Padic p`-tower `L → M` from the two given
  towers.
- `spectralNorm_algebraMap`: the spectral norm of `M/E` restricted to `L`
  equals the spectral norm of `L/F`. Both equal the canonical norms, by the
  published `ArithmeticCoordinate.spectralNorm_eq_canonicalNorm`. Canonical
  norms are preserved by `Padic p`-embeddings (`canonicalNorm_map`).
- `residue_eq_iff`: two integral elements have the same residue exactly when
  the spectral norm of their difference is `< 1`.
- `residueHom_restriction`: suppose `g ∈ Gal(M/E)` acts on the residue field
  of `M` as `y ↦ y^q`. Then `ρ(g)` acts on the residue field of `L` as
  `y ↦ y^q`. Write `y` for the image of an integer `x` of `L` in `M`. The
  hypothesis gives `‖g y - y^q‖ < 1` in `M`. Because `L → M` is compatible
  with `g` and `ρ(g)` (`AlgEquiv.restrictNormal_commutes`), this element is
  the image of `ρ(g) x - x^q`. The norm comparison transports the inequality
  to `L`.
- `residue_card_pow`, `residueDegree_eq_mul`: the residue field of `E` has
  `q_F ^ f` elements, so the canonical absolute residue degrees satisfy
  `f_E = f_F · f`.
- `residueHom_pow_apply`: `σL^f` acts by `y ↦ y^(q_F^f)`.

By the coordinate hypothesis, `σM` acts by `y ↦ y^(q_E)` with
`q_E = q_F^f`. Hence `ρ(σM)` and `σL^f` have the same residue action.
Injectivity of the residue action on `Gal(L/F)` (the first half of
`IsArithmeticUnramifiedCoordinate F L χL`) gives `ρ(σM) = σL^f`. Then
`χL(σL^f) = ofAdd (f • 1)`.

## Valuations and the invariant

- `residueDeg_mul_ord_algebraMap`: `f · ord_E(a) = N · ord_F(a)` for
  `a ∈ F`. The published `ramificationIndex_mul_ord_relative_algebraMap`
  gives `e_F · ord_E(a) = e_E · ord_F(a)`. Combined with
  `e_E f_E = [E:Q_p] = N · e_F f_F` and `f_E = f_F · f`, cancelling `f_F`
  and `e_F` gives the claim.
- `ord_pow`: `ord(x^k) = k · ord(x)`.
- `invariant_H2π_of_sum`: suppose a cocycle's generator sum at the
  coordinate generator is the base unit of `b`. Then its
  `unramifiedH2Invariant` is `rationalClass (ord(b) / degree)`. This combines
  `cyclicH2NormEquiv_H2π_of_sum` with the published
  `unramifiedH2Invariant_normRepresentative`.
- `rationalClass_scaling`: assume `n S = m t`, `n q + t = f` and
  `f · oE = N · oF`. Then `S·oE/m` and `N·oF/n` differ by the integer
  `-q·oE`, so they agree in `ℚ/ℤ`.

## Assembly

`invariant_restriction_inflation` proves the formula for fixed instances.

1. If `n = 1`, the published `unramifiedH2Invariant_degree_one` and
   `unramifiedH2Invariant_injective` give `x = 0`, and both sides vanish.
2. If `n > 1`, write `x = cyclicClass F L χL a` (`exists_cyclicClass_eq`).
   Its carry cocycle has generator sum `a`, so
   `inv(F,L)(x) = rationalClass (ord_F(a)/n)`.
3. Restriction after inflation is
   `cyclicClass E M (χL ∘ ρ) (image of a)`. Let `t = χL(ρ(σM))`, which is
   `f mod n`. Then `m • t = 0`, because `σM^m = 1`. The telescope gives
   `n S = m · t.val`, where `S = Σ_{i<m} cyclicCarry (i•t) t`. The
   generator sum at `σM` of the restricted cocycle is the base unit of
   `(image of a)^S`. So the left side is
   `rationalClass (S · ord_E(a)/m)`.
4. `rationalClass_scaling` finishes the proof, with `q = f / n`,
   `t.val = f % n` and the valuation identity above.

## Relation to the literature

Serre, *Local Fields*, Chapter XIII, Section 3, Proposition 7, proves that
restriction multiplies the invariant by the field degree. Its proof uses the
Frobenius power `f` in the unramified direction and valuation scaling `e` in
the ramified direction. The implemented proof uses the same two inputs:
`ρ(σM) = σL^f` and `f · ord_E = N · ord_F`. It works with the Library's
actual finite cocycle constructions and the explicit cyclic periodicity
comparison, not with Brauer groups. Registered source:
`serre-1979-local-fields`.

## Credits

The tactic proof of `cyclicH2NormEquiv_H2π_of_sum` is adapted from
Worker 28's public draft `CyclicClassNormProof` (task 10d6ec1c, draft
revision 1). That draft is not imported, and this module does not depend on
`CyclicClassNormNormalization`. Worker 84, a co-executor of this task,
discussed the division of work. No code from their drafts is used here.
