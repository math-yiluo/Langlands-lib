# Reduction of the unequal-rank dual Euler factorization

Module `Langlands.Global.RankinSelberg.UnequalDualEulerFactorizationReduction`, namespace
`Langlands.Global.RankinSelbergGlobal.UnequalDualEuler`.

## Main results

`UnequalDualEulerFactorizationReductionStatement` is the proposition

```text
UnramifiedWhittakerFactorizationStatement → WhittakerCellDecompositionStatement →
  UnequalUnfoldingStatement → ContragredientDualWhittakerStatement →
    UnequalDualEulerFactorizationStatement
```

with the universe parameters `u` (number fields) and `uQ` (spectral presentations) free.
The theorem `unequalDualEulerFactorizationReduction` proves it.
`unequalDualEulerFactorization_of_premises` is the same result in curried form. The four
premises are Library statements:

- `UnramifiedWhittakerFactorizationStatement` (module
  `Langlands.Global.RankinSelberg.UnramifiedWhittakerFactorizationStatement`). At a finite
  place `v ∉ S` and for `g` with `g_v = 1`, `W_x(g ι_v(h)) = W_x(g) W°(h; a)` for the
  `ψ`-Whittaker function of a vector spherical outside `S`. The analogous identity holds for
  the `ψ⁻¹`-Whittaker function with the inverse standard character. This is Shintani's
  formula in global form.
- `WhittakerCellDecompositionStatement` (module
  `Langlands.Global.RankinSelberg.WhittakerCellDecompositionStatement`). For integrable `f`
  on `N_m(𝔸)\GL_m(𝔸)`,
  `∑_λ N(v)^(∑_(i<j)(λ_i-λ_j)) ∫_(U_A) f(N_m(𝔸) ι_v(ϖ^λ) g) = ∫_(U_(A∪{v})) f`.
- `UnequalUnfoldingStatement` (module `Langlands.Global.RankinSelberg.UnequalUnfoldingStatement`),
  used only for the absolute convergence of the dual integral.
- `ContragredientDualWhittakerStatement` (module
  `Langlands.Global.RankinSelberg.EqualDualEulerFactorizationReduction`). The function
  `g ↦ W_x(w_n ᵗg⁻¹)` is the `ψ⁻¹`-Whittaker function of a vector `x̃` of the
  contragredient realization that is spherical outside `S`.

The proof also uses proved results of the modules
`Langlands.Representation.RankinSelberg.UnramifiedUnequalLocalSum` (`localTerm`,
`localTerm_eq_sphericalWhittaker`, `exists_hasSum_localTerm`),
`Langlands.Global.RankinSelberg.PartialEulerProductConvergence`
(`exists_partialEulerFactor_convergence`, `exists_hasSatakeBound_presentation`),
`Langlands.Global.RankinSelberg.PartialIntegralExhaustion`
(`integral_eq_hasProd_mul_setIntegral`, `measurableSet_unipotentIntegralClasses`),
`Langlands.Global.RankinSelberg.LocalPointFactorization` (Worker 5130's lemmas on the points
`ι_v(h)`, the uniformizer `placeUniformizer v` and determinants) and
`Langlands.Representation.Whittaker.RectangularSupport` (the support lemma for spherical
Whittaker functions on `[[g,0,0],[x,I,0],[0,0,1]]`).

## Auxiliary results

Notation: `ι_v(h) = localPoint F m v h`, `g_v = finiteComponent F m v g`, `E` the matrix
of an adelic point, `w = unfoldingWeyl F h = diag(I_(t+1), w_(r-t))`,
`ϖ = placeUniformizer v`, `𝒪_v` the integers of the canonical valuation
`canonicalValuation v` of `padicField v`, and `q_v` its residue cardinality.

- Points: `adeles_ext`, `points_ext` (an adelic point is determined by its infinite part
  and its finite components), `infinite_localPoint`, `localPoint_mem_unipotentAdelic`
  (`ι_v(u) ∈ N_m(𝔸)` for upper unitriangular `u`), `finiteComponent_pad`, `infinite_pad`,
  `pad_localPoint` (`pad(ι_v(P)) = ι_v(diag(P, I))`), `finiteComponent_rectangularPoint`
  (`rect(g, x)_v = rectGL h g_v x_v`), `unfoldingWeyl_inv` (`w⁻¹ = w`),
  `unfoldingWeyl_entry` (the entries of `w` are `0` or `1`; its proof uses the
  propositional helper `imp_or_imp`: `(p → a) ∨ (¬p → b)`).
- Local facts: `rectGL_torus` (`diag(ϖ^λ, I) = ϖ^(λ,0)`, with the weight `padZeroWeight`
  of `UnramifiedUnequalLocalSum`), and `modulusExponent_eq`
  (`∑_(i<j)(λ_i-λ_j) = ∑_i (t-2i)λ_i`; the computation is that of Worker 5130's
  `EqualEulerLocal.sum_sub_of_lt_eq`).
- The place `v`: `integer_trivial_of_conductor` and `exists_ne_one_of_conductor`. If the
  component `ψ_v` has additive conductor `0`, then `ψ_v = 1` on `𝒪_v`, and for `z ∉ 𝒪_v`
  there is `c ∈ 𝒪_v` with `ψ_v(cz) ≠ 1` (from the Library's
  `mem_additiveLattice_of_forall_complex_mul_eq_one`). Also `finiteComponent_unfoldingWeyl_mem`
  (`w_v ∈ GL_(r+1)(𝒪_v)`), and `apply_localPoint_mul_of_split`: if `Φ(g ι_v(h)) = Φ(g) φ(h)`
  whenever `g_v = 1`, then `Φ(ι_v(Q) Y) = φ(Q) Φ(Y)` as soon as
  `φ(Q Y_v) = φ(Q) φ(Y_v)`.
- `sphInv v ψ_v r a` and `sphStd v ψ_v t b` are the Library's `sphericalWhittaker` at
  `ϖ`, with the inverse standard and the standard character of `ψ_v`, the residue
  cardinality `q_v` and Satake tuples `a`, `b`.
- `cellFactor h v ψ_v a b s Q = sphInv(diag(Q, I)) · sphStd(Q) · |det Q|_v^(s-(r-t)/2)`.
- `whittaker_split` restates the two halves of `UnramifiedWhittakerFactorizationStatement`
  at `ϖ`. `whittakerInv_rectangularPoint_localPoint_mul`: for `g_v ∈ GL_(t+1)(𝒪_v)`,
  `W̃(rect(ι_v(Q) g, y) w) = sphInv(diag(Q, I)) W̃(rect(g, y) w)` for every `y`, where `W̃` is
  the `ψ⁻¹`-Whittaker function of a spherical vector. `whittaker_localPoint_mul_of_integral`:
  `W'(ι_v(Q) g) = sphStd(Q) W'(g)` for such `g`.
- `dualKernel_localPoint_mul_of_integral` and `dualKernel_localPoint_torus_mul` (the cell
  property). For `g_v ∈ N_(t+1)(F_v) GL_(t+1)(𝒪_v)`, the Library's dual kernel
  `Unfolding.dualKernel` of `ρ(w)W̃` and `W̃'` at `ι_v(ϖ^λ) g` equals
  `cellFactor(ϖ^λ)` times its value at `g`.
- `integrand_shift` is the same identity for `dualWhittakerIntegrand` on quotient classes.
  `zpow_modulusExponent_mul_cellFactor` gives
  `N(v)^(∑_(i<j)(λ_i-λ_j)) · cellFactor(ϖ^λ) = localTerm q_v a b s λ`.
  `partialEulerFactor_eq` writes `L(s, Π̃_v × Π̃'_v)` as
  `(∏_(i,j)(1 - a_i b_j q_v^(-s)))⁻¹`. `residueCardinality_canonical` is `q_v = N(v)`, and
  `mem_ofTuple` is the membership of the tuple entries in the Satake multiset.
- `setIntegral_cons_eq` (the one-place step): for `S ⊆ A`, `v ∉ A` and `L` the sum of the
  local terms at `v`,
  `∫_(U_(A∪{v})) Ψ̃-integrand = L · ∫_(U_A) Ψ̃-integrand`.

## Proof

Fix the data of the target statement. `UnequalUnfoldingStatement` gives `C` with the dual
integral absolutely convergent at `1 - s'` for `Re s' < -C`, that is, at `s` for
`Re s > 1 + C`. `exists_partialEulerFactor_convergence` gives `σ_E` for the Euler product
of the contragredient pair. The Satake bounds of `Pd` and `Pd'`
(`exists_hasSatakeBound_presentation`) give exponents `A`, `B`, and
`exists_hasSum_localTerm` gives a `σ_C` uniform in the place. Take
`σ = max(1 + C, σ_E, σ_C)`.

For `x`, `x'` spherical outside `S` and `Re s > σ`, apply
`ContragredientDualWhittakerStatement` twice. With `ψ` it gives `x̃ ∈ Td` with
`W_(x̃)^(ψ⁻¹) = W_x^ψ(w_n ᵗ·⁻¹)`. With `ψ⁻¹` (`inverseCharacter ψ`) it gives `x̃' ∈ Td'` with
`W_(x̃')^ψ = W_(x')^(ψ⁻¹)(w_m ᵗ·⁻¹)`. Both vectors are spherical outside `S`. The first two
conclusions of the target are then the convergence statements above. For the identity,
`integral_eq_hasProd_mul_setIntegral` reduces it to the one-place step for every finite
`A ⊇ S` and `v ∉ A`, with factor `L(s, Π̃_v × Π̃'_v)`.

One-place step. `FiniteAdditiveSupport` gives the component `ψ_v` of conductor `𝒪_v`.
`ofTuple_surjective` gives Satake tuples `a`, `b` of `Pd`, `Pd'` at `v`. Apply
`WhittakerCellDecompositionStatement` to the integrable dual integrand at `v` and
`ϖ = placeUniformizer v`. On the classes in `U_A` the representative satisfies
`g_v ∈ N(F_v) GL(𝒪_v)`, and there the cell property gives
`f(N ι_v(ϖ^λ) g) = cellFactor(ϖ^λ) f(N g)`. Hence the `λ`-term of the cell decomposition is
`localTerm q_v a b s λ · ∫_(U_A) f`. `exists_hasSum_localTerm` sums the local terms to
`(∏(1 - a_i b_j q_v^(-s)))⁻¹ = L(s, Π̃_v × Π̃'_v)`, and uniqueness of sums gives the step.

Cell property. Write `g_v = u k` with `u` upper unitriangular and `k ∈ GL_(t+1)(𝒪_v)`, and
`g = ι_v(u) g₁`, so `(g₁)_v = k`. Then
`ι_v(ϖ^λ) g = ι_v(ϖ^λ u ϖ^(-λ)) ι_v(ϖ^λ) g₁`. Both `ι_v(u)` and `ι_v(ϖ^λ u ϖ^(-λ))` lie in
`N_(t+1)(𝔸)`, and the dual kernel is left `N_(t+1)(𝔸)`-invariant
(`Unfolding.dualKernel_whittaker_unipotent_mul`). This reduces the claim to `g₁`. There,
`rect(ι_v(P) g₁, y) = pad(ι_v(P)) rect(g₁, y) = ι_v(diag(P, I)) rect(g₁, y)`. The
`v`-component of `rect(g₁, y) w` is `rectGL h k y_v · w_v` with `k` and `w_v` integral. By
`apply_localPoint_mul_of_split` and `sphericalWhittaker_inverseStandard_rectGL_zero_mul`,
`W̃(ι_v(diag(P, I)) rect(g₁, y) w) = sphInv(diag(P, I)) · W̃(rect(g₁, y) w)` for every `y`. This
holds pointwise in `y`, so it passes through the inner integral over `M_(r-t-1, t+1)(𝔸)`
without any integrability hypothesis. The factor `W̃'(ι_v(P) g₁) = sphStd(P) W̃'(g₁)` is
the same argument without the rectangular block, and `|det|` is multiplicative
(`detPower_localPoint_mul`).

## Provenance

The reduction is the author's formulation of the proof of Cogdell 2004, §4.1, printed
p.220 (J. W. Cogdell, *Analytic theory of L-functions for GL_n*, registered as
`cogdell-2004-analytic-theory-gln`, PDF page = printed page + 3): the dual global integral
`Ĩ(1-s; φ̃, φ̃')` factors as the product over `v ∈ S` of the dual local integrals times
`L^S(1-s, π̃ × π̃')`. Cogdell gets the unramified dual factor from the local functional
equation (p.220, with Theorems 3.2–3.3, pp.214–215). Here it is computed directly from
Shintani's formula (p.206), the cell decomposition `dh = dn δ_B⁻¹(ϖ^J) dk` (Cogdell, Fields
lectures 2003, Lecture 7 §3, p.57), the local unramified sum (Theorem 3.3, p.215) and the
support lemma of `RectangularSupport`. The direct computation is a deviation in route,
not in statement. The decomposition into the four premises is internal.
