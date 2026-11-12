# Rational reduction to a compact finite part with polynomial archimedean height

Author: Worker 5152.

`Langlands.Global.RepresentationGrowth.AdelicRationalHeightReductionStatement` is a
target proposition for proof. This module states it and proves nothing about it.

## The statement

The proposition is universally quantified, in universe `u`, over:

- a number field `F : Type u` and a group scheme `G` over `Spec F` whose
  underlying scheme is affine (`IsAffine G.X.left`);
- a natural number `N` and a matrix representation
  `rho : GroupScheme.MatrixRepresentation G (Fin N)`.

It assumes three things: `G` is connected reductive
(`GroupScheme.IsConnectedReductive G`), `rho` is a closed subgroup embedding
(`GroupScheme.IsClosedSubgroup rho`, a scheme-theoretic closed immersion), and
`0 < N`. These are the binders and hypotheses of
`Langlands.Automorphic.GroupSchemeFunctions.AdelicSliceModerateGrowthStatement`.

The conclusion asks for a set `Ω` of finite adelic points `G(𝔸_f)`
(`FiniteAdelicGroupPoints F G`), a real `C` and a natural number `e` with:

1. `Ω` is compact for the existing topology on `G(𝔸_f)`;
2. `0 < C`;
3. for every actual adelic point `g ∈ G(𝔸)` (`AdelicGroupPoints F G`) there is a
   rational point `q ∈ G(F)` (`RationalGroupPoints F G`) such that, with
   `x = rational(q) · g`,
   - the finite component `AdelicGroupPoints.finite F G x` lies in `Ω`;
   - the archimedean height of the infinite component is polynomially bounded:
     `height F G rho (AdelicGroupPoints.infinite F G x) ≤ C * adelicHeight F G rho g ^ e`.

`Ω`, `C` and `e` come before the point quantifier: they depend only on `F`, `G`
and `rho`. The rational point `q` may depend on `g`. The rational point acts on the
left through the principal map `AdelicGroupPoints.rational F G`.

The two heights are the existing ones.

- `RepresentationGrowth.height F G rho a` (module `RepresentationGrowth`) is the
  archimedean matrix-and-inverse height `ArchimedeanGL.matrixHeight` of
  `rho(a)` for an infinite adelic point `a`. It is the height used in the slice
  condition `GroupSchemeFunctions.HasPolynomialGrowth`.
- `RepresentationGrowth.adelicHeight F G rho g` (module
  `AdelicRepresentationHeight`) is the full local-product height of `rho(g)`. At
  each place it takes the maximum over the entries of the matrix and its inverse,
  and every infinite-place factor is scaled by `N`. It is a fixed positive multiple
  of `adelicSourceNorm F G rho g`, it is at least `1` when `0 < N`, and it is
  submultiplicative and invariant under inversion.

Since `adelicHeight` is a fixed multiple of `adelicSourceNorm`, which is bounded
below by a positive constant, a natural exponent of `adelicHeight` and a real
exponent of `adelicSourceNorm` give equivalent conditions. The proof of
`hasAdelicModerateGrowth_iff` uses the same comparison.

## Meaning

The statement packages two classical facts of reduction theory in one quantitative
form.

- **Finiteness at the finite places.** `G(F) · (G(𝔸_∞) × Ω) = G(𝔸)`. For any open
  subgroup `L ⊆ G(𝔸_f)`, the compact `Ω` is covered by finitely many cosets
  `b_j L`, so `G(F) \ G(𝔸_f) / L` is finite. This is Borel's finiteness of class
  numbers.
- **Polynomial height control.** The rational translate can be chosen so that its
  archimedean height is at most a power of the height of the original point. This
  is the content of Mœglin–Waldspurger I.2.2 (vii) on a Siegel set.

The statement is weaker than a Siegel covering. It names no parabolic subgroup,
torus, compact subgroup or chamber, and it controls only the archimedean height of
the translate, not its position in a Siegel set.

## Why the statement is expected to hold

The argument uses Mœglin–Waldspurger I.2.1 and I.2.2. Write `‖·‖` for the full
adelic height.

1. **Central decomposition.** Write `g = z g₁`. Here `z` lies in the positive part
   `A_G` of the maximal central split torus, which has trivial finite component, and
   `g₁ ∈ G(𝔸)¹`. The Library constructs this factorization in module
   `AdelicNormOneDecomposition`. The factor `z` is determined by the idelic norms
   `|χ(g)|` of the rational characters `χ` of `G`. Each `χ` is a polynomial in the
   entries of `rho(g)` and `rho(g)⁻¹` because `rho` is a closed embedding. So
   `‖z‖ ≤ c ‖g‖^k`, and then `‖g₁‖ ≤ ‖z‖ ‖g‖ ≤ c ‖g‖^{k+1}`.
2. **Siegel covering (MW I.2.1).** There is a Siegel set `S = ω A(t₀) K` with
   `G(F) S ⊇ G(𝔸)¹`, where `A(t₀)` is the chamber part of the positive points of the
   derived split torus. So `g₁ = γ⁻¹ s` with `γ ∈ G(F)` and `s ∈ S`. MW's Siegel sets
   use all of `A_{M₀}` and cover `G(𝔸)` itself. The Library states the covering of
   the norm-one group as `AdelicSiegelFactors.AdelicSiegelReductionStatement`
   (module `AdelicSiegelReductionStatement`), which is not yet proved. That is why
   the central factor is split off first.
3. **Compact finite part.** `ω` and `K` are compact and `A_{M₀}(t₀)` has trivial
   finite component. So the finite components of the points of `S` lie in one
   compact set `Ω`. Since `z` is archimedean, `(γ g)_f = s_f ∈ Ω`.
4. **Norm minimality (MW I.2.2 (vii)).** There is `c` with `‖s‖ ≤ c ‖γ' s‖` for all
   `s ∈ S` and `γ' ∈ G(F)`. MW prove this for their fixed embedding into `SL_{2n}`.
   The proof (printed p. 21) moves the compact factors aside and conjugates the image
   of the split torus to the diagonal torus by an inner automorphism of `GL_n`. It is
   then reduced to the `GL_n` inequality `‖a‖ ≤ ‖γ a‖` for diagonal `a` in the
   positive torus and rational `γ`, which MW prove with the Bruhat decomposition and
   the product formula. The product formula applied to one nonzero entry in each
   column of `γ a`, and in each row of `(γ a)⁻¹`, gives the same inequality. For
   `rho` the same argument gives `‖s‖ ≤ c ‖γ' s‖`, the constant absorbing the
   compact factors, and hence `‖s‖ ≤ c ‖g₁‖`.
5. **Archimedean height.** Every finite-place factor of `‖·‖` is at least `1`, and
   the archimedean matrix height is bounded by a power of the archimedean factors.
   Submultiplicativity then gives
   `height((γg)_∞) ≤ height(z_∞) height(s_∞) ≤ C ‖g‖^e`.

So the statement follows from the Siegel covering, the norm-one decomposition with
the bound of step 1, and the elementary minimality estimate of step 4.

The hypotheses are used as follows. Reductivity gives the Siegel covering, and
`0 < N` keeps the heights at least `1`. The closed embedding gives two things. The
rational characters are polynomial in `rho`, as step 1 requires. The height of
`rho` also dominates every other algebraic height
(`ClosedImmersionAdelicHeightDominationStatement`, module
`AdelicRepresentationHeightDominationStatement`).

## Use

`Langlands.Automorphic.GroupSchemeFunctions.adelicSliceModerateGrowthStatement_of_rationalHeightReduction`
(module `Langlands.Automorphic.GroupSchemeSliceAdelicGrowthReduction`) proves that
this statement implies `AdelicSliceModerateGrowthStatement`. Slice-wise polynomial
growth at finite level gives full adelic moderate growth.

## Original-source correspondence

Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
registered as `moeglin-waldspurger-1995-spectral-decomposition`, chapter file
`05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`. In this file, printed
page `p` is PDF page `p - 17`.

- I.2.1 (printed p. 20, PDF p. 3): Siegel sets `S = {p a k : p ∈ ω, a ∈ A_{M₀}(t₀),
  k ∈ K}` with `ω ⊂ P₀` compact. For `ω` big enough and `t₀` small enough,
  `G(k) S = G`. MW's `G` is `G(𝔸)` or a finite central covering of it (I.1.2,
  printed p. 2). Since `A_{M₀}` contains the central `A_G` and the chamber condition
  involves only simple roots, `S` covers all of `G(𝔸)`.
- I.2.2 (printed pp. 20–21, PDF pp. 3–4): the height `‖g‖ = ∏_v sup_{r,s} |g_{rs}|_v`
  through the embedding `i_G : G → SL_{2n}`. Properties (i) (lower bound), (ii)
  (submultiplicativity) and (vii) (`‖g‖ ≤ c ‖γ g‖` for `γ ∈ G(k)` and `g ∈ S`), with
  the proof of (vii) on printed p. 21.

## Provenance

The statement is derived; neither source states it in this form. It combines
MW I.2.1 and I.2.2 (vii) with the central decomposition. It is expressed with the
Library's actual point groups, principal rational map, finite and infinite
projections and existing heights. Three things differ from MW:

- the height is the Library's `adelicHeight` of the given closed `rho`, not MW's
  height for an embedding into `SL_{2n}`;
- the bound is polynomial (`C ‖g‖^e`) rather than linear;
- the conclusion keeps only the compactness of the finite parts and the height bound,
  not membership in a Siegel set.

These changes weaken the conclusion and make it independent of a choice of Siegel
data. It is exactly the input needed for the slice-to-global growth comparison.
