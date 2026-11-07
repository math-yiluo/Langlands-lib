# The graph argument for the supercuspidal local converse theorem

This supporting module carries out Henniart's graph argument (Henniart 1993,
`henniart-1993-epsilon-pairs`, sections 3.1 and 3.2, printed pages 344-346) for
irreducible supercuspidal representations of `GL_(k+2)` over a p-adic field. It
proves two results. Both take Whittaker completeness against normalized products
of supercuspidals, the Library proposition
`SupercuspidalProductCompletenessStatement`, as an explicit hypothesis `hC`:

- `nonempty_equiv_of_sameProductGammaFactors`: two irreducible supercuspidal
  representations `π`, `π'` of `GL_(k+2)` with common gamma factors against every
  normalized product of supercuspidals of total rank `k+1`
  (`SameProductGammaFactors`) are equivalent;
- `supercuspidalLocalConverse_of_completeness`: `hC` implies the target
  proposition `SupercuspidalLocalConverseStatement` (Henniart 1993, Corollary,
  printed page 340).

The module does not prove completeness, so it does not prove the target theorem
by itself. Once `SupercuspidalProductCompletenessStatement` is proved, the target
follows by applying `supercuspidalLocalConverse_of_completeness` to that proof.

## Provenance and the route taken

In Henniart's section 3.1, `S` is the space of pairs `(W, W')` of Whittaker
functions of `π` and `π'` that agree on every `diag(g, 1)`. `S̃` is the analogous
space for the transformed functions `W̃(g) = W(w_n ᵗg⁻¹)`. Lemme 3.1 says
`(W, W') ∈ S` if and only if `(W̃, W̃') ∈ S̃`. Its proof combines the equal gamma
factors with the functional equation, and then applies the completeness lemma
(Lemme 2.1) to the coefficients `H_m` of the difference `W̃ - W̃'`. In section 3.2,
`S` is stable under the mirabolic subgroup `P` and, by Lemme 3.1, under `ᵗP`. These
two subgroups generate `GL_n`, so `S` is the graph of an isomorphism.

The Lean proof follows this outline, with three changes:

1. The tests are the normalized products of supercuspidals. These are the tests
   that `SameProductGammaFactors` and `SupercuspidalProductCompletenessStatement`
   use, and the Library's `SameSupercuspidalEpsilonFactors.productGammaFactors`
   (gamma multiplicativity) derives `SameProductGammaFactors` from the epsilon
   hypothesis. Generic irreducible tests are not used.
2. Only the forward direction of Lemme 3.1 is proved. Here `S` is the graph of a
   bijection by supercuspidal Kirillov theory (`Langlands.supercuspidalKirillov`),
   so the abstract graph lemma below needs only `S ⊆ D`. `D` is the relation for
   the dual functions, and it is the graph of a function.
3. Henniart splits the dual integral into the coefficients `H_m`. The Lean proof
   instead uses one value: for supercuspidal `π` both dual integrals are Laurent
   polynomials in `q^(-s)`. Equal rational continuations make them equal at
   `s = 1/2`, where the determinant weight is `1`. The vanishing integral is then
   the pairing of the whole restriction `g ↦ (W̃ - W̃')(diag(g, 1))` with a test
   coefficient. That restriction is a compact Whittaker test function, so `hC`
   applies to it directly.

The other lemmas are internal and derived from published Library results, as
described below. Worker 1718 wrote the module.

## Rank conventions

`Langlands.GeneralLinear (n + 1) F` is `GL_(n+1)(F)`. `WhittakerFunctions ψ n`,
`InverseWhittakerFunctions ψ n`, `glFunctionals ψ n π`, `glInverseFunctionals ψ n π`
and `mirabolic n F` all use Lean index `n` for the group `GL_(n+1)`. In the main
results `π` and `π'` act on `GL_(k+1+1)` (Lean index `k+1`, rank `k+2`). The tests
act on `GL_(k+1)` (Lean index `k`, rank `k+1`).

## Inverse-transpose closure

Let `τ` and `σ` be representations of `GL_(n+1)`, and let
`Φ : inverseTransposePullback τ ≃ σ` be an equivalence.

- `transportedDualFunctional τ σ Φ ℓt` is the functional `ℓt ∘ Φ⁻¹ ∘ σ(w)` on `σ`,
  where `w = weylLong (n + 1) F`.
- `transportedDualFunctional_apply`: its value at `σ(g) z` is the `dualFunction`
  (the composite with `g ↦ w ᵗg⁻¹`) of the coefficient `h ↦ ℓt(τ(h) Φ⁻¹ z)`,
  evaluated at `g`.
- `transportedDualFunctional_mem`: if `ℓt` is an inverse-character functional for
  `ψ.scale (-1)`, the transported functional is in `glInverseFunctionals ψ n σ`.
- `exists_secondDualFunction_eq`: every coefficient `f` of `τ` for such an `ℓt` is
  `secondDualFunction ψ n f'` for some coefficient `f'` of `σ`, with respect to a
  functional `ℓ` that is nonzero when `ℓt` is.

In the main proof `τ` is the test and `σ` the product of the inverse-transpose
pullbacks in reversed block order. The equivalence `Φ` comes from the Library's
`Parabolic.inverseTransposeProduct`. This replaces Henniart's step "when `τ` runs
through the generic irreducible representations, so does `τ^∨`".

## Kirillov consequences

These lemmas apply the published `Langlands.supercuspidalKirillov` to an
irreducible supercuspidal `π` of `GL_(r+1)` over a p-adic field with its canonical
topology.

- `glFunctionals_entrywise` restates the covariance of a standard functional
  entrywise. `unitaryAdditiveCharacter_complex_ne_one` says the complex character
  of `ψ` is nontrivial.
- `eq_of_mirabolic_coefficient_eq`: for a nonzero standard functional `ℓ`, two
  vectors whose Whittaker functions agree on `mirabolic r F` are equal (Kirillov
  injectivity).
- `exists_mirabolic_coefficient_eq`: given a second such `π'` with nonzero `ℓ'`,
  every mirabolic Whittaker function of `π` is that of some vector of `π'`
  (Kirillov transfer, since both models restrict onto the same Kirillov space).
- `exists_glFunctional_ne_zero`: `π` has a nonzero standard Whittaker functional.

## The abstract graph lemma

`nonempty_equiv_of_graph` works for any group `G` with representations `π` on `V`
and `π'` on `V'`. It needs a relation `S` that:

- is the graph of a bijection (total, functional, surjective, injective);
- is closed under addition and scalar multiplication;
- is stable under every element of a set `A`.

It also needs a relation `D` that contains `S`, is functional, and is stable under
a set `B`. If every subgroup containing `A` and `B` is `⊤`, then `π` and `π'` are
equivalent. The proof turns `S` into a linear bijection `J`. The elements `g` with
`J ∘ π(g) = π'(g) ∘ J` form a subgroup. It contains `A` by stability of `S`, and it
contains `B` because `D` is functional, `B`-stable and contains `S`.

## Gamma equation helpers

- `integral_eq_zero_of_eq_sub`: if `φ = φ₁ - φ₂` pointwise, with `φ₁` and `φ₂`
  integrable with equal integrals, then `∫ φ = 0`.
- `GammaFunctionalEquation.dual_unique`: two gamma functional equations with the
  same scalar, gamma factor and forward continuation have the same dual
  continuation. They agree at infinitely many reflected spectral points.
- `eq_of_laurent_of_rationalContinuation`: two functions with the same rational
  continuation, each everywhere equal to a Laurent polynomial in the spectral
  variable, are equal at every `s`. The proof uses `laurentToRatFunc` and
  `HasRationalContinuation.unique`.

## Restriction along `g ↦ diag(g, I)`

- `weylLong_rankOne` and `blockWeylAt_succ_self`: in corank one the block Weyl
  element `blockWeylAt n (n + 1) h` is the identity.
- `appendRestriction ψ n d` is the linear map from `WhittakerFunctions ψ (n + d)`
  to `WhittakerFunctions ψ n` given by `φ ↦ (g ↦ φ(diag(g, I_d)))`. It is a
  Whittaker function by `appendUnipotent_character`. `appendRestriction_apply` is
  its defining equation.
- `eq_on_mirabolic_of_appendIdentity`: two Whittaker functions on `GL_(n+2)` that
  agree on every `diag(g, 1)` agree on `mirabolic (n + 1) F`. Every mirabolic
  element is a radical element times `diag(g, 1)`, by
  `Mirabolic.eq_radicalElement_mul_levi`.
- `continuous_appendIdentity_one`, `appendIdentity_one_mem_mirabolic` and
  `translateWhittaker_one` are elementary facts.
- `unequalRankIntegrand_zero_congr`: the corank-one integrand
  `unequalRankIntegrand ψ abv 0 0 W W' s x` depends on `W` only through the values
  `W(diag(g, 1))`.

## The p-adic part

The field is a `PadicField` with its canonical topology, valuation and normalized
absolute value `abv`. The groups and quotients carry Borel σ-algebras, and `qF` is
the residue cardinality.

- `mirabolicTest_integrable_and_laurent`: if `φ` is a mirabolic test function
  (`IsMirabolicTestFunction`) and `φ'` is continuous, the corank-one block-zero
  integrand is integrable for every `s`. The integral against the point mass at
  the empty matrix is one Laurent polynomial in `q^(-s)`, by the Library's
  `exists_laurent_unequalRankIntegral_zero`. Integrability holds because the
  integrand is continuous and has compact support in the quotient.
- `unequalRankIntegral_blockWeylAt_succ_self` and `unequalRankIntegral_dirac_zero`:
  in corank one the dual integral involves no Weyl translation and no rectangular
  variable, and it is the quotient integral of the integrand at the zero matrix.
- `isCompactWhittakerTestFunction_appendRestriction_sub`: the restriction along
  `diag(g, 1)` of the difference of two mirabolic test functions is an
  `IsCompactWhittakerTestFunction`. The open subgroup is the preimage of the
  intersection of their invariance subgroups, and the compact set is the union of
  the compact sets given by `exists_compact_appendIdentity_support`.
- `isMirabolicTestFunction_firstDualFunction`: first dual functions of
  coefficients of an irreducible supercuspidal `π` with nonzero `ℓ` are mirabolic
  test functions for `ψ.scale (-1)`. They are coefficients of the irreducible
  supercuspidal `inverseTransposePullback π` (`firstDualFunction_coefficient`), so
  the Library's `isMirabolicTestFunction_of_supercuspidalKirillov` applies.

### Henniart's inclusion `S ⊆ D`

`integral_appendRestriction_firstDual_sub_eq_zero` is the integral form of the
forward direction of Lemme 3.1. Its hypotheses are:

- `π` and `π'` on `GL_(k+2)` are irreducible supercuspidal, with
  `SameProductGammaFactors F ψ ν k π π'`;
- `ℓ` and `ℓ'` are nonzero standard functionals;
- `ℓ(π(diag(g, 1)) v) = ℓ'(π'(diag(g, 1)) v')` for all `g` in `GL_(k+1)`.

Write `cd` and `cd'` for the first dual functions of the coefficients of `v` and
`v'`. The lemma states that the restriction of `cd - cd'` pairs to zero, under
the quotient measure `unipotentQuotientHaar F.Carrier k`, with every coefficient
`f` of every `ψ.scale (-1)` inverse-character functional `ℓt` of every normalized
product of smooth irreducible supercuspidals `τ_i` of total rank `k+1`. The proof:

1. If `ℓt = 0` the integrand vanishes.
2. Otherwise let `σ` be the product of the inverse-transpose pullbacks of the
   `τ_i` in reversed order. These pullbacks are smooth, irreducible and
   supercuspidal by `isSupercuspidal_comp_inverseTranspose` and
   `isIrreducible_comp_mulEquiv_iff`. `exists_secondDualFunction_eq` writes `f` as
   the second dual of a coefficient `f'` of `σ` for a nonzero `ℓσ`.
3. `SameProductGammaFactors` gives a common gamma factor `G` of `(π, σ)` and
   `(π', σ)`. `isPairGammaFactor_of_lt` turns it into two gamma functional
   equations for the block `j = 0`. The scalars agree by
   `HasModelMinusOneScalar.unique`.
4. The forward integrals of `(coefficient of v, f')` and
   `(coefficient of v', f')` are equal by `unequalRankIntegrand_zero_congr`. So
   the forward continuations agree (`HasRationalContinuation.unique`), and the
   dual continuations agree (`GammaFunctionalEquation.dual_unique`).
5. In corank one the dual integrals are the block-zero integrals of `cd` and `cd'`
   against `f`. `mirabolicTest_integrable_and_laurent` shows that both are Laurent
   polynomials. `eq_of_laurent_of_rationalContinuation` then makes them equal at
   `s = 1/2`, where the determinant weight is `1`.
6. `integral_eq_zero_of_eq_sub` gives the vanishing.

`firstDual_appendIdentity_eq` applies `hC` to this restriction, which is a compact
Whittaker test function, with the measure `unipotentQuotientHaar F.Carrier k` and
its compatibility `unipotentQuotientHaar_isCompatible`. It concludes that `cd` and
`cd'` agree on every `diag(g, 1)`.

### The assembly

`nonempty_equiv_of_sameProductGammaFactors` applies `nonempty_equiv_of_graph` with
these choices:

- `ℓ` and `ℓ'` are nonzero standard functionals (`exists_glFunctional_ne_zero`);
- `S v v'`: the Whittaker functions `q ↦ ℓ(π(q) v)` and `q ↦ ℓ'(π'(q) v')` agree on
  `mirabolic (k + 1)`;
- `D v v'`: the same with the first dual functionals on the inverse-transpose
  pullbacks;
- `A` is the mirabolic subgroup and `B` its image under `inverseTranspose`.

`S` is a bijective graph by the two Kirillov lemmas, and `D` is functional by
Kirillov injectivity for `inverseTransposePullback π'`. Both relations are
evidently stable under `A` and `B` respectively. `S ⊆ D` follows from
`firstDual_appendIdentity_eq`, `eq_on_mirabolic_of_appendIdentity` and
`firstDualFunction_coefficient`. `A` and `B` generate `GL_(k+2)` by the Library's
`eq_top_of_mirabolic_le_of_inverseTranspose_mem` (Henniart, section 3.2).

## The conditional target

`supercuspidalLocalConverse_of_completeness` takes
`hC : SupercuspidalProductCompletenessStatement.{uF, uW}` and proves
`SupercuspidalLocalConverseStatement.{uF, uV, uW}`. It reduces the two classes to
representatives `A` and `A'` and unfolds the epsilon hypothesis by
`sameClassEpsilonFactors_mk_iff`. It then gets `SameProductGammaFactors` from
`SameSupercuspidalEpsilonFactors.productGammaFactors`, using the published
Kirillov theorem at universes `uV` and `uW`. Next it applies
`nonempty_equiv_of_sameProductGammaFactors` and concludes with `Quotient.sound`.
The isomorphism of supercuspidal representations is built from the equivalence by
`SmoothRep.mkIso`.
