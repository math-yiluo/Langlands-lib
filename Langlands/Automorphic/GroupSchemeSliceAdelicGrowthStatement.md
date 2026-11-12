# Slice-wise polynomial growth at finite level gives full adelic moderate growth

`AdelicSliceModerateGrowthStatement` is a target proposition for proof. It is
universally quantified over the following data:

- a number field `F` (in an arbitrary universe) and an affine group scheme `G`
  over `F`;
- a natural number `N` and a matrix representation
  `rho : GroupScheme.MatrixRepresentation G (Fin N)`.

It assumes that `G` is connected reductive (`GroupScheme.IsConnectedReductive G`),
that `rho` is a closed subgroup embedding (`GroupScheme.IsClosedSubgroup rho`) and
that `0 < N`. For every `f : ContinuousRationalFunctions F G` (a continuous function
on the adelic points `G(𝔸)`, left invariant under the rational points) it then
asserts:

if `f` lies in `finiteSmoothSubrepresentation F G` and satisfies the slice-wise
condition `GroupSchemeFunctions.HasPolynomialGrowth F G rho f`, then `f` satisfies
`HasAdelicModerateGrowth F G rho f`.

The three conditions mean the following.

- `f ∈ (finiteSmoothSubrepresentation F G).toSubmodule`: some open subgroup `L` of
  the finite adelic points `G(𝔸_f)` fixes `f` under right translation, that is
  `f(x l) = f(x)` for all `x ∈ G(𝔸)` and `l ∈ L`.
- `GroupSchemeFunctions.HasPolynomialGrowth F G rho f` (module
  `GroupSchemeGrowth`): for every finite adelic point `b`, the infinite slice
  `a ↦ f(pair a b)` on the infinite adelic points satisfies
  `RepresentationGrowth.HasPolynomialGrowth F G rho`. So there are `C_b ≥ 0` and a
  natural number `d_b` with `‖f(pair a b)‖ ≤ C_b * height(a)^(d_b)` for all `a`.
  Here `height` is `RepresentationGrowth.height F G rho`, the archimedean matrix
  height of `rho(a)`. The constant and the exponent may depend on `b`.
- `HasAdelicModerateGrowth F G rho f` (module `GroupSchemeAdelicGrowth`): there are
  `C > 0` and a real `r` with `‖f(g)‖ ≤ C * ‖g‖^r` for every adelic point `g`. Here
  `‖g‖` is `RepresentationGrowth.adelicSourceNorm F G rho g`, the product over all
  places of the local matrix-and-inverse maxima of `rho(g)`. One constant and one
  exponent serve all of `G(𝔸)`.

The statement does not assume smoothness of the slices, finiteness under a maximal
compact subgroup or under the centre of the enveloping algebra. Its proof does not
need them.

## Relation to published results

The converse implication is published without any hypothesis on `G` or `rho`
beyond `0 < N`: `HasAdelicModerateGrowth.polynomialGrowth` in module
`GroupSchemeAdelicSliceGrowth` shows that full adelic moderate growth gives
polynomial growth on every infinite slice. The Markdown of that module records that
the present direction is not proved there. Under the hypotheses above, a proof of
this statement and the published converse together show that, for functions with an
open finite-level stabilizer, the slice-wise condition and the full adelic
condition coincide.

The slice-wise condition does not depend on the closed embedding:
`polynomialGrowthSubrepresentation_eq_of_closedImmersions` (module
`GroupSchemeGrowthIndependence`) proves this. The published Markdown of `GroupSchemeAdelicGrowth`
records that the corresponding independence of the full adelic condition is a
separate assertion; this statement does not claim it.

## Role

[The reductive quotient measure coverage note](../../notes/automorphic/l1-reductive-quotient-measure-coverage.md),
section 5, item 8, names the slice-to-global moderate-growth comparison. The published `GL_n` realization maps (modules
`GeneralLinearUniformCuspidalRealization` and
`GeneralLinearCanonicalUniformComparison`) assume a containment hypothesis. An
original matrix automorphic form is bounded on each finite slice separately, while
an actual form has one bound on all of `G(𝔸)`.
`isAdelicAutomorphicForm_iff_generalLinear_and_adelicGrowth` (module
`GeneralLinearAdelicForms`) therefore keeps `HasAdelicModerateGrowth` as an extra
condition on the matrix side.

The present statement is that missing comparison for a general connected reductive
group. It applies to the `GL_n` group scheme for `0 < n`:
`Langlands.GroupScheme.isConnectedReductive_generalLinear` gives the reductivity
hypothesis. The standard representation is a closed
embedding; it is the identity morphism. The original matrix slice growth transfers to
`GroupSchemeFunctions.HasPolynomialGrowth` for any closed embedding by
`continuousGeneralLinearEquiv_mem_polynomialGrowth_of_closedImmersion` (module
`GeneralLinearGrowthIndependence`). Removing the containment hypothesis from the
`GL_n` maps would also need a proof of `AdelicAutomorphicUniformGrowthStatement`
and a separate derivation. Neither is part of this statement.

## Original-source correspondence

Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995), registered
as `moeglin-waldspurger-1995-spectral-decomposition`, chapter file
`05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`. In this file,
printed page `p` is PDF page `p - 17`.

- I.2.1 (printed p. 20): Siegel sets `S = {p a k : p ∈ ω, a ∈ A_{M_0}(t_0), k ∈ K}`
  with `ω ⊂ P_0` compact. For `ω` big enough and `t_0` small enough, `G(k) S = G`.
- I.2.2 (printed pp. 20–21): the height `‖g‖ = ∏_v sup_{r,s} |g_{rs}|_v` of `G(𝔸)`
  for a fixed embedding into `SL_{2n}`. Property (vii): there is `c > 0` such that
  `‖g‖ ≤ c ‖γ g‖` for all `γ ∈ G(k)` and `g ∈ S`. The proof is given on printed
  p. 21.
- I.2.3 (printed p. 25): `φ` has moderate growth if there are `c, r ∈ ℝ` with
  `|φ(g)| ≤ c ‖g‖^r` for all `g`. This is the quantifier form of
  `HasAdelicModerateGrowth`.

Getz–Hahn, *An Introduction to Automorphic Representations* (2024), registered as
`getz-hahn-2024-automorphic-representations`, PDF page = printed page + 14:

- Definition 6.3.1 (printed pp. 161–162): adelic moderate growth, with the same
  quantifier form.
- Lemma 6.3.2 (printed p. 162, citing [Bor07, §5.4]): a function on `[G]` has
  moderate growth if and only if it satisfies a power bound in the torus coordinate on
  every Siegel set.
- Proof of Theorem 6.3.4, display (6.17) (printed pp. 164–165): for a compact open
  `K^∞ ≤ G(𝔸_f)` and representatives `t_1, …, t_h` of the finite set
  `G(F)\G(𝔸_f)/K^∞`, restriction to the slices `x ↦ φ(x t_i)` identifies the
  `K^∞`-fixed adelic forms with a sum of classical forms on `Γ_i(K^∞)\G(F_∞)`.
  The present statement is the growth half of this identification in one direction:
  slice-wise growth gives adelic growth. Getz–Hahn do not give a separate proof of
  that growth comparison.

## Why the statement is expected to hold

Let `L` be an open subgroup of `G(𝔸_f)` fixing `f`. By MW I.2.1 there is a Siegel set
`S` with `G(F) S = G(𝔸)`. The finite components of the points of `S` lie in a
compact set: `ω` and `K` are compact, and the torus part `A_{M_0}(t_0)` has trivial
finite component. Finitely many cosets `b_1 L, …, b_m L` cover that compact set.

Let `g ∈ G(𝔸)`. Write `g = γ s` with `γ ∈ G(F)` and `s ∈ S`, and write the finite
component of `s` as `b_j l` with `l ∈ L`. Rational invariance and `L`-invariance give
`f(g) = f(s) = f(pair s_∞ b_j)`. The slice hypothesis at `b_j` gives
`‖f(g)‖ ≤ C_j height(s_∞)^(d_j)`. Each finite-place factor of the source norm is at
least `1`, and the archimedean matrix height is bounded by a constant multiple of
the archimedean part of the source norm. So `height(s_∞)` is at most a constant
times `‖s‖`. Property (vii) of MW I.2.2 gives `‖s‖ ≤ c ‖γ s‖ = c ‖g‖`. Since
`height ≥ 1` (`RepresentationGrowth.one_le_height`) and the source norm is bounded
below by a positive constant when `0 < N`, the finitely many bounds combine into one
bound `C ‖g‖^r`, with `r` determined by `max_j d_j` and the exponent of the norm
comparison below.

MW use their own fixed embedding into `SL_{2n}`. The heights of two closed
embeddings bound each other polynomially, so property (vii) holds for
`adelicSourceNorm` in the weaker form `‖s‖ ≤ c ‖γ s‖^e` with some `e > 0`. A
polynomial bound of that kind suffices for the argument above. Reductivity is used
for the Siegel-set covering. The closed-embedding hypothesis makes
`adelicSourceNorm` a height in the sense of MW I.2.2, which the comparison of
heights uses.

The Library has the Siegel-covering target
`Langlands.Global.AdelicSiegelFactors.AdelicSiegelReductionStatement`, stated for the
norm-one subgroup. No Library statement records property (vii) of MW I.2.2.

## Provenance

The statement is derived; neither source states it as a separate result. It is the
growth half of the slice identification (6.17) of Getz–Hahn. Its proof is the
standard argument from MW I.2.1, I.2.2 (vii) and the definition I.2.3, equivalently
the Siegel-set criterion GH Lemma 6.3.2. The objects are the published Library
carrier, finite-level subrepresentation and growth predicates; the differences in
the norm are explained above. No proof is supplied here.
