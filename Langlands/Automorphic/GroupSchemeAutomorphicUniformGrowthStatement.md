# Every actual adelic automorphic form has uniformly moderate growth

`AdelicAutomorphicUniformGrowthStatement` is a target proposition for proof. It is
universally quantified over the following data:

- a number field `F` (in an arbitrary universe) and an affine group scheme `G`
  over `F`, smooth of relative dimension `d` (`hsmooth`);
- a subgroup `Kinf` of the infinite adelic points `InfiniteAdelicGroupPoints F G`;
- a matrix representation `rho : GroupScheme.MatrixRepresentation G (Fin N)`.

It assumes that `G` is connected reductive (`GroupScheme.IsConnectedReductive G`),
that `rho` is a closed subgroup embedding (`GroupScheme.IsClosedSubgroup rho`), that
`Kinf` is a maximal compact subgroup (`CompactIwasawa.IsMaximalCompact Kinf`) and
that `0 < N`. For every original finite plot-smooth rational function `f` it then
asserts:

if `f` satisfies the published form conditions `IsAdelicAutomorphicForm F G Kinf rho
hsmooth hcalc f`, then `f` satisfies `HasAdelicUniformModerateGrowth F G rho hsmooth
hcalc f`.

Here `hcalc` is the published proof `adelicDifferentialCommutator_of_smooth F G
hsmooth`. The form conditions are the published conjunction of three conditions:

- `Kinf`-finiteness under right translation (`IsAdelicInfiniteFinite`);
- finiteness under the centre of the actual enveloping algebra (`IsAdelicCenterFinite`);
- moderate growth of `f` itself for the source norm of `rho` (`HasAdelicModerateGrowth`).

Continuity, left invariance under the rational points, plot smoothness of every
infinite slice and an open stabilizer in the finite adelic points are part of the
carrier `FinitePlotSmoothRationalFunctions F G`.

The conclusion is the published one-exponent bound: there is one real `r` such that,
for every element `a` of `AdelicEnvelopingAlgebra F G hsmooth`, some positive `C`
satisfies `‖(adelicEnvelopingAction a f)(g)‖ ≤ C * ‖g‖ ^ r` at every adelic point
`g`. The norm `‖g‖` is `RepresentationGrowth.adelicSourceNorm F G rho g`, the same
norm that is used in the hypothesis. The exponent is chosen before `a`, and the
constant may depend on `a`.

## Role

The Library defines the uniform form space
`uniformAdelicAutomorphicSubrepresentation` as the intersection of the form space
`adelicAutomorphicSubrepresentation` with the uniform-growth subrepresentation.
`mem_uniformAdelicAutomorphicSubrepresentation_iff` and the published `GL_n`
realizations (`GeneralLinearUniformOperatorRealization`,
`GeneralLinearUniformCuspidalRealization`) are stated for this intersection. A proof
of this statement shows that the intersection is the whole form space, for every
connected reductive `G`. The uniform-growth hypothesis can then be dropped from those
results.

The Library also has the archimedean `GL_n` target
`Langlands.Global.ArchimedeanGL.FiniteUniformDifferentialGrowthStatement`. That
target concerns functions on the infinite adelic points of `GL_n` and keeps the given
exponent. The present statement concerns the original adelic carrier of a general
connected reductive `G`, and it only asserts that some common exponent exists.

## Original-source correspondence

Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995), registered
as `moeglin-waldspurger-1995-spectral-decomposition`, chapter file
`05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`. In this file,
printed page `p` is PDF page `p - 17`.

- I.2.3 (printed p. 25): `φ` and its derivatives have uniformly moderate growth if
  `∃ r ∈ ℝ, ∀ X ∈ 𝔘, ∃ c_X ∈ ℝ, ∀ g ∈ G, |δ(X)φ(g)| ≤ c_X ‖g‖^r`. This has the same
  quantifier order as `HasAdelicUniformModerateGrowth`. The Library asks for a
  positive constant; a positive constant can always be chosen.
- I.2.5, Lemma (a) (printed p. 27): for a smooth compactly supported `f` on `G(𝔸)`
  and `φ` of moderate growth, `δ(f)φ` and its derivatives have uniformly moderate
  growth.
- I.2.17 (printed pp. 37–39): an automorphic form has moderate growth and is smooth,
  `K`-finite and `𝔷`-finite. The lemma there (citing Harish-Chandra) gives a smooth
  compactly supported `f` with `δ(f)φ = φ`. The text then concludes: "The preceding
  lemma and Lemma I.2.5 show that for all `P` and all `φ ∈ A(U(𝔸)M(k)\G)`, `φ` and
  its derivatives have moderate growth." The statement here is the case `P = G` of
  that conclusion.

Getz–Hahn, *An Introduction to Automorphic Representations* (2024), registered as
`getz-hahn-2024-automorphic-representations`, PDF page = printed page + 14:

- Definition 6.2.1 (printed p. 159) and Definition 6.3.1 (printed pp. 161–162):
  moderate growth and uniform moderate growth, with the same quantifier order.
- Theorem 6.2.4 and Corollary 6.2.5 (printed p. 160): the archimedean version, with
  Harish-Chandra's theorem [HC66, §8, Theorem 1] and the proof sketched below.
- Definition 6.3.3 (printed p. 163): adelic automorphic forms with respect to
  `K = K_∞ K^∞`, with `K_∞` maximal compact.

The Library's form conditions differ from these sources in form only. `K`-finiteness
is split into `Kinf`-finiteness and an open stabilizer at the finite places, which is
equivalent for a compact open `K^∞`. Derivatives are taken with the published
`adelicEnvelopingAction` along the infinite slices, built from the smooth atlas
chosen from `hsmooth`. The Library does not impose GH's tensor decomposition (6.1),
which GH use to define derivatives. Left `G(F)`-invariance is part of the rational
carrier.

## Why the statement is expected to hold

Fix a form `f`. Its `Kinf`-translates span a finite-dimensional space, and one ideal
`J` of finite codimension in the centre annihilates `f` and all these translates. For
each adelic point `g`, the slice `x ↦ f(g x)` on the infinite adelic points has `Kinf`-types
in one fixed finite set and is annihilated by `J`. Harish-Chandra's theorem gives one
compactly supported smooth `α` with `R(α)φ = φ` for all these slices. Differentiating
moves each element `a` of the enveloping algebra onto `α`, so the slice derivative is
`R(α_a)` of the slice. After replacing the exponent `r` of `f` by `max r 0`, the
source norm is submultiplicative up to a constant and is bounded on the compact
support of `α_a`. This exponent therefore bounds every derivative, with a constant
depending on `a` and `f`.

## Provenance

The statement is taken from the source: it is the case `P = G` of the conclusion of
Mœglin–Waldspurger I.2.17, combined with I.2.5, and Getz–Hahn Corollary 6.2.5 is its
archimedean analogue. It is written with published Library objects only; the
differences in form are listed above. No proof is supplied here.
