# Weighted Fréchet spaces of smooth functions of uniform moderate growth

Module `Langlands.Automorphic.GroupSchemeUniformGrowthFrechet` constructs, for
a matrix representation `rho` of `G`, a real exponent `R` and a subgroup `L`
of the finite adelic points, the space of smooth functions on `G(F) \ G(𝔸)`
that are right `L`-invariant and all of whose derivatives are bounded by a
multiple of `‖g‖^R`, where `‖g‖` is the adelic norm of `rho`. It carries the
topology of the seminorms `sup_g |(a f)(g)| ‖g‖^{-R}`, one for every element
`a` of the complex enveloping algebra. The growth predicate and the submodule
are defined for every `rho`; the topologized space requires `rho` to be a
closed embedding. It is a definition module. Besides the closure laws of the
submodule and the boundedness needed to define the weighted derivatives, it
proves nothing.

The construction is derived from the Fréchet spaces of Bernstein and Lapid
described below. It is not literally their space for a given `R`: the weight
is a power of an algebraic height instead of `e^{R‖H_0‖}` on a Siegel domain.
The section "Correspondence with the source" states the intended relation and
what it requires.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §7.1, journal
pp.210–211 (PDF pages 24–25). For `R > 0`, `𝔉^R(X)` is the Banach space of
functions on `X = G(F) \ G(𝔸)` majorized by a multiple of
`e^{R‖H_0(·)‖}` on a Siegel domain. Its smooth part `𝔉^R_smth(X)` is the
union over open subgroups `K` of `G(𝔸_f)` of the Fréchet spaces of smooth
right `K`-invariant functions `f` with `δ(X)f ∈ 𝔉^R(X)` for all `X` in the
enveloping algebra, and `𝔉_umg(X)` is the union over `R` of these. Footnote 6
on p.211 records that this notion of uniform moderate growth is equivalent to
the prevalent definition with a height function on `G(𝔸)`. Corollary 8.6
(p.226, PDF page 40) states the meromorphic continuation of Eisenstein series
in the Fréchet spaces `𝔉^R_smth(X)`, with `R` chosen locally in the parameter.
Throughout, `G` is a connected reductive group over a number field.

C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein
series* (1995), registered as `moeglin-waldspurger-1995-spectral-decomposition`,
I.2.2, printed pp.20–21. The height there is built from the fixed embedding
`i_G : G → SL_{2n}` of I.1.1. Property (iv) compares `log ‖a‖` with
`‖log_{M_0} a‖` on `A_{M_0}` up to positive factors and an additive constant,
and property (vii) bounds `‖g‖` by a multiple of `‖γ g‖` for `g` in a Siegel
domain and `γ ∈ G(F)`.

## Existing objects used

All carriers and actions are those of the existing forms on `G(F) \ G(𝔸)`:

- `FinitePlotSmoothRationalFunctions F G`: continuous left `G(F)`-invariant
  functions on `G(𝔸)` with plot-smooth infinite slices and a common open
  finite stabilizer (module `Langlands.Automorphic.GroupSchemePlotSmooth`).
  `evaluate F G` gives the underlying function.
- `adelicEnvelopingAction F G hsmooth hcalc`: the action of the complex
  enveloping algebra `AdelicEnvelopingAlgebra F G hsmooth` of the actual
  Lie algebra of `G(𝔸_∞)`, under the existing atlas `hsmooth` and commutator
  premise `hcalc` (module `Langlands.Automorphic.GroupSchemeAdelicUniformGrowth`).
- `finitePlotSmoothRightAction F G`: right translation.
- `RepresentationGrowth.adelicSourceNorm F G rho`: the exact adelic norm of
  a matrix representation `rho`, the norm of the existing
  `HasAdelicUniformModerateGrowth`. For `N > 0` it is positive
  (`adelicSourceNorm_pos`).
- `GroupScheme.IsClosedSubgroup rho` (module
  `Langlands.GroupScheme.Reductive.Basic`): the underlying morphism of
  schemes of `rho : G → GL_N` is a closed immersion, the algebraic hypothesis
  already used by `RepresentationGrowth.ClosedImmersionHeightDominationStatement`.

## Definitions

- `HasUniformGrowthExponent F G rho hsmooth hcalc R f`: for every enveloping
  element `a` there is `C` with `|(a f)(g)| ≤ C ‖g‖^R` for all `g`. The
  exponent `R` is fixed. For the same `rho`, the existing
  `HasAdelicUniformModerateGrowth` is the union of these conditions over `R`.
- `IsFixedByFiniteSubgroup F G L f`: `f` is fixed by right translation by
  every element of `L`.
- `uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L`: the submodule of
  the finite plot-smooth carrier cut out by both conditions. Its closure
  under zero, sums and scalar multiples is proved in the definition.
- `UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L`, for
  `hN : 0 < N` and `hrho : GroupScheme.IsClosedSubgroup rho`, is this
  submodule as a type, with its additive group and complex module
  structures, and `UniformGrowthFrechetSpace.toFun` gives the underlying
  function on `G(𝔸)`. The premise `hrho` is not used in the construction; it
  restricts the space to the heights of closed embeddings, for which the
  correspondence below is intended.
- `weightedDerivative … a f` is the bounded function
  `g ↦ (a f)(g) · ‖g‖^{-R}` as an element of `ℓ^∞(G(𝔸))`, Mathlib's
  `lp (fun _ => ℂ) ∞` with the supremum norm. It is bounded by the constant
  `C` of `HasUniformGrowthExponent`, since `‖g‖^R > 0`.
- The topology on `UniformGrowthFrechetSpace` is the infimum over all
  enveloping elements `a` of the topologies induced by `weightedDerivative a`.
  This is the topology of the seminorms `p_a(f) = sup_g |(a f)(g)| ‖g‖^{-R}`.

## Dependence on the representation

The growth predicate and the submodule depend on `rho` and are meaningful as
Bernstein–Lapid growth conditions only when `rho` is faithful in the algebraic
sense. For a representation that is not a closed embedding the weight can be
far too small. For the trivial one-dimensional representation `adelicSourceNorm`
is identically `1`, so the submodule consists of the functions with bounded
derivatives. For `G = G_m` over `ℚ` the idele norm `x ↦ |x|_𝔸` on
`ℚ^× \ 𝔸^×` has uniform moderate growth in the sense of BL §7.1 but lies in
none of these submodules. This is why `UniformGrowthFrechetSpace` takes the
premise `GroupScheme.IsClosedSubgroup rho`.

## Correspondence with the source

The intended relation concerns connected reductive `G`, a closed embedding
`rho`, `R > 0` and an open subgroup `L` of `G(𝔸_f)`. It is a comparison of
growth scales after a change of exponent, not an identification of spaces at
the same `R`:

- For the height of a closed embedding, MW95 I.2.2 (iv) gives positive
  factors `c ≤ c'` with `e^{c‖H_0(x)‖} ≪ ‖x‖ ≪ e^{c'‖H_0(x)‖}` on a Siegel
  domain. MW95 I.2.2 (vii) lets a bound on a Siegel domain for a left
  `G(F)`-invariant function pass to a bound on all of `G(𝔸)`. Together they
  would give, for each level `L`, inclusions of BL's `𝔉^R_smth` at level `L`
  into this space with exponent `R/c`, and of this space with exponent `R`
  into BL's `𝔉^{c'R}_smth` at level `L`. The two families are therefore
  expected to be mutually cofinal, and their unions over `R` and over open `L`
  to coincide with BL's `𝔉_umg(X)`, as footnote 6 asserts for height
  functions.
- MW's height uses entries of an embedding into `SL_{2n}`, while
  `adelicSourceNorm` is the Library's norm of the matrix and its inverse. The
  comparison of the two for a closed embedding is a further step of the same
  kind.
- In the existential statements where these spaces are used ("there is `R`",
  as in BL Corollary 8.6), the change of exponent is harmless. A statement
  about one fixed `R` does not transfer literally.
- BL take the union over open subgroups `K` of `G(𝔸_f)`; here the level `L`
  is a parameter, and statements quantify over open `L`.
- BL's seminorms are indexed by the enveloping algebra `𝒰(𝔤)`; here they are
  indexed by all elements of the existing complex enveloping algebra.

None of these comparisons is proved here; they are obligations for later
work.

## Scope

Not proved here: that the topology makes the space a Hausdorff locally convex
topological vector space, metrizability (countably many seminorms suffice),
completeness, independence of the closed embedding `rho` up to change of
exponent, the comparisons with the Siegel-domain weight and with MW's height
described above, and the topology of the union `𝔉_umg(X)`.
