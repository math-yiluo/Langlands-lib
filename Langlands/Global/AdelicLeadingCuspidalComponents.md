# Cuspidal exponents and leading cuspidal components

Module `Langlands.Global.AdelicLeadingCuspidalComponents`. Author: Worker 763.

This module defines the objects of Bernstein–Lapid, *On the meromorphic
continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), §§6.1–6.3,
printed pp. 199–203 (`bernstein-lapid-2024-meromorphic-continuation-eisenstein`).
They are defined for the actual number-field adelic points, automorphic
functions, characters, constant terms and measures of the Library. The data are:

- the left action of the positive real split component `𝔄_P`, unnormalized and
  normalized (6.2);
- generalized exponents (6.3), (6.10);
- the leading condition `Re λ ∈ 𝔞*_{0,+}`;
- constant terms and cuspidality on `U(𝔸) M(F) \ G(𝔸)`;
- the cuspidal projection characterized by (6.8);
- cuspidal components, cuspidal exponents and leading cuspidal components;
- the maps `𝓛` (6.11a) and `𝓛_P` (6.11b).

The comparisons with the source hold on the source's domain. The height comes
from a faithful closed matrix embedding and `K_∞` is in good position (§5,
"Source data"). The polynomial exponent condition is the generalized-eigenspace
condition for functions with smooth orbit maps (§3).

The task contract calls these subsections §§6.1–6.2. In the published paper
they are §6.2, "Cuspidal exponents" (pp. 200–202), and §6.3, "Leading cuspidal
components" (p. 203). In the arXiv TeX file `1911.02342.tex` they are the
subsections `Cuspidal exponents` and `Leading cuspidal components`, lines
1187–1383. The underlying theory of exponents and cuspidal projection is
Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
I.3.1–I.3.5, printed pp. 40–48 (`moeglin-waldspurger-1995-spectral-decomposition`).

The module makes definitions and proves a few comparison lemmas. It proves no
existence, uniqueness or finiteness theorem. Where the source defines a linear
map whose well-definedness is a theorem (the cuspidal projection `φ ↦ φ^cusp`,
the decompositions (6.3), (6.6) and (6.10), the projections `p^ld_P`), the module
defines a *relation* between an input and a candidate output. Later proofs of
the decomposition and of Theorem 6.3 have to show that the relations are
functional.

## 1. The family of standard parabolics

`StandardParabolicFamily F G` is supplied data for a group scheme `G` over a
number field `F`. Its parameters are instances `[IsAffineHom G.X.hom]`,
`[IsAffine G.X.left]` and `[LocallyOfFiniteType G.X.hom]`. Its fields are:

- `connectedReductive`: `G` is connected reductive;
- a commutative group scheme `T`, a map `i : T → G` with `maximalSplit :
  IsMaximalSplitTorus i`, and a cocharacter `ν` with `generic :
  IsGenericCocharacter i ν`. This is BL's `S_0` together with the minimal
  parabolic `P_0`, the dynamic parabolic of `ν`;
- `coroots : RelativeRootReflectionData i`, the integral coroots `α^∨` of the
  relative roots of `T` (with reflection representatives);
- for every index `J` (below), group schemes `P J`, `M J`, `U J`, a split torus
  `A J`, and maps `p J : P J → G`, `iU J : U J → P J`, `l J : M J → P J`,
  `a J : A J → M J`, `f J : A J → T`, `torus J : T → M J`;
- `isCompatible J`: the presentation data `⟨T, i, ν, J, f J⟩` are compatible with
  `(p J, l J, a J)` in the sense of the published
  `ParabolicRootPresentationData.IsCompatible`. Thus `p J` is a parabolic with
  image `standardParabolic i ν J`, `l J` is a rational Levi factor with image
  `standardLevi i ν J`, and `a J` is a split component (the maximal central split
  torus `S_M` of BL §6.1) factoring through `T` by `f J`;
- `isUnipotentRadical J`: `iU J` is the geometric unipotent radical of `P J`;
- `torus_comp J : torus J ≫ l J ≫ p J = i`. This records `S_0 ⊂ M_0 ⊂ M_J`
  as an actual factorization. Because `l J ≫ p J` is a monomorphism, `torus J`
  is determined by `i`;
- `leviDim J` and `leviSmooth J : SmoothOfRelativeDimension (leviDim J) (M J).X.hom`,
  the smooth structure used to define automorphic forms on `M J`;
- the regularity facts `affineP`, `finiteTypeP`, `affineM`, `finiteTypeM`,
  `affineU` and `closedU` (`iU J ≫ p J` is a closed immersion). These hold for
  the standard objects. They are recorded as fields so that the published
  constant-term and Haar-measure constructions apply as instances.

The index type is `StandardIndex F G i ν = {J // J ⊆ simpleRelativeRoots i ν}`.
`J` is the set `Δ_0^P` of simple roots of `S_0` in `M_P`. Standard parabolics
correspond bijectively to these subsets. The order on indices is inclusion of
the sets `J`. `le_iff_range_le` proves that `Q ≤ P` holds exactly when the actual
parabolic subgroup functor of `Q` is contained in that of `P`. It uses the
published `standardParabolicOrder` and the field `parabolic_eq`. So `Q ≤ P` and
`Q < P` are BL's `Q ⊂ P` and `Q ⊊ P`. `top` is the index `J = Δ_0`, the
parabolic `G` itself, and `le_top` says that every index is below it.

## 2. The split component `𝔄_P` and its actions (§6.2, (6.2))

BL set `𝔄_0 = S_0(ℝ)^0`, embedded in `S_0(𝔸)` through
`ℝ ⊂ 𝔸_ℚ ⊂ 𝔸_ℚ ⊗ F = 𝔸_F`, and `𝔄_P = 𝔄_0 ∩ S_M(𝔸)`. For the split torus
`S_M = A J` this is the group of points of `A J` all of whose coordinates are
equal positive reals at every infinite place and `1` at every finite place.
`positiveSplitComponent J` is the image in `P(𝔸)` of
`PositiveRealTorus.intrinsicSubgroup F (A J)`, through `a J ≫ l J`, written
with the published `PositiveRealTorus.imageSubgroup`. The intrinsic subgroup
consists of the adelic points whose every character value is such a positive
scalar idele. The published `PositiveRealTorusIntrinsic` proves that, for a
split torus, it is exactly the coordinate positive subgroup above.

- `unnormalizedAction J x φ` is `g ↦ φ(p(x) g)`, for `x ∈ P(𝔸)` and a function
  `φ` on `G(𝔸)`, where `p(x)` is the image of `x` under the adelic point map of
  `p J`. `unnormalizedAction_mul` gives `x * y ↦` "first `x`, then `y`".
- `positiveSplitComponent_mul_comm`: `𝔄_P` is commutative, because it is the
  image of the point group of the commutative group scheme `A J`. So the left
  translations form a representation, `splitComponentRepresentation J` of
  `𝔄_P` on `G(𝔸) → ℂ`. This is BL's "left action of `𝔄_P` on `𝒜_P`" on all
  functions. It preserves left `U(𝔸) M(F)`-invariance, because `𝔄_P` is central
  in `M(𝔸)` and normalizes `U(𝔸)`; this is not proved or used here.
- `halfModulus J x = x^{ρ_P}`. Here `ρ_P` is the published
  `halfModulusParameter F (P J) = ½ ⊗ det(Ad | Lie P) ∈ X^*(P) ⊗ ℂ`, which is BL's
  definition: "the determinant of the adjoint representation of `P` on its Lie
  algebra is an element of `X^*(P)`, which we write as `2ρ_P`" (p. 201). The
  power `x^λ` is the published `parameterPower F P λ x =
  exp ⟨λ, H_P(x)⟩`, with `H_P = characterLog F P` the normalized
  logarithmic map `e^{⟨χ, H_P(x)⟩} = |χ(x)|` of BL §2.1.
- `normalizedAction J x φ` is `g ↦ x^{-ρ_P} φ(p(x) g)`. This is BL (6.2),
  `a·φ(g) = δ_P(a)^{-1/2} φ(a g)`, with `δ_P(a)^{1/2} = a^{ρ_P}`.
  `normalizedSplitComponentRepresentation J` is the corresponding
  representation of `𝔄_P`. Its multiplicativity uses `parameterPower_mul`
  (the character `x ↦ x^λ` is multiplicative) and commutativity.
- `halfModulus_eq_sqrt` proves that `x^{ρ_P}` is the square root of the
  normalized idele norm of `det(Ad(x) | Lie P)`.
  `halfModulus_eq_sqrt_modularCharacter` combines this with the published
  `adelicModularCharacterAdjointDeterminant`. When `P J` is connected, `x^{ρ_P}`
  is the square root of Mathlib's modular character of the locally compact
  group `P(𝔸)`. Smoothness comes from `isCompatible`; connectedness is a
  hypothesis of the lemma. So the normalization is the square root of the
  actual parabolic modulus.

## 3. Generalized exponents ((6.3), (6.10))

The parameters are `λ ∈ ComplexCharacterParameter F (P J) = X^*(P) ⊗ ℂ`, BL's
`𝔛_P`. In the number field case restriction to `𝔄_P` identifies `𝔛_P` with the
quasi-character group `𝔛̃_P` of `𝔄_P` ((6.1) is an isomorphism, p. 201). So
these parameters are exactly the possible exponents.

`polynomialFunctions V n` is the complex span of the functions
`v ↦ ℓ_1(v) ⋯ ℓ_k(v)` with `k ≤ n` and `ℓ_j` real-linear forms on the real
vector space `V`. On a finite-dimensional space these are exactly the
complex polynomial functions of degree at most `n`. The constant `1` is the
case `k = 0`. It is used with `V = RealCharacterDual F (P J) = Hom(X^*(P), ℝ)`,
which is BL's `𝔞_P`.

- `HasUnnormalizedExponent J λ φ`: there is `n` such that for every `g ∈ G(𝔸)`
  there is a polynomial `Q` of degree at most `n` on `𝔞_P` with
  `φ(p(x) g) · x^{-λ} = Q(H_P(x))` for all `x ∈ 𝔄_P`. This is the polynomial
  description of `𝒜^{un}_{P,λ}` for the unnormalized action, (6.10). For
  functions with smooth orbit maps it is membership in that generalized
  eigenspace (see below).
- `HasExponent J λ φ`: the same with the normalized action `(x·φ)(g)` in place
  of `φ(p(x) g)`. In the same sense this is membership in `𝒜_{P,λ}`, (6.3).
- `hasExponent_iff` proves `HasExponent J λ φ ↔ HasUnnormalizedExponent J
  (λ + ρ_P) φ`. This is BL's `𝒜_{P,λ} = 𝒜^{un}_{P,λ+ρ_P}` (p. 203). The proof
  is `x^{-ρ_P} x^{-λ} = x^{-(λ+ρ_P)}` (`parameterPower_add`).

BL define `𝒜_{P,λ}` as the `λ`-generalized eigenspace of the twisted
`𝔄_P`-action on the space `𝒜_P` of automorphic forms. They state the polynomial
description as a consequence: "Thus, for every
`φ ∈ 𝒜_{P,λ}` there exists `n ≥ 0` such that for every `g ∈ G(𝔸)` the function
`a ↦ (a·φ)(g) a^{-λ}` is a polynomial in `H_P(a) ∈ 𝔞_P` of degree `≤ n`" (p. 201).
The module uses this polynomial description as the definition. It agrees with
the generalized-eigenspace condition on the source's smooth forms. It does not
agree for arbitrary functions. The comparison is explanation only and is not
proved in Lean.

- Let `π` be either action of `𝔄_P`. Fix `g` and let `F_g` be the function on
  `𝔞_P` with `F_g(H_P(a)) = (π(a)φ)(g) a^{-λ}`. This is well defined because
  `H_P` restricted to `𝔄_P` is an isomorphism onto `𝔞_P` (p. 201). For
  `b ∈ 𝔄_P`, the function attached to `(π(b) − b^λ)φ` at `g` is `b^λ` times
  the finite difference `F_g(· + H_P(b)) − F_g`.
- The generalized-eigenspace condition is: there is `n` such that
  `∏_{j=1}^{n+1} (π(a_j) − a_j^λ) φ = 0` for all `a_1, …, a_{n+1} ∈ 𝔄_P`. By
  the previous point it says that, for every `g`, every product of `n+1` finite
  differences annihilates `F_g`.
- A polynomial of degree `≤ n` is annihilated by every product of `n+1` finite
  differences. So `HasExponent` implies the generalized-eigenspace condition
  for every function, and likewise `HasUnnormalizedExponent` for the
  unnormalized action.
- Conversely, suppose every `F_g` is smooth. Take a basis `(e_k)` of `𝔞_P`, the
  differences in the directions `t_1 e_{k_1}, …, t_{n+1} e_{k_{n+1}}`, divide by
  `t_1 ⋯ t_{n+1}` and let all `t_j → 0`. This shows that every partial derivative
  of order `n+1` of `F_g` vanishes, so `F_g` is a polynomial of degree `≤ n`.
  The source's forms satisfy this hypothesis. `𝔄_P` lies in the archimedean
  component and the forms are smooth in the archimedean variable (MW I.2.5 and
  I.2.17), so the orbit maps `a ↦ φ(a g)` are smooth. MW I.3.1 (pp. 40–41) gives
  the corresponding polynomial description for smooth functions on `A_M`
  annihilated by an ideal of finite codimension of the enveloping algebra of
  its Lie algebra.
- Without regularity the converse fails. Take `G = P = 𝔾_m` over `ℚ`, `λ = 0`,
  and `φ(g) = B(log |g|_𝔸)` for a discontinuous additive map `B : ℝ → ℝ`. The
  modulus of `𝔾_m` is `1`, so both actions agree. Every first difference of
  `F_g` is constant, so every product of two differences annihilates `F_g`.
  But `F_1` is `B` in the coordinate `H_P`, which is not a polynomial, so `φ`
  satisfies neither `HasExponent` nor `HasUnnormalizedExponent`.

## 4. Leading exponents (§6.3)

BL embed `𝔞^*_P ⊂ 𝔞^*_0` and define the closed positive chamber
`𝔞^*_{0,+} = {λ ∈ 𝔞^*_0 | ⟨λ, α^∨⟩ ≥ 0 for all α ∈ Δ_0}`. A `λ ∈ 𝔛̃_P` is leading
if `Re λ ∈ 𝔞^*_{0,+}` (p. 203).

- `chamberEmbedding J : X^*(P) ⊗ ℝ → X^*(T) ⊗ ℝ` is restriction of characters
  along `torus J ≫ l J : T → P`, written with the published
  `realParameterRestriction`. This is BL's embedding `𝔞^*_P = X^*(P) ⊗ ℝ ⊂
  X^*(P_0) ⊗ ℝ = X^*(S_0) ⊗ ℝ = 𝔞^*_0` (§2.1 and §6.1, pp. 190 and 199–200), the
  restriction of characters from `P` to `P_0` and then to `S_0`.
- `closedPositiveChamber` is the set of `y ∈ X^*(T) ⊗ ℝ` with
  `⟨y, 1 ⊗ α^∨⟩ ≥ 0` for every simple relative root `α`. The pairing is the
  published real pairing `RealTorusSpace.pair`, and `α^∨` is
  `coroots.coroot α`.
- `IsLeadingExponent J λ` is `chamberEmbedding J (Re λ) ∈ closedPositiveChamber`,
  with `Re` the published `parameterRealPart`.

The coroot of a root is determined by the root: the published theorem
`relativeRealCoroot` (proving `RelativeRealCorootStatement`) shows that any two
`RelativeRootReflectionData` for `i` have the same coroots. The chamber condition only uses the rays `ℝ_{>0} α^∨`,
so the convention for non-reduced relative root systems does not matter.

## 5. Constant terms and cuspidality (§6.2, p. 201)

- `constantTerm Q φ` is `g ↦ ∫_{U_Q(F) \ U_Q(𝔸)} φ(u g) du`, the published
  `subgroupConstantTerm F (iU Q ≫ p Q) φ`. It uses the quotient Haar measure
  scaled to total mass one (BL's footnote on p. 191:
  `vol(V(F) \ V(𝔸)) = 1` for unipotent `V`). The published construction
  evaluates `φ` at a chosen representative and returns `0` where the integrand
  is not integrable. For `φ` left invariant under `U_Q(F)` the representative
  is irrelevant. `U_Q(F) \ U_Q(𝔸)` is compact, so the normalized measure is a
  probability measure.
- `parabolicConstantTerm P Q φ` is `C_{P,Q} φ`: the constant term along `Q`
  if `Q ⊆ P`, and `0` otherwise ("for consistency, it will be useful to set
  `C_{P,Q} φ = 0` if `Q ⊄ P`", p. 201). For `Q ⊆ P` the formula does not depend
  on `P`.
- `IsCuspidalAlong P φ`: `constantTerm Q φ = 0` for every `Q < P`. This is BL's
  `𝒜^cusp_P`: the `φ ∈ 𝒜_P` with `C_{P,Q} φ = 0` for all `Q ⊊ P` (p. 202).
- `IsAutomorphicOn hsmooth Kinf rho P φ` is the published
  `IsAutomorphicFunctionOn` for the subgroup `U(𝔸) M(F)`
  (`parabolicQuotientSubgroup`). The data are a
  smooth structure `hsmooth` of `G`, a subgroup `Kinf` of `G(F_∞)` and a matrix
  representation `rho` whose adelic norm defines moderate growth. The
  differential-commutator premise is discharged by the published
  `adelicDifferentialCommutator_of_smooth`. For the source data below this is
  BL's `𝒜_P` (MW I.2.17).

### Source data

The Lean predicates take `hsmooth`, `Kinf` and `rho` as parameters and are
defined for every choice. They are the source's objects only for the source
choices:

- `rho` is a faithful closed embedding: `rho.hom.hom.left` is a closed
  immersion `G → GL_N`. MW I.2.2 (p. 20) defines the height of `G(𝔸)` from the
  embedding `i_G : G → SL_{2n}` fixed in I.1.1. Moderate growth (I.2.3,
  p. 24) and hence `𝒜_P` (I.2.17, p. 37) refer to that height.
- `Kinf` is the archimedean part `K_∞` of the maximal compact subgroup `K` of
  `G(𝔸)` in good position relative to `P_0` (BL §2.1, p. 190).

For other choices the predicates can differ from the source. For example, take
`G = P = M = 𝔾_m` over `ℚ` with `rho` the trivial one-dimensional
representation. Its published `adelicSourceNorm` is identically `1`, so moderate
growth becomes boundedness. The idelic absolute value `g ↦ |g|_𝔸` is then not
`IsAutomorphicOn`. Yet in the source it is a cusp form on
`𝔾_m(ℚ) \ 𝔾_m(𝔸)`, since `𝔾_m` has no proper parabolics. It is its own cuspidal
projection and its own leading cuspidal component (there are no roots, so its
exponent is leading). The Library does not prove that the predicates are
independent of the faithful embedding (MW I.2.2).

The scope applies to every source identification below. This includes the Levi
data `rho ∘ (l J ≫ p J)` and `Kinf ∩ M(F_∞)` of §6, the cuspidal projection
relation, and the relations of §7. If `rho` is a closed immersion, then so is
`l J ≫ p J ≫ rho`, because the parabolic `P J` is a closed subgroup of `G` and
the Levi factor `M J` is a closed subgroup of `P J`. So the restricted
representation is again a faithful closed embedding, as the source's
automorphic forms on `M` require. This is explanation; the Lean does not
assume it.

## 6. Cusp forms on the Levi and the cuspidal projection ((6.8))

BL characterize the cuspidal projection `φ ↦ φ^cusp ∈ 𝒜^cusp_P` (MW I.3.4–I.3.5)
in two equivalent ways. The first uses pairings over `X_P` with
`(f ∘ H_P) · ψ'`, `f ∈ C_c^∞(𝔞_P)`, `ψ' ∈ 𝒜^cusp_P`; this is MW's definition by the
linear form on `C_0(U(𝔸) M(k) \ G)`. The module uses the second, (6.8): for every cusp form `ψ`
on `X_M = M(F) \ M(𝔸)`,
`(φ(·g), ψ)_{X_M^1} = (φ^cusp(·g), ψ)_{X_M^1}` for all `g ∈ G(𝔸)`, where
`X^1_M = M(F) \ M(𝔸)^1` and `(f_1, f_2)_{X^1_M} = ∫ f_1 \overline{f_2}`
"whenever the integral is absolutely convergent" (p. 202).

- `leviInfiniteCompact Kinf J` is `Kinf ∩ M(F_∞)`, the inverse image of `Kinf`
  under the infinite-adelic point map of `l J ≫ p J`. When `Kinf` is the
  archimedean part of a maximal compact subgroup in good position (BL §2.1,
  p. 190), it is the maximal compact subgroup of `M(F_∞)` used for automorphic
  forms on `M`.
- `IsLeviCuspidal J ψ`: for every parabolic `p' : P' → M J` with
  `range p' ≠ ⊤` and every geometric unipotent radical `r : U' → P'`,
  `subgroupConstantTerm F (r ≫ p') ψ = 0`. The instance binders `U'` affine and
  `r ≫ p'` a closed immersion, which the published constant term needs, always
  hold for a parabolic and its unipotent radical. These
  are the vanishing constant terms along all proper rational parabolics of `M`.
  This is equivalent to vanishing along the standard ones, since every
  parabolic is `M(F)`-conjugate to a standard one; that equivalence is not used.
- `IsLeviCuspForm Kinf rho J ψ`: `ψ` is automorphic on `M(F) \ M(𝔸)` (the
  published `IsAutomorphicFunctionOn` for `M J`, with `leviSmooth J`, the subgroup
  `rationalSubgroup F (M J)`, `leviInfiniteCompact Kinf J` and the matrix
  representation `rho ∘ (l J ≫ p J)`), and `IsLeviCuspidal J ψ`. For the source
  data of §5 these are the cusp forms on `X_M` of (6.8).
- `leviPairingIntegrand J φ g ψ` is the function
  `m ↦ φ(m g) \overline{ψ(m)}` on `NormOneRationalQuotient F (M J) = M(F) \ M(𝔸)^1`,
  evaluated at the chosen representative `m ∈ M(𝔸)^1` of each class. Here
  `M(𝔸)^1` is the published `normOneSubgroup`, the common kernel of all
  `|χ|`, `χ ∈ X^*(M)`, which is BL's `M(𝔸)^1 = ker H_M`. For `φ` left
  `M(F)`-invariant and `ψ` an automorphic form the representative is irrelevant.
- `leviPairing J φ g ψ` is its integral for the published
  `normOneRationalQuotientHaarMeasure F (M J)`, the quotient of Haar measure on
  `M(𝔸)^1` by counting measure on `M(F)`. The characterization does not depend
  on the scaling of this measure.
- `IsCuspidalProjection hsmooth Kinf rho P φ φc`: `φc ∈ 𝒜^cusp_P`
  (`IsAutomorphicOn` and `IsCuspidalAlong`), and for every cusp form `ψ` on
  `M_P` and every `g ∈ G(𝔸)` both pairing integrands are integrable and the
  two pairings agree. Integrability is part of the relation, as the source's
  "whenever the integral is absolutely convergent" requires. For the source
  data of §5 this is the characterization (6.8) of `φc = φ^cusp`. The choice of
  `rho` and `Kinf` enters both the test forms `ψ` and the requirement on `φc`.

The Library's Hilbert-space cuspidal projections are not used. The forms here
have moderate growth and need not lie in those Hilbert spaces. The source
pairing makes sense because cusp forms are rapidly decreasing on `X^1_M`. For
the source data of §5 this gives the recorded convergence for `φ ∈ 𝒜_P`. For
other choices the relation still requires convergence.

## 7. Cuspidal components, decompositions and leading parts (§§6.2–6.3)

- `IsCuspidalComponent P Q φ ψ`: if `Q ⊆ P`, `ψ` is the cuspidal projection
  along `Q` of `constantTerm Q φ`; otherwise `ψ = 0`. This is BL's
  `C^cusp_{P,Q} φ = (C_{P,Q} φ)^cusp`, "where by convention `C^cusp_{P,Q} φ = 0`
  unless `Q ⊂ P`" (p. 202).
- `IsExponentDecomposition P ψ s c` is a supplied finite decomposition
  `ψ = ∑_{λ ∈ s} c λ`. Each component `c λ` with `λ ∈ s` is automorphic on
  `X_P`, cuspidal along `P`, and has unnormalized exponent `λ`
  (`HasUnnormalizedExponent`). It is a decomposition of `ψ ∈ 𝒜^cusp_P` according
  to (6.10). For the source data of §5 the components are smooth, so by §3
  `HasUnnormalizedExponent` is membership in `𝒜^{un}_{P,λ}`. Zero components are allowed and the finset makes the exponents
  distinct. Existence for `ψ ∈ 𝒜^cusp_P` is (6.6) and MW I.3.2–I.3.3. Uniqueness
  of the nonzero components (the sum is direct) is a theorem for later tasks.
- `leadingSum P s c = ∑_{λ ∈ s, λ leading} c λ` keeps the components whose
  unnormalized exponents satisfy `IsLeadingExponent`.
- `IsLeadingPart P ψ ψld`: `ψld = leadingSum P s c` for some exponent
  decomposition `(s, c)` of `ψ`. This is BL's `p^ld_P ψ` (p. 203). By the
  uniqueness just mentioned, `ψld` does not depend on the decomposition; that
  is not proved here.
- `IsUnnormalizedCuspidalExponent P Q φ λ`: `Q ⊆ P` and `λ` carries a nonzero
  component in an exponent decomposition of a cuspidal component of `φ` along
  `Q`. This is `λ ∈ E^{cusp,un}_Q(φ)`, the translate by `ρ_Q` of BL's
  `E^cusp_Q(φ)` (pp. 202–203).
- `IsLeadingCuspidalComponent P Q φ ψ`: if `Q ⊆ P`, there is a cuspidal
  projection `φc` of `constantTerm Q φ` along `Q` such that `ψ` is a leading
  part of `φc`; otherwise `ψ = 0`. This is the `Q`-coordinate
  `p^ld_Q(C^cusp_{P,Q} φ)` of `𝓛_P φ` (6.11b).
- `IsLeadingCuspidalComponents P φ L`: `L Q` is a leading cuspidal component of
  `φ` along `Q` for every `Q`. Here `L = 𝓛_P φ` for `φ` on the parabolic
  quotient `U_P(𝔸) M_P(F) \ G(𝔸)`.
- `IsGlobalLeadingCuspidalComponents φ L`: for every standard `Q` there is a
  cuspidal projection `φc` of `constantTerm Q φ` along `Q` with `L Q` a leading
  part of `φc`. This is `L = 𝓛 φ` (6.11a) for `φ` on `G(F) \ G(𝔸)`, where every
  `Q` lies in `G`. `isGlobalLeadingCuspidalComponents_iff` proves that it is the
  parabolic version for `top`.

None of these definitions imposes conditions on the input `φ`. The automorphy
of `φ` (on `G(F) \ G(𝔸)`: `IsAutomorphicFunctionOn` for `rationalSubgroup F G`;
on a parabolic quotient: `IsAutomorphicOn`) is a hypothesis of the theorems
that will use them, such as Theorem 6.3.

All relations of this section depend on `hsmooth`, `Kinf` and `rho` through
`IsCuspidalProjection` and `IsExponentDecomposition`. They are the source's
`C^cusp_{P,Q}`, `p^ld_P`, `E^{cusp}`, `𝓛_P` and `𝓛` for the source data of §5.
For other choices they are still defined but can differ from the source. The
example of §5 shows this for `𝓛`: with the trivial representation of `𝔾_m`,
`IsGlobalLeadingCuspidalComponents` excludes the idelic absolute value as its
own leading cuspidal component.

## 8. Scope and what is not proved

- The family is supplied data. Its existence for a connected reductive group
  (choices of `T`, `ν`, coroots, the representing group schemes and their
  regularity) is not constructed here. Published results cover parts of it,
  for example `relativeRootReflectionExistence` (reflection data) and
  `exists_compatibleStandardSplitComponent` (split components of the standard
  Levi subgroups).
- Not proved: the existence and uniqueness of cuspidal projections; the
  directness of the decompositions (6.3), (6.6) and (6.10); the independence of
  leading parts from the decomposition; the finiteness of exponent sets; the
  equivalence of the two characterizations of `φ^cusp` in §6.2; the
  equivalence of the polynomial and generalized-eigenspace descriptions for
  smooth orbit maps in §3; and the independence of the predicates from the
  faithful embedding `rho`. These belong to the decomposition, injectivity (Theorem 6.3) and
  geometric-lemma tasks that use these definitions.
- The source identifications of §§5–7 assume the source data of §5: `rho` a
  faithful closed embedding and `Kinf` the archimedean part of a maximal compact
  subgroup in good position. The Lean does not impose these conditions.
  Theorems that compare these relations with the source must assume them.
- Function field `F` is out of scope; the module is for number fields only.

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
  series*, J. Amer. Math. Soc. 37 (2024), 187–234: §2.1 (pp. 189–190;
  `𝔞_P`, `H_M`, `𝔛_P`, `K` in good position); §2.2 (p. 191; `X_P`, `𝒜_P`, the
  footnote normalizing unipotent Haar measures); §6.1 (pp.
  199–200; `S_M`, `𝔞^*_P ⊂ 𝔞^*_0`, simple roots and coroots, `H_P`); §6.2
  (pp. 200–202; (6.1)–(6.3), `ρ_P`, `C_{P,Q}`, `𝒜^cusp_P`, (6.6)–(6.8), cuspidal
  components, `E^cusp`); §6.3 (p. 203; (6.10), `𝔞^*_{0,+}`, leading exponents,
  `p^ld_P`, (6.11a)–(6.11b), Theorem 6.3). TeX source `1911.02342.tex`,
  lines 1102–1383.
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein
  series* (1995): I.2.2 (p. 20; the height from the embedding `i_G` of I.1.1),
  I.2.3 (p. 24; moderate growth), I.2.5 (p. 26; smooth functions), I.2.17
  (p. 37; automorphic forms on `U(𝔸) M(k) \ G`), I.3.1–I.3.2
  (pp. 40–43; `A_M`-finite functions and the exponent decomposition), I.3.4–I.3.5
  (pp. 45–48; cuspidal components and the cuspidal form `φ_P^cusp`).
