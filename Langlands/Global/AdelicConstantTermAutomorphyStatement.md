# Constant terms of automorphic functions on parabolic quotients

Module `Langlands.Global.AdelicConstantTermAutomorphyStatement` states the proposition
`Langlands.Global.ConstantTermAutomorphyStatement` (universe `u`) and proves nothing.

## Statement

Let `F` be a number field and `G` an affine group scheme over `Spec F`, locally of finite type,
with a compatible standard parabolic family `fam : StandardParabolicFamily F G` (module
`Langlands.Global.AdelicLeadingCuspidalComponents`; the family includes the connected
reductivity of `G`, a maximal split torus, a generic cocharacter and the standard parabolics
`P_J = M_J U_J`). Fix

- an arbitrary subgroup `Kinf` of `G(F_∞)` (`InfiniteAdelicGroupPoints F G`),
- a matrix representation `rho : G → GL_N` that is a closed embedding (`IsClosedSubgroup rho`),
- a smooth structure `hsmooth : SmoothOfRelativeDimension d G.X.hom`.

Let `Q ≤ P` be standard indices, that is `P_Q ⊆ P_P`, and let `φ : G(𝔸) → ℂ` satisfy
`fam.IsAutomorphicOn hsmooth Kinf rho P φ`. Then the constant term

\[
  (C_Q\varphi)(g) = \int_{U_Q(F)\backslash U_Q(\mathbb A)} \varphi(ug)\,du
\]

(`fam.constantTerm Q φ`, with the normalized quotient measure of the Library) satisfies
`fam.IsAutomorphicOn hsmooth Kinf rho Q (fam.constantTerm Q φ)`.

Unfolded, `IsAutomorphicOn Q` is `IsAutomorphicFunctionOn` (module
`Langlands.Automorphic.GroupSchemeInvariantForms`) for the subgroup `U_Q(𝔸) M_Q(F)` of `G(𝔸)`
(`parabolicQuotientSubgroup`): left invariance under that subgroup, smoothness (continuity,
plot-smooth infinite slices and invariance under right translation by an open subgroup of
`G(𝔸_f)`), finite-dimensionality of the span of the right translates by `Kinf`, annihilation of
all infinite slices by one ideal of finite codimension in the center of the complex enveloping
algebra of `G(F_∞)`, and moderate growth for the adelic norm of `rho`.

## Sources

- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
  I.2.6, p. 27: for a standard parabolic `P = MU` and `φ` on `U(k)\G`, the constant term
  `φ_P(g) = ∫_{U(k)\U(𝔸)} φ(ug) du` is left invariant under `M(k)`, of moderate growth, or
  smooth when `φ` is left invariant under `G(k)`, of moderate growth, or smooth. I.2.17,
  pp. 37–38, defines automorphic forms on `U(𝔸)M(k)\G` by moderate growth, smoothness,
  `K`-finiteness and `𝔷`-finiteness.
- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024), §6.2, p. 201: for `Q ⊂ P` the constant term
  `C_{P,Q}φ(g) = ∫_{U_Q(F)\U_Q(𝔸)} φ(ug) du` defines a linear map `𝒜_P → 𝒜_Q`.

## Correspondence and scope

The proposition is the assertion of Bernstein–Lapid that `C_{P,Q}` maps `𝒜_P` to `𝒜_Q`,
for the Library's actual standard family and automorphy predicate. A function on
`U_P(𝔸)M_P(F)\G(𝔸)` is left invariant under `Q(F)` because `Q ⊆ P`, so Mœglin–Waldspurger
I.2.6 applies with `M_Q(F)` in place of `M(k)`; left invariance under `U_Q(𝔸)` comes from the
invariance of the quotient measure. Right translations commute with the constant term, which
gives the finiteness conditions under `Kinf` and under the center of the enveloping algebra.

The sources work with the infinite part `K_∞` of a fixed maximal compact subgroup. The
proposition allows an arbitrary subgroup `Kinf`, because finiteness under right translation by
any subgroup passes to the constant term. For `Q = P` the conclusion is the hypothesis, since
the constant term along `P` of a function on `U_P(𝔸)M_P(F)\G(𝔸)` is the function itself.
