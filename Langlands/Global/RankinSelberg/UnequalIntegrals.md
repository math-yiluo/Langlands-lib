# Actual global Rankin–Selberg projections and unequal-rank integrals

This module defines the unequal-rank objects in J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004), §2.2, printed pp.205–207 (PDF pp.208–210), registered as `cogdell-2004-analytic-theory-gln`. The source PDF SHA-256 is `8117f145869274324b12344dc83fa3289e3bd27c515b8d0d4a0211cd64174944`. It supplies definitions, not the analytic assertions of Theorem 2.1.

## Actual carriers and functions

All declarations are in `Langlands.Global.RankinSelbergGlobal`. The number field `F` remains in an arbitrary universe. `Scheme F n` is the actual general linear group scheme and `Points F n` is its actual adelic point group. These are abbreviations for existing Library objects, not supplied carriers. `GeneralLinearGroupPoints.adelicEquiv` identifies these points with the actual invertible matrices over `Adeles F`.

For `T : Automorphic.CuspidalOperatorRealization F r`, `cuspFunction F T v` is the actual function of the vector `v : T.Space`. It applies `T.realization.toContinuous`, transports by the inverse of `continuousGeneralLinearEquiv`, and evaluates by `GroupSchemeFunctions.evaluate`. Its rank is `r + 1`. `cuspWhittaker F T ψ v` applies the Library's `generalLinearWhittakerFunction` with every simple-root coefficient equal to one to this function. The second cusp form's Whittaker function is obtained by passing `ψ⁻¹` as the character.

The definitions of the integral operators allow arbitrary functions on these actual point groups. The intended analytic statements specialize them to these cusp functions and impose continuity, nontriviality, unitarity and rational triviality of the additive character as appropriate. No analytic claim is a hypothesis of an integral definition.

## Determinant and block conventions

`detNorm F n g` is the positive real underlying the Library's `AdelicBlockDeterminantCharacter.determinantNorm F n`, hence the normalized idelic absolute value of the actual determinant. `detPower F n g s` is `exp(s * log(detNorm F n g))`, with the real logarithm embedded in `ℂ`. Thus a positive-real base always uses its real logarithm. There is no complex logarithm branch choice.

`padMatrix`, `padGL` and `pad` implement `g ↦ diag(g,I)` with the first block occupying the initial indices, using `finSumFinEquiv` and then the rank equality `m + (n - m) = n`. These are concrete matrix constructions. `iota` is transpose inverse. `dualFunction F n φ g` is `φ(w_n (ᵗg⁻¹))`, using the Library's long Weyl matrix and inverse-transpose map. This is Cogdell's convention on pp.206–207. For a rationally invariant function, inserting the rational matrix `w_n` does not change its value.

## Projection

Write `n = r + 1`. `projectionWeight n m` is constant zero on indices `0,…,m`, then strictly decreasing. Its block unipotent subgroup `projectionUnipotent F n m` is therefore the radical `Y_(n,m)` of the standard parabolic of type `(m+1,1,…,1)` in Cogdell p.205. Its adelic points are proved closed by the Library's represented closed subgroup scheme construction. No closedness assumption is supplied by the caller.

`projectionCharacter F r m ψ` restricts the standard generic character: it applies `ψ` to the sum of adjacent upper-diagonal entries. The adjacent entries in the first block vanish on this radical. `projection F h ψ φ p`, for `h : m < r + 1`, is precisely

\[
|\det p|^{-(r-m)/2}
\int_{Y_{n,m}(F)\backslash Y_{n,m}(\mathbb A)}
  \varphi(y\operatorname{diag}(p,I_{r-m}))\overline{\psi(y)}\,dy.
\]

For a unitary `ψ`, the conjugate in the Library coefficient is `ψ⁻¹`, as in the source. This displayed expression defines the operator on all `GL_(m+1)(𝔸)`; its restriction to the mirabolic subgroup is Cogdell's projection. The extension lets the composition by transpose inverse make sense even though transpose inverse sends the mirabolic to its opposite. `dualProjection` is exactly this composition `ι ∘ projection ∘ ι`, where `ι` acts on functions by precomposition with transpose inverse. The Weyl matrix belongs in `dualFunction`, not in the definition of `ι`.

The unipotent integral reuses `subgroupCharacterCoefficient`. Its measure is exactly `AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure`: the actual quotient Haar measure divided by its total mass. On the compact unipotent rational quotient this gives mass one, the same normalization used by the Library's global Whittaker functions. As in the reused coefficient, `Quotient.out` chooses a representative. Rational invariance of the input and rational triviality of the character are what make the intended integrand independent of that choice; no invariance is asserted here for arbitrary inputs.

## Global integrals and convergence boundary

Write `m = t + 1`, `n = r + 1` with `h : t < r`. `unequalIntegrand` evaluates

\[
P_m^n\varphi(\operatorname{diag}(g,1))\varphi'(g)|\det g|^{s-1/2}
\]

at the chosen representative `g` of the actual quotient `GL_m(F)\GL_m(𝔸)`. `unequalIntegral` integrates it against the existing `AdelicGroupPoints.rationalQuotientHaarMeasure`. This is the Library's actual ambient Haar divided by counting measure on the discrete rational subgroup, with the scale fixed by that Library Haar choice; it is not a probability normalization on the generally noncompact reductive quotient. Cogdell leaves this reductive Haar scale implicit. Future unfolded quotient measures must be compatible with this exact choice and the mass-one unipotent normalization above. `dualUnequalIntegrand` and `dualUnequalIntegral` replace the projection by `dualProjection`, as on p.207.

These are defining Bochner integrals. Lean totalizes such an integral by zero when its integrand is not integrable. This convention does not assert convergence, holomorphy, continuation, representative independence, or a functional equation. For actual cusp forms those are separate Prop-valued statements to be proved. In particular no analytic continuation is defined by assigning values outside a convergence region.

The concrete transport and padding helpers are internal implementation choices derived from the source's matrix formulas. They do not extend the mathematical claims beyond the displayed definitions. Existing Library Lean/Markdown pairs are unchanged.
