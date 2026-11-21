# Slice-wise polynomial growth gives adelic moderate growth (proof)

## What the module proves

`Langlands.Automorphic.GroupSchemeFunctions.adelicSliceModerateGrowthStatement` proves the
published statement
`Langlands.Automorphic.GroupSchemeFunctions.AdelicSliceModerateGrowthStatement.{u}`
(module `Langlands.Automorphic.GroupSchemeSliceAdelicGrowthStatement`) at its full
universe-polymorphic scope, with no extra hypothesis. Let `F` be a number field, `G` an
affine connected reductive group scheme over `F`, and `rho` a closed matrix representation
of `G` of positive size `N`. Let `f` be a continuous rational-invariant function on the
adelic points of `G` with an open finite-adelic stabilizer. Assume each infinite slice
`a ↦ f(pair a b)` has polynomial growth, with a constant and an exponent that may depend on
the finite point `b`. Then `f` has adelic moderate growth: one constant `C > 0` and one
exponent `r` give `‖f(g)‖ ≤ C · adelicSourceNorm(g)^r` for every adelic point `g`.

## Implemented proof

The theorem applies two published Library proofs:

`adelicSliceModerateGrowthStatement_of_rationalHeightReduction
  RepresentationGrowth.adelicRationalHeightReduction_of_finiteRightSiegelCover`

1. `RepresentationGrowth.adelicRationalHeightReduction_of_finiteRightSiegelCover`
   (module `Langlands.Global.AdelicFiniteTranslateHeightReduction`) proves
   `RepresentationGrowth.AdelicRationalHeightReductionStatement` without hypotheses. That
   statement gives a compact set `Ω` of finite-adelic points, a constant `C > 0` and an
   exponent `e`, none of which depends on the point. For every adelic point `g` there is a
   rational `q` such that the finite component of `q g` lies in `Ω`. Also, the
   archimedean matrix height of the infinite component of `q g` is at most
   `C · adelicHeight(g)^e`. Its proof uses three published results:
   - the finite-volume covering construction (module `Langlands.Global.AdelicFiniteVolumeProof`).
     It writes a rational translate of each norm-one point as an element of a weak Siegel
     product times one of finitely many right factors;
   - polynomial norm minimality on Siegel products,
     `AdelicSiegelFactors.siegelNormMinimalityStatement` (module
     `Langlands.Global.AdelicSiegelNormMinimalityProof`);
   - the polynomially bounded positive central factor,
     `RepresentationGrowth.centralNormOneHeightFactorStatement` (module
     `Langlands.Global.AdelicCentralPositiveHeightProof`).

   The finite right factors only enlarge the compact set and the constants. So this route
   does not use the exact Siegel covering `AdelicSiegelFactors.AdelicSiegelReductionStatement`
   (one Siegel set without right translates).
2. `adelicSliceModerateGrowthStatement_of_rationalHeightReduction` (module
   `Langlands.Automorphic.GroupSchemeSliceAdelicGrowthReduction`) turns any proof of the
   rational height reduction into a proof of the target. Rational invariance of `f`
   replaces `g` by `q g`. Finitely many left cosets `b_j L` of the open stabilizer `L`
   cover the compact set `Ω`. So `L`-invariance reduces `f(q g)` to a value of one of
   finitely many slices `a ↦ f(pair a b_j)`. The slice hypothesis bounds these values by
   `K_j · height(a)^(d_j)`. The resulting bound is `K₀ · C^D · adelicHeight(g)^(D·e)`, with
   `K₀ = Σ_j K_j` and `D = max_j d_j`. Finally, `hasAdelicModerateGrowth_iff` converts this
   height bound into the moderate-growth bound with `adelicSourceNorm`.

The module's axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Sources

The proof follows the Siegel-set argument for moderate growth. It changes one thing: it
uses a finite union of right translates of a Siegel set instead of one Siegel set.

- Mœglin–Waldspurger 1995 (`moeglin-waldspurger-1995-spectral-decomposition`), I.2.1
  (Siegel sets with `G(k) S = G`), I.2.2 (vii) (norm minimality) and I.2.3 (moderate
  growth), printed pp. 20–25.
- Getz–Hahn 2024 (`getz-hahn-2024-automorphic-representations`), Lemma 6.3.2 (the
  Siegel-set criterion for moderate growth, printed p. 162) and display (6.17) (printed
  pp. 164–165).
