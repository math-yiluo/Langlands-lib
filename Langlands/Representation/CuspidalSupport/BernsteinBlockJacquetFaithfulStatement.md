# The Jacquet functor to the cuspidal component kills no block object: statement

Author: Worker 6. Module `Langlands.Representation.CuspidalSupport.BernsteinBlockJacquetFaithfulStatement`, namespace `Langlands.CuspidalSupport`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.10.3, Proposition and proof, printed p.209 / PDF p.215. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## The source

Let `(M, (ρ, W))` be a cuspidal datum with `M` a standard Levi, `P` the standard parabolic with Levi `M`, `D = [M, ρ]_M` and `𝔰 = [M, ρ]_G`. Let `r_D` be the composite of `r_P^G : M(G) → M(M)` with the projection onto the component `M(M)_D`. The proposition reads: `r_D : M(G)_𝔰 → M(M)_D` sends nonzero objects to nonzero objects. The proof: since `i_{P̄}^G Π_D` is a progenerator of `M(G)_𝔰`, second adjointness gives `{0} ≠ Hom_G(i_{P̄}^G Π_D, π) ≃ Hom_M(Π_D, r_P^G π) = Hom_M(Π_D, r_D π)`.

## The Lean statement

`BernsteinBlockJacquetFaithfulStatement` is a statement unit: nothing is proved. It uses the published standard-family framework and exactly the hypotheses of the companion VI.10.1 Theorem statement `BernsteinInducedProgeneratorStatement` (Worker 6, candidate `c8183a09-928c-4f9e-8755-071b330ec5c1`). These are:

- a standard family `family : BernsteinStandardFamily i ν` over a nonarchimedean local field;
- a cuspidal datum `a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family`, with standard Levi `M = bernsteinLeviScheme i ν a.roots`;
- an irreducible `ρ₀` of the common norm kernel of `M(F)` with an injective morphism into the restriction of `a.representation`.

`Π_D` is `rationalNormKernelSummandInduction M ρ₀`, transported to the literal standard Levi subgroup `levi i ν a.roots` by the published `bernsteinLiteralLeviRep`. The published VI.4.1 statement `RationalSummandSmallProgeneratorStatement` asserts that `Π_D` is a small progenerator of the inertia block of `a.representation` in `M(M)`.

The conclusion is the following. For every object `X` of the published block `BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a)` (Renard's `M(G)_𝔰`) with `Nontrivial X.obj`, there is a nonzero morphism

`f : bernsteinLiteralLeviRep i ν a.roots Π_D ⟶ (normalizedJacquetFunctor (unipotent i ν a.roots) (levi i ν a.roots) _ _).obj X.obj`,

from `Π_D` to the published normalized Jacquet module `r_P^G(X)` along the standard parabolic of `a.roots`. This is the functor paired with the normalized induction used for `bernsteinInduction`. The normalizer hypothesis is `(family.decomposition a.roots).levi_le_normalizer`.

## Why this is Renard's proposition

The block decomposition `M(M) = ∏ M(M)_{D'}` (VI.7.2 for `M`) is not available as a published construction, so the projection `r_D` cannot be written directly. The statement therefore uses the equivalent condition `Hom_M(Π_D, r_P^G X) ≠ 0`. Equivalence (not formalized): `Π_D` lies in `M(M)_D`, and there are no nonzero morphisms between different components, so `Hom_M(Π_D, r_P^G X) = Hom_M(Π_D, r_D X)`. Since `Π_D` is a generator of `M(M)_D`, this space is nonzero exactly when `r_D X ≠ 0`. The nonvanishing of this Hom space is also exactly what Renard's proof establishes.

## Remarks

- "Nonzero object" is `Nontrivial X.obj`, i.e. a carrier with a nonzero vector.
- The proof (second adjointness and the VI.10.1 results) is not formalized here.
- The VI.10.3 Corollary is the separate statement `SupercuspidalInductionLengthStatement` (candidate `9cd8e9be-876f-44bc-806a-ebade95b7e73`).
