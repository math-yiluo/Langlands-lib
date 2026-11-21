# Joint evaluation of weakly holomorphic uniform-growth families

In `Langlands.Automorphic.GroupSchemeFunctions`, use the uniform-growth
space `𝔉 = UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L`
with its weighted-derivative topology. The data are a number field `F`,
an affine group scheme `G` over `F`, a closed matrix representation of
positive size `N`, the smooth calculation data `hsmooth`, `hcalc`, an
exponent `R`, and a finite-adelic level subgroup `L`. Write `ev(a,g)` for
`UniformGrowthFrechetSpace.toFun ... a g` on the actual adelic points of `G`.

## Named proposition

`UniformGrowthJointContinuityStatement` takes an open preconnected
`T ⊆ ℂⁿ`, a map `a : ℂⁿ → 𝔉`, scalar functions `q,p` on `ℂⁿ`, and a
scalar family `h(s,g)`. Assume on `T` that:

- `q` is holomorphic and nonzero somewhere, and `p` is continuous;
- `s ↦ φ(a(s))` is holomorphic for each scalar continuous complex-linear
  functional `φ` on `𝔉`;
- `s ↦ h(s,g)` is holomorphic for each adelic point `g`;
- `q(s) h(s,g) = p(s) ev(a(s),g)` for every `s ∈ T` and every `g`.

Then `h` is jointly continuous on `T × G(𝔸)`. The proof
`uniformGrowthJointContinuity` specializes
`UniformGrowthFrechetSpace.continuousOn_of_mul_eq_eval`, which allows
any finite-dimensional complex normed parameter space.

## Implemented proof

1. `UniformGrowthFrechetSpace.continuousOn_of_differentiableOn_dual` tests
   continuity in the topology of `𝔉` by the maps `weightedDerivativeCLM`
   to `ℓ∞`. For each such map `D`, the function `D ∘ a` is weakly
   holomorphic, since a scalar functional on `ℓ∞` composes with `D`
   to a scalar functional on `𝔉`. Use `WeakHolomorphy.continuousAt_of_weak`
   on the family of operators `z ↦ z • (D ∘ a)(s)` with source `ℂ`.
   Evaluation at `1` gives continuity in the `ℓ∞` norm for that seminorm.
2. `UniformGrowthFrechetSpace.continuous_uncurry_toFun` uses the identity
   derivative `D 1`. Its image is a bounded function of `g`, and is also
   continuous: it is the original continuous adelic function times the
   inverse of the continuous positive weight `w(g) = adelicSourceNorm(g)^R`,
   viewed in `ℂ`. The source norm is continuous by the proved identity
   expressing it as the adelic representation height divided by a nonzero
   constant. On the subtype of continuous `ℓ∞` functions, evaluation is
   continuous in `g` for a fixed vector and is uniformly 1-Lipschitz in the
   vector at each `g`. The product continuity lemma gives joint continuity
   of this evaluation. Multiplication by `w(g)` recovers the original value
   `ev(a,g)`.
3. The given product identity now yields joint continuity of `q h`.
   `SeveralComplex.continuousOn_of_differentiableOn_of_mul` removes `q`,
   using holomorphy in `s` and the nontriviality of `q` on `T` rather than
   assuming nonvanishing at the point of evaluation.

## Provenance and scope

This is a derived continuity criterion for the Library's existing
uniform-growth spaces. It combines the Library's weak holomorphy and
adelic-height results with an elementary evaluation estimate and
holomorphic division on affine complex line discs. It is a bridge for
the joint root-hyperplane formulation used in the approach to Lapid's
Proposition 6: it supplies the joint continuity step when a local
uniform-growth numerator and a pointwise holomorphic pole-cleared family
are given. It does not establish either continuation or root-hyperplane
singularities for Eisenstein series, nor does it prove Proposition 6.
