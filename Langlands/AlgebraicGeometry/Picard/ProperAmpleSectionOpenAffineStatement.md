# Generation loci of ample line bundles on proper schemes over affine bases

Author: Worker 3462.

`Langlands.AlgebraicGeometry.Picard.ProperAmpleSectionOpenAffineStatement.{u}`
quantifies, in the scheme universe `u`, over schemes `X` and `U` with `U`
affine, a proper morphism `f : X ⟶ U`, an actual line bundle
`L : LineBundle X` satisfying the Library's `L.IsAmple`, and a global section
`σ : GlobalSections L.obj` of `L` itself (degree one). It asserts

```lean
IsAffineOpen (trivializationOpen L.obj σ)
```

that is, the open subscheme `X_σ` on which `σ` generates `L` is affine.

The Library's `LineBundle.IsAmple` is the section-open definition: `X` is
quasi-compact, and every point lies in some `X_s` with `s` a global section
of a positive tensor power and `X_s` affine. The conclusion concerns every
degree-one section, not only those in a chosen cover. Without properness it
fails, for example for the trivial bundle on a quasi-affine non-affine
scheme and `σ = 1`.

## Provenance

Derived; a standard consequence of the definitions, used here as a step of
the target `PolarizedEtaleRelationEffectivityStatement`. A proof:

1. For an ample `L`, every `X_σ` is quasi-affine: on each affine `X_s` with
   `s ∈ Γ(X, L^{⊗n})`, the intersection `X_σ ∩ X_s` is the principal open of
   the function `σ^n / s`. Compare the Stacks Project, Proposition 28.27.13,
   tag [01Q3](https://stacks.math.columbia.edu/tag/01Q3).
2. Let `j : X_σ ⟶ Y = Spec Γ(X_σ, O)` be the resulting open immersion. It is
   an isomorphism if it is universally closed, which can be checked by the
   valuative criterion. Given a valuation ring `V` with fraction field `K`, a
   `K`-point of `X_σ` and a compatible `V`-point of `Y`, properness of `f`
   extends the `K`-point to a `V`-point `v` of `X` over `U`. Choose a section
   `s` of `L^{⊗n}` generating at the image of the closed point. On `Spec V`
   the pullbacks of `σ` and `s` are elements `a` and `b` of `V` after
   trivializing, with `b` a unit. The function `s / σ^n ∈ Γ(X_σ, O)` pulls
   back through the `V`-point of `Y`, so `b / a^n ∈ V`; hence `a` is a unit
   and `v` factors through `X_σ`.

## Intended use

The proof of `PolarizedEtaleRelationEffectivityStatement` applies this to an
equivariant power of the polarization (see
`EquivariantLineBundleTensorPowStatement`) and an invariant section produced
by `EquivariantInvariantSectionStatement`, obtaining invariant affine opens
covering the chart.

This module defines the proposition only and proves nothing.
