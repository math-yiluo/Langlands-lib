# Godement constructions on a coreflective subcategory of twisted sheaves

Author: Worker 26. Generalizes the section on discrete sheaves of Worker 26's published
module `Langlands.Sheaf.Equivariant.TwistedGodement`, and uses its twisted Godement functor
`twistedZeroFunctor`, its coaugmentation `twistedCoaugmentation` and
`mono_twistedCoaugmentation_of_jointlyFaithful`. The Godement complex is
`Langlands.Cohomology.CokernelComplex.functor`, as in `TwistedGodement`.

## Purpose

`TwistedGodement` defines the degree-zero Godement functor of a twisted site, and its
discrete part `discreteZeroFunctor` on the discrete sheaves of a local action system. The
construction uses only the inclusion of discrete sheaves into all sheaves and its right
adjoint, the discrete part. This module repeats it for any fully faithful functor
`incl : 𝒜 ⥤ Sheaf (twistedTopology ρ J) (ModuleCat R)` with a right adjoint `cor`.

The intended instance is the inclusion of the locally discrete sheaves of
`LocalActionSmoothPart`, with its right adjoint `smoothCoreflector` (`smoothAdjunction`).
For the twisted étale site these are Berkovich's étale `G`-sheaves. The module
`DivisibleSystem.AnalyticEtale` uses that instance.

All declarations are in `Langlands.Sheaf.Equivariant.TwistedOver`.

## Data

- `C : Type u` with `Category.{v} C`, a morphism property `P` with `[P.RespectsIso]`, an
  object `X`, a group `G : Type uG` with `ρ : G →* Aut X`, and a topology `J` on
  `P.Over ⊤ X` with `[IsTranslationInvariant J]`.
- Points `points : I → J.Point.{w}` with `I : Type w`, and a commutative ring `R : Type w`.
- The hypothesis of `TwistedGodement` that every module presheaf on `P.Over ⊤ X` has a
  pointwise right Kan extension along `(ι P ρ).op`. It defines the induction from the site
  over `X` to the twisted site.
- A category `𝒜 : Type uA` with `Category.{vA} 𝒜`, functors
  `incl : 𝒜 ⥤ Sheaf (twistedTopology ρ J) (ModuleCat R)` and
  `cor : Sheaf (twistedTopology ρ J) (ModuleCat R) ⥤ 𝒜`, and an adjunction
  `adj : incl ⊣ cor`.

## Declarations

- `exactZeroFunctor ρ J points R incl cor`: the endofunctor
  `incl ⋙ twistedZeroFunctor ρ J points (ModuleCat R) ⋙ cor` of `𝒜`. It restricts to the
  site over `X`, takes the product of the skyscraper sheaves at the points, induces back to
  the twisted site and applies `cor`.
- `exactCoaugmentation ρ J points R adj`: the natural transformation
  `𝟭 𝒜 ⟶ exactZeroFunctor ρ J points R incl cor` with components the unit of `adj`
  followed by `cor` applied to the twisted coaugmentation of `incl F`. Naturality follows
  from the naturality of the unit and of the twisted coaugmentation.
  `exactCoaugmentation_app` (by `rfl`) gives the components.
- `mono_exactCoaugmentation_of_jointlyFaithful ρ J points R adj hpoints F`: if `incl` is full
  and faithful and the fibre functors `(points i).sheafFiber` are jointly faithful on module
  sheaves on `J` (`hpoints`), every component of the coaugmentation is a monomorphism. The
  unit of `adj` is an isomorphism because `incl` is fully faithful (Mathlib's
  `unit_isIso_of_L_fully_faithful`). The twisted coaugmentation is a monomorphism by
  `mono_twistedCoaugmentation_of_jointlyFaithful`, and the right adjoint `cor` preserves
  monomorphisms.
- `exactComplexFunctor ρ J points R adj`, for abelian `𝒜`: the Godement cochain complex
  functor `𝒜 ⥤ CochainComplex 𝒜 ℕ`, the published `CokernelComplex.functor` of the
  Godement functor and its coaugmentation (iterated cokernels).

## Original source and correspondence

This is construction infrastructure. The source correspondence is the one recorded in
`TwistedGodement`. Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), registered as `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, §2,
printed p.304 = PDF p.6, uses Berkovich's smooth `G`-equivariant Godement resolution of an
étale `G`-sheaf. In the twisted model, the Godement functor of the étale `G`-sheaves is the
locally discrete part of the twisted Godement functor. This module gives that
construction for any coreflective subcategory. The generalization is ours.

## Not formalized here

The exactness of `exactZeroFunctor` (Harris's Fact 3), a family of points satisfying
`hpoints`, and any comparison with the discrete-sheaf constructions of `TwistedGodement`.
