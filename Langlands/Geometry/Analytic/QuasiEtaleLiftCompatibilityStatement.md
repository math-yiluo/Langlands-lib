# Statement: lifts of a continuous action are compatible with morphisms over the base

Author: Worker 21.

This module states, without proof, that the lifts of a continuous action to
compact spaces quasi-étale over `X` are compatible with morphisms over `X`.
For such spaces `U` and `V`, a morphism `f : V → U` over `X`, and lifts of the
action to `U` and to `V`, the morphism `f` is equivariant for the two lifted
actions on some open subgroup. This is the canonicity of Berkovich's lifts in
the form used to build equivariant sheaves on the quasi-étale site. The
statement is the `Prop`-valued definition
`Langlands.Analytic.SaturatedAtlasPresentation.QuasiEtaleLiftCompatibilityStatement`.
Nothing in the module proves it.

## Original sources

Berkovich, *Vanishing cycles for formal schemes* (1994) ([Ber3]), registered
as `berkovich-1994-vanishing-cycles-formal-schemes`, SHA256
`f4f7bc00cc46a0a5f72a69d7bbb220bce1d3ed9fd465aeda629f37dfc054bed1`, §7,
printed p.560 / PDF p.22. The section begins "As in §6, all the analytic spaces
considered are assumed to be Hausdorff." Key Lemma 7.2 reads:

> Let X be an analytic space, and let f : U → X be a quasi-étale morphism with
> compact U. Then there exists ε₀ ∈ 𝔈(U) with the following property. For any
> ε ≤ ε₀ there exists δ ∈ 𝔈(X) such that, for any cartesian (resp.
> commutative) diagram (∗) and any morphism φ′ : Y → X with d(φ, φ′) < δ,
> there exists a unique morphism ψ′ : V → U with d(ψ, ψ′) < ε for which the
> following diagram is also cartesian (resp. commutative).

Here (∗) is the square with `φ : Y → X`, `ψ : V → U`, `g : V → Y` and
`f : U → X`, and commutativity means `f ∘ ψ = φ ∘ g`.

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*
(unfinished manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
(folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`), §1.4,
printed p.7:

> It follows that for any quasi-étale morphism U → X with compact U the action
> of G on X extends in a canonical way to a continuous action of some open
> subgroup G_U ⊂ G on U.

## The statement

`QuasiEtaleLiftCompatibilityStatement K`, for a complete ultrametric normed
field `K`, is the following proposition. Let `G` be a topological group (in a
fixed universe). Let `X`, `U`, `V` be analytic spaces in
`LocalizedCategory.{u, v, v}`, let `ρ : G →* Aut X` be an action, and let
`p : U ⟶ X`, `q : V ⟶ X` and `f : V ⟶ U` be morphisms with `f ≫ p = q`.
Assume that

- the underlying space of `X` is Hausdorff,
- `ρ` is continuous (the Library's `IsContinuousAction`),
- `p` and `q` are quasi-étale (the Library's `quasiEtale`), and
- `U` and `V` are compact (the Library's `IsCompactSpace`: compact and
  Hausdorff).

Then for every lift `a : ActionLift ρ p` and every lift `b : ActionLift ρ q`
there is an open subgroup `N` of `G`, contained in the subgroups of `a` and
`b`, such that for every `g ∈ N`

`(b.action g).hom ≫ f = f ≫ (a.action g).hom`.

In the usual order of composition this says `f ∘ b(g) = a(g) ∘ f`. The lifts
`ActionLift` are those of the published module `LocalActionLifts`: an open
subgroup, a continuous action of it on the source, and equivariance of the
morphism to `X`. Composition `≫` is in diagrammatic order.

The uniqueness half of the published `QuasiEtaleActionLiftStatement` is the
special case `V = U`, `f = 1_U`, `q = p`.

## Correspondence with the sources

The statement is derived from the uniqueness in Key Lemma 7.2 for commutative
diagrams. The following argument is not formalized. Apply the Key Lemma to
`p : U → X` and the commutative square with `Y = V`, `g = 1_V`, `φ = q` and
`ψ = f`, which commutes because `p ∘ f = q`. For `h ∈ G` near `1`,
`φ′ = ρ(h) ∘ q` is `δ`-close to `q` by continuity of `ρ`. Both `f ∘ b(h)` and
`a(h) ∘ f` satisfy `p ∘ ψ′ = ρ(h) ∘ q`, by equivariance of `q` and `p`. By
continuity of `a` and `b`, both are `ε`-close to `f` for `h` near `1`. So they
are equal by uniqueness. The elements of both lift subgroups at which they
are equal form a subgroup containing a neighbourhood of `1`, hence an open
subgroup.

The manuscript's phrase "in a canonical way" is the form of this
compatibility that Berkovich uses on the quasi-étale site. Conventions are as
in `QuasiEtaleActionLiftStatement`. Spaces are Hausdorff: both sources assume
it, and here it is imposed on `X` and contained in the compactness of `U` and
`V`. `Aut X` is Berkovich's group of `K`-automorphisms, and continuity is the
Library's `IsContinuousAction`.

## Scope

Only the proposition is defined. The Key Lemma and the deduction above are
not formalized.
