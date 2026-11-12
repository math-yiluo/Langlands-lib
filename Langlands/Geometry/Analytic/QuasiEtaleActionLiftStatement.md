# Statement: lifts of continuous actions to compact quasi-étale spaces

Author: Worker 21.

This module states, as a proposition, the consequence of Berkovich's Key
Lemma used to define equivariant sheaves: a continuous action on `X` lifts,
on an open subgroup, to every compact space quasi-étale over `X`, and the
lift is unique up to shrinking the subgroup. The statement is not proved
here; it is a target for a separate proof task.

## Original sources

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*
(unfinished manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
(folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`; file
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`),
§1.4, printed p.7:

> Recall that the Key Lemma 7.2 from [Ber3] implies that given a quasi-étale
> morphism U → X with compact U there exist ε ∈ 𝔈(X), δ ∈ 𝔈(U) and a unique
> continuous homomorphism 𝒢_ε(X) → 𝒢_δ(U) such that the morphism U → X
> commutes with the action of 𝒢_ε(X). It follows that for any quasi-étale
> morphism U → X with compact U the action of G on X extends in a canonical
> way to a continuous action of some open subgroup G_U ⊂ G on U.

Berkovich, *Vanishing cycles for formal schemes* (1994) ([Ber3]), registered
as `berkovich-1994-vanishing-cycles-formal-schemes`, SHA256
`f4f7bc00cc46a0a5f72a69d7bbb220bce1d3ed9fd465aeda629f37dfc054bed1`, §7,
printed p.560 / PDF p.22: "As in §6, all the analytic spaces considered are
assumed to be Hausdorff." Key Lemma 7.2: "Let X be an analytic space, and let
f : U → X be a quasi-étale morphism with compact U. Then there exists
ε₀ ∈ 𝔈(U) with the following property. For any ε ≤ ε₀ there exists
δ ∈ 𝔈(X) such that, for any cartesian (resp. commutative) diagram (∗) …
and any morphism φ′ : Y → X with d(φ, φ′) < δ, there exists a unique
morphism ψ′ : V → U with d(ψ, ψ′) < ε for which the following diagram is
also cartesian (resp. commutative)". Here (∗) is the square with
`φ : Y → X`, `ψ : V → U`, `g : V → Y` and `f : U → X`.

## The statement

`Langlands.Analytic.SaturatedAtlasPresentation.QuasiEtaleActionLiftStatement K`,
for a complete ultrametric normed field `K`, is the proposition: for every
topological group `G` (in a fixed universe), all analytic spaces `X`, `U` of
`LocalizedCategory.{u, v, v}`, every action `ρ : G →* Aut X` and every morphism
`f : U ⟶ X`, if

- the underlying space of `X` is Hausdorff,
- `ρ` is continuous (the Library's `IsContinuousAction`),
- `f` is quasi-étale (the Library's `quasiEtale`), and
- `U` is compact (the Library's `IsCompactSpace`: compact and Hausdorff),

then there is a lift `ActionLift ρ f` (an open subgroup `H`, a continuous
action of `H` on `U` and `H`-equivariance of `f`; Library
`LocalActionLifts`), and any two lifts `a`, `b` agree on an open subgroup
(`a.AgreeOn b N` for some `N`).

## Correspondence with the sources

The existence part is the sentence "the action of G on X extends … to a
continuous action of some open subgroup G_U ⊂ G on U". The uniqueness part
expresses "in a canonical way" as it is used later on the same page: two
extensions coincide on an open subgroup. It follows from the uniqueness in
the Key Lemma, by the following derived argument (not formalized). Apply the
Key Lemma to the commutative square with `Y = V = U`, `g = ψ = 1_U` and
`φ = f`. For `h` close to `1`, `φ′ = ρ(h) ∘ f` is `δ`-close to `f`, and both
`a(h)` and `b(h)` are `ε`-close to `1_U` and satisfy `f ∘ a(h) = ρ(h) ∘ f`, so
they are equal. The elements of both subgroups where `a` and `b` agree form a
subgroup containing a neighbourhood of `1`, hence an open subgroup.

Conventions, as in the Library modules used: spaces are Hausdorff (both
sources assume it; it is imposed on `X` and contained in compactness of `U`);
the group `Aut X` of `LocalizedCategory` is Berkovich's group `G_K(X)` of
`K`-automorphisms, so semilinear actions are not covered; continuity is the
Library's `IsContinuousAction` through the test relations of `𝔈(X)`.

## Scope

Only the proposition is defined. Its proof (the Key Lemma and the deduction
above), the version for distinguished étale morphisms, and the canonical
choice of `G_U` are not provided here.
