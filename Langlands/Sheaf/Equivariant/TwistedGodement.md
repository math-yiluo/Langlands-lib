# Godement constructions on a twisted site

Author: Worker 26. Uses the published twisted category
`Langlands.Sheaf.Equivariant.TwistedOver` (Worker 26), Worker 13's Godement
construction on a site with points `Langlands.Sheaf.Godement` and iterated-cokernel
complexes `Langlands.Cohomology.CokernelComplex`, and the discrete part of module
sheaves `Langlands.Sheaf.Equivariant.LocalActionDiscretePart` (Worker 26). From
Mathlib it uses right Kan extensions, the pushforward of sheaves along a cocontinuous
functor (`Functor.sheafPushforwardCocontinuous`), and its adjunction with the
pushforward along a continuous functor (`Functor.sheafAdjunctionCocontinuous`).

## Purpose

Berkovich (§1.5) builds the Godement resolution of an étale sheaf on `X(G)` from a
family of geometric points `x̄ᵢ`: `𝒞⁰(F) = ν_* ν^*(F)` for the morphism of sites
`ν : Top(I) → X(G)_ét`, with `F → 𝒞⁰(F)` the adjunction morphism, and
`𝒞^{m+1}(F) = 𝒞⁰(Coker d^{m-1})`. Harris (1999, p.304) uses the resulting
embedding `T → F(T)`. This module builds the construction on the twisted site of
`TwistedOver`. There, sheaves are sheaves over `X` with an action of `G` with the
discrete topology. A second version works among the discrete sheaves of a local
action system.

## Setting

- `C : Type u` with `Category.{v} C`, a morphism property `P` with
  `[P.RespectsIso]`, an object `X`, a group `G : Type uG` and `ρ : G →* Aut X`.
  `J` is a topology on `P.Over ⊤ X` with `[IsTranslationInvariant J]`, and
  `twistedTopology ρ J` is the twisted topology.
- `A` is a coefficient category. The induction functor needs the right Kan
  extensions along `(ι P ρ).op`. They are an instance argument
  `[∀ F, (ι P ρ).op.HasPointwiseRightKanExtension F]`.
  `hasPointwiseRightKanExtension_moduleCat` proves this argument for module
  categories `ModuleCat.{max u v uG} R`, by instance inference.

## Restriction and induction

- `restriction ρ J A` (from `TwistedOver`) restricts a sheaf on the twisted site to
  `P.Over ⊤ X` along the continuous inclusion `ι`. `restriction_faithful`: it is
  faithful, because every object of the twisted category is the image of an object
  of `P.Over ⊤ X`.
- `induction ρ J A : Sheaf J A ⥤ Sheaf (twistedTopology ρ J) A` is Mathlib's
  pushforward along the cocontinuous functor `ι`: the right Kan extension of
  presheaves along `ι.op`, which preserves sheaves.
- `restrictionAdjunction ρ J A : restriction ⊣ induction` is Mathlib's
  `sheafAdjunctionCocontinuous`. `induction` is a right adjoint (instance). Since
  restriction is faithful, the unit is a monomorphism
  (`mono_restrictionAdjunction_unit_app`).

Not formalized but useful for intuition: a twisted arrow `ιV ⟶ U` with twist `g`
factors uniquely through the object `g⁻¹U`. So the pointwise formula gives
`(induction S)(U) ≅ ∏_{g ∈ G} S(g⁻¹U)`.

## The Godement functor of the twisted site

Let `points : I → J.Point.{w}` be a family of Mathlib points of `J`, with
`I : Type wI`, and assume `A` has products of sizes `w` and `wI` and colimits of
size `w` (the hypotheses of Worker 13's module).

- `twistedZeroFunctor ρ J points A` is
  `restriction ⋙ Godement.zeroFunctor points A ⋙ induction`. It sends `F` to the
  induction of `∏ᵢ skyscraperᵢ(fiberᵢ(F|_X))`, where `F|_X` is the restriction.
- `twistedCoaugmentation ρ J points A : 𝟭 ⟶ twistedZeroFunctor`. Its component at
  `F` is the unit of `restrictionAdjunction`, followed by the induction of Worker
  13's coaugmentation of `F|_X` (`twistedCoaugmentation_app`). The coaugmentation
  of `J` is the product of the units of the fiber–skyscraper adjunctions. So this
  is the unit of the composite adjunction, from the fibers of `F|_X` at the points
  to the twisted site.
- `mono_twistedCoaugmentation_of_jointlyFaithful`: if the sheaf fiber functors of
  the points are jointly faithful, then each component is a monomorphism. The
  proof composes the monic unit with the induction of Worker 13's monic
  coaugmentation; induction preserves monomorphisms as a right adjoint.
- With `[Abelian A]` and `[HasSheafify (twistedTopology ρ J) A]`, the sheaves on
  the twisted site form an abelian category. `twistedComplexFunctor` is the cochain
  complex of iterated cokernels (`CokernelComplex.functor`) of the twisted
  coaugmentation, and `twistedComplex F` its value at `F`.
  `twistedAugmentation F : F ⟶ (twistedComplex F).X 0` is the coaugmentation, and
  `twistedAugmentation_d` says its composite with the first differential is zero.

## Discrete sheaves

Let `G` be a topological group, `L` a local action system on the twisted category,
`points : I → J.Point.{w}` with `I : Type w`, and `R : Type w` a commutative
ring. Assume the Kan-extension hypothesis for `ModuleCat.{w} R` and
`[L.HasFiniteEquivariantRefinements (twistedTopology ρ J)]`, under which
`LocalActionDiscretePart` constructs the discrete part `discreteCoreflector`,
right adjoint to the inclusion of discrete sheaves (`discreteAdjunction`).

- `discreteZeroFunctor ρ J L points R` is the composite of three functors on
  discrete sheaves: inclusion, then `twistedZeroFunctor`, then the discrete part.
- `discreteCoaugmentation ρ J L points R : 𝟭 ⟶ discreteZeroFunctor`. Its
  component at `F` is the unit of `discreteAdjunction`, an isomorphism because the
  inclusion is fully faithful. It is followed by the discrete part of the twisted
  coaugmentation.
- `mono_discreteCoaugmentation_of_jointlyFaithful`: with jointly faithful fibers,
  each component is a monomorphism. The discrete part preserves monomorphisms as a
  right adjoint.
- With `[HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]`, discrete sheaves form
  an abelian category (`LocalActionDiscretePart`). `discreteComplexFunctor` is
  the cochain complex of iterated cokernels of the discrete coaugmentation.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished
1995–1996 manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
(folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`),
§1.5, printed p.10 = PDF p.10, read in the original (rendered page) by Worker 26:

> Suppose we are given a set `I` and a surjective map `I → X : i ↦ xᵢ`. We endow
> `I` with the discrete topology and fix for each `i ∈ I` a geometric point `x̄ᵢ`
> over `xᵢ`. This gives rise to a morphism of sites `ν : Top(I) → X(G)_ét`. For an
> étale abelian sheaf `F` on `X(G)`, let `𝒞^·(F)` denote the right resolution of
> `F` constructed as follows:
> (a) `𝒞⁰(F) = ν_*ν^*(F)`, and `d^{-1} : F → 𝒞⁰(F)` is the adjunction morphism;
> (b) if `m ≥ 0`, then `𝒞^{m+1}(F) = 𝒞⁰(Coker d^{m-1})`, and `d^m` is the
> canonical morphism `𝒞^m(F) → 𝒞^{m+1}(F)`.

Harris, *Galois properties of cohomological automorphic forms on GL(n)* (1999),
registered as `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, §2,
printed p.304: "Berkovich constructs an embedding T → F(T), … and which is
acyclic for the functor RΓ_c".

## Provenance and correspondence

This module is derived infrastructure; it is the twisted-site form of Berkovich's
construction.

- The morphism of sites `ν` factors through `X_ét`. Its inverse image takes the
  fibers of the underlying sheaf at the points. Its direct image is the product of
  skyscrapers, followed by the direct image from `X` to the `G`-equivariant site.
  In the twisted model, the last step is the right adjoint `induction` of
  `restriction`. So `twistedZeroFunctor` is `ν_*ν^*`, and `twistedCoaugmentation`
  is the adjunction morphism of the composite adjunction. Berkovich's surjective
  family of geometric points is replaced by a family of Mathlib points with jointly
  faithful fiber functors. That hypothesis is what monicity uses.
- For a topological group, Berkovich's sheaves on `X(G)` correspond to the
  discrete `G`-sheaves (Theorem 1.4.2, not formalized here). Among discrete
  sheaves, the right adjoint of the fibers is the discrete part of `ν_*`, so
  `discreteZeroFunctor` is the corresponding construction.
- Berkovich's properties of `𝒞^m(F)` (flabbiness, exactness of `F ↦ 𝒞^m(F)`, split
  fibers), Proposition 1.5.1 (softness) and the acyclicity for `RΓ_c` used by
  Harris are not proved here. Nor is the identification of the restriction of the
  twisted complex with Worker 13's complex of `J`.

## Not formalized here

Analytic instances need families of geometric points of Worker 21's étale sites
(open). The comparison with Berkovich's site `X(G)_ét` and any acyclicity
statement are also not formalized.
