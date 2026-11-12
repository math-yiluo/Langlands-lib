# ℓ-divisible systems of discrete Godement resolutions on a twisted site

Author: Worker 26. Applies Worker 61's generic constructions for a coaugmented exact
endofunctor to Worker 26's discrete Godement functor on a twisted site. Uses
`Langlands.Cohomology.DivisibleSystem` (`DivisibleSystem`, `map`, `obj`, `degree`),
`Langlands.Cohomology.DivisibleSystem.Coaugmented` (`coaugmentation`,
`residualSystem`, `termSystem`), `Langlands.Cohomology.DivisibleSystem.Resolution`
(`resolutionSystem`, `resolutionSystemDegreeIso`, `resolutionSystemObjIso`,
`resolutionSystem_obj_exactAt`) and Worker 26's
`Langlands.Sheaf.Equivariant.TwistedGodement` (`discreteZeroFunctor`,
`discreteCoaugmentation`, `mono_discreteCoaugmentation_of_jointlyFaithful`,
`discreteComplexFunctor`). From Mathlib it uses
`Functor.additive_of_preservesBinaryBiproducts` and
`preservesBinaryBiproducts_of_preservesBinaryProducts`.

All names are in the namespace `Langlands.Cohomology.DivisibleSystem`.

## Setting

The variables are those of the section `Discrete` of `TwistedGodement`, in the same
order. `G` acts on `X : C` through `ρ : G →* Aut X`. `J` is a translation-invariant
topology on `P.Over ⊤ X`, and `G` is a topological group. `L` is a local action system
on the twisted category with finite equivariant refinements for the twisted topology.
`points : I → J.Point.{w}` is a family of points of `J`, and `R : Type w` is a
commutative ring. The twisted-site Godement construction needs right Kan extensions
along the inclusion and sheafification of `R`-module presheaves on the twisted site.

`L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)` is the abelian category of
discrete sheaves of `R`-modules: Berkovich's discrete sheaves, Harris's "étale
sheaves in smooth modules". `F = discreteZeroFunctor ρ J L points R` is the degree-zero
discrete Godement functor, the discrete part of `ι_* C⁰(ι^* -)`, and
`η = discreteCoaugmentation ρ J L points R : 𝟭 ⟶ F` is its coaugmentation.

`ℓ`-divisible systems are those of the published `DivisibleSystem`, with its
conventions. An inverse system `T m`, `m : ℕ`, has inclusions `i : T m' ⟶ T m` and
projections `j : T m ⟶ T (m - m')`. `ℓ ^ m` vanishes on `T m`, and
`0 ⟶ T m' ⟶ T m ⟶ T (m - m') ⟶ 0` is short exact (Harris (2.1)). `i` is a kernel of
`ℓ ^ m'` on `T m`, and a flatness condition replaces Harris's freeness over
`ℤ/ℓ^m`. The index starts at `0`, with `T 0` zero.

## Hypotheses

Exactness of `F` is not proved. It enters as instance arguments
`[PreservesFiniteLimits F]` and `[PreservesFiniteColimits F]`. This is Harris's
Fact 3; Berkovich derives it from the explicit stalks of `ν_* ν^*`. For the site
Godement functor it is part of the open statement
`Langlands.Sheaf.Godement.ModuleZeroFunctorExactnessStatement` (Worker 3). The
constructions in the section `Exact` also take
`hpoints : JointlyFaithful (fun i => (points i).sheafFiber)`. This makes the
coaugmentation monic (published `mono_discreteCoaugmentation_of_jointlyFaithful`).

## Declarations

- `discreteZeroFunctor_additive`: if `F` preserves finite limits it is additive. This
  is the standard argument: binary products are biproducts in an abelian category,
  and `F` preserves them.
- `discreteGodementImageSystem T`: for an `ℓ`-divisible system `T` of discrete sheaves
  and exact `F`, the images `F(T m)` with the maps `F(i)` and `F(j)` (published `map`).
  This is Harris's Fact 4.
- `discreteGodementCoaugmentation T`: the embeddings `b_m = η (T m) : T m ⟶ F(T m)` as
  a morphism of `ℓ`-divisible systems `T ⟶ discreteGodementImageSystem T`.
- `discreteGodementResidualSystem T hpoints q`: in degree `0` the system `T`, and in
  degree `q + 1` the cokernel system of the coaugmentation of the degree-`q` system.
  For `q = 0` this is Harris's `{coker b_m}`, obtained "from Facts 3 and 4 and the
  snake lemma" (published `cokernelSystem`).
- `discreteGodementTermSystem T hpoints q`: the term system `F^q`, that is, `F`
  applied to the residual system in degree `q`.
- `discreteGodementResolutionSystem T hpoints`: the `ℓ`-divisible system of cochain
  complexes `F^0 ⟶ F^1 ⟶ ⋯` with the differentials of the published
  `termDifferential`.
- `discreteGodementResolutionSystemDegreeIso`: its degree-`q` system is the term
  system `F^q`.
- `discreteGodementResolutionSystemObjIso T hpoints m`: its level `m` is the published
  discrete Godement complex `(discreteComplexFunctor ρ J L points R).obj (T.obj m)` of
  `T m`.
- `discreteGodementResolutionSystem_obj_exactAt`: each level is exact in every
  positive degree. Exactness of `0 ⟶ T m ⟶ F^0 ⟶ F^1` is not restated here.

## Provenance and scope

Harris, *Galois properties of cohomological automorphic forms on GL(n)* (1999), §2,
printed p.304 = PDF p.6, read in the original by Worker 26 (checked against the page
image):

> **Fact 3.** The functor `T → F(T)` is exact.
>
> **Fact 4.** Suppose `{T_m}` is an `ℓ`-divisible system of `S(ẽ)`-modules over
> `U(ẽ)`. Then `{F(T_m)}` is again an `ℓ`-divisible system of `S(ẽ)`-modules over
> `U(ẽ)`, with respect to the morphisms `F(i)` and `F(j)`.
>
> Let `b_m : T_m → F(T_m)` denote the canonical embedding. It follows from Facts 3
> and 4 and the snake lemma that `{coker b_m}` is again an `ℓ`-divisible system of
> `S(ẽ)`-modules over `U(e, N)`. By induction, we thus have
>
> **Lemma 2.2.** For each `m` the constant sheaf `ℤ/ℓ^mℤ` admits an `RΓ_c`-acyclic
> resolution `0 → ℤ/ℓ^mℤ → F_m^0 → F_m^1 → ⋯ → F_m^q → ⋯` such that, for each `q`,
> `{F_m^q}` is an `ℓ`-divisible system of `S(ẽ)`-modules over `U(ẽ)`.

`U(e, N)` is printed so; Harris's `F(T)` is Berkovich's `b^* ν_* ν^*` (Harris p.304).
In the twisted-site model, discrete sheaves on the twisted site stand for Harris's
étale sheaves in smooth modules over `U(ẽ)`. `F` stands for Berkovich's degree-zero
Godement functor; `TwistedGodement` explains the correspondence. This module carries
out the inductive construction for an arbitrary `ℓ`-divisible system `T` in place of
the constant sheaves `ℤ/ℓ^mℤ`. It is a derived specialization: the construction is
Worker 61's, and the functor is Worker 26's.

Not constructed or proved here: exactness of `F` (Fact 3); `RΓ_c`-acyclicity of the
terms (Berkovich Prop. 1.5.1); the constant `ℓ`-divisible system `ℤ/ℓ^mℤ` on a
twisted site; the truncations of Lemma 2.2 bis; the section complexes and Mittag-Leffler
argument of (2.3)–(2.8); and any analytic instance.

Universes: `C : Type u` with morphisms in `v`, `G : Type uG`, and `I`, `R` and the
points in `w`.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`.
