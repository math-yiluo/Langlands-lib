# Truncated discrete Godement resolutions and compact cohomology on a twisted site

Author: Worker 26. This module specializes the generic constructions of Lemma 2.2 bis and
(2.3) to the discrete Godement functor and the smooth compactly supported sections on a
twisted site. It uses:

- Worker 26's `Langlands.Cohomology.DivisibleSystem.TwistedGodement`:
  `discreteZeroFunctor_additive` and `discreteGodementResolutionSystem`.
- Worker 26's `Langlands.Cohomology.DivisibleSystem.AcyclicTruncation`:
  `truncatedResolutionAugmentation`, `truncatedResolutionAugmentation_quasiIso`,
  `isZero_rightDerived_truncatedResolutionSystem_obj_X`, `acyclicTruncatedSectionsSystem` and
  `acyclicTruncatedSectionsHomologyIso`.
- Worker 61's `Langlands.Cohomology.DivisibleSystem.Truncation`: `truncatedResolutionSystem`,
  `truncatedResolutionHom`, `truncatedResolutionHom_quasiIso` and
  `isZero_truncatedResolutionSystem_obj_X`.
- Worker 26's `Langlands.Sheaf.Equivariant.TwistedGodement`: `discreteZeroFunctor`,
  `discreteCoaugmentation` and `mono_discreteCoaugmentation_of_jointlyFaithful`.
- Worker 26's `Langlands.Sheaf.Equivariant.TwistedCompactSupport`: `PointEquivariance`,
  `discreteCompactSections` and `discreteCompactDerived`.
- `Langlands.Cohomology.AcyclicResolution.Comparison`: `AcyclicResolution.resolutionComparison`.
- Worker 26's `Langlands.Sheaf.Equivariant.LocalActionDiscretePart`, through its instance
  `discreteSheaf_enoughInjectives`: discrete sheaves have enough injectives when sheaves of
  modules on the twisted site do.

All names are in the namespace `Langlands.Cohomology.DivisibleSystem`.

## Setting

The variables are those of `DivisibleSystem.TwistedGodement`, in the same order. `G` acts
on `X : C` through `ρ : G →* Aut X`. `J` is a translation-invariant topology on `P.Over ⊤ X`,
and `G` is a topological group. `L` is a local action system on the twisted category with
finite equivariant refinements for the twisted topology. `points : I → J.Point.{w}` is a
family of points of `J` with `I : Type w`, and `R : Type w` is a commutative ring.
`F = discreteZeroFunctor ρ J L points R` is the degree-zero discrete Godement functor on
discrete sheaves of `R`-modules on the twisted site. `η = discreteCoaugmentation ρ J L points R`
is its coaugmentation. `T` is an `ℓ`-divisible system of discrete sheaves of `R`-modules,
and `D : ℕ` is the truncation degree.

The section `Compact` adds the data of the published compactly supported sections:
`P` contains identities, `P.Over ⊤ X` is locally `w`-small, `G` is a topological group, `J`
has sheafification for `R`-modules, and sheaves of `R`-modules on the twisted site have enough
injectives. `Ψ : I' → J.Point.{w}` is a second family of points. It is indexed by a
topological space `I'` on which `G` acts by continuous maps (`ContinuousConstSMul`), and
`E : PointEquivariance ρ Ψ` identifies the fibers along the action. The Godement points and
the points defining compact support are independent families; in an application they may be
taken to be the same points. `discreteCompactSections J R L E` is the functor of smooth
compactly supported global sections (Berkovich's `Γ_{c,X{G}}`), with values in smooth
`R`-representations of `G`. `discreteCompactDerived J R L E n` is its `n`-th right derived
functor, Berkovich's `H^n_c(X{G}, -)`.

## Hypotheses

All of these are explicit; none is proved here.

- `[PreservesFiniteLimits F]` and `[PreservesFiniteColimits F]`: exactness of the discrete
  Godement functor, Harris's Fact 3, as in `DivisibleSystem.TwistedGodement`.
- `hpoints : JointlyFaithful (fun i => (points i).sheafFiber)`: the Godement points detect
  morphisms. This makes the coaugmentation monic.
- `hF`: for every discrete sheaf `M` and every `r`, `discreteCompactDerived J R L E (r + 1)`
  vanishes on `F(M)`. This is Harris's statement that `F(T)` is `RΓ_c`-acyclic (p.304).
- `hT`: for all `m` and `n > D`, `discreteCompactDerived J R L E n` vanishes on `T m`. This is
  Harris's Fact 2 (p.303) for the levels of `T`, over the whole space.

## Declarations

Section `Truncation`:

- `discreteGodementTruncatedResolutionSystem ρ J L points R T hpoints D`: Harris's
  `G^• = τ_{≤ D+1}(F^•)`, the published `truncatedResolutionSystem` for `F` and `η`. Its
  degree-`q` terms are the Godement term systems for `q ≤ D`, the residual system `R (D + 1)`
  in degree `D + 1`, and zero above.
- `discreteGodementTruncatedResolutionHom`: the inclusion of `G^•` into the discrete Godement
  resolution system `discreteGodementResolutionSystem`.
- `quasiIso_discreteGodementTruncatedResolutionHom`: at every level this inclusion is a
  quasi-isomorphism.
- `isZero_discreteGodementTruncatedResolutionSystem_obj_X`: every level is zero in degrees
  above `D + 1`.
- `discreteGodementTruncatedAugmentation ρ J L points R T hpoints D m`: the augmentation
  `T m ⟶ G^•_m`, from `T m` placed in degree `0`.
- `quasiIso_discreteGodementTruncatedAugmentation`: the augmentation is a
  quasi-isomorphism, so `G^•_m` is a finite-length resolution of `T m`.

Section `Compact`:

- `isZero_discreteCompactDerived_truncatedResolutionSystem_obj_X` (needs `hF`, `hT`): every
  term of every level of `G^•` is acyclic for `discreteCompactSections J R L E`. Together with
  the previous item this is Lemma 2.2 bis for `T` on the twisted site.
- `discreteGodementTruncatedCompactSectionsSystem ρ J L points R T hpoints D E hF hT`: the
  `ℓ`-divisible system of finite-length complexes `Γ_c(G^•_m)` of smooth representations,
  the generic `acyclicTruncatedSectionsSystem`. Its divisible-system structure includes the
  surjectivity of the projections that Harris checks for Lemma 2.2 bis.
  `discreteGodementTruncatedCompactSectionsSystem_obj` states that level `m` is
  `discreteCompactSections J R L E` applied degreewise to `G^•_m` (by `rfl`).
- `discreteGodementTruncatedCompactHomologyIso ρ J L points R T hpoints D E hF hT m n`:
  Harris's (2.3) on the twisted site, `Hⁿ(Γ_c(G^•_m)) ≅ H^n_c(T m)`, the latter being
  `(discreteCompactDerived J R L E n).obj (T.obj m)`.
  `discreteGodementTruncatedCompactHomologyIso_hom` states that its forward map is the
  published comparison map `AcyclicResolution.resolutionComparison` of the augmentation
  (by `rfl`).
- `isZero_discreteGodementTruncatedCompactSectionsSystem_homology`: `Hⁿ(Γ_c(G^•_m)) = 0` for
  `n > D`.

## Proofs

Every declaration applies the generic result of `DivisibleSystem.Truncation` or
`DivisibleSystem.AcyclicTruncation` to `F`, `η` and `Φ = discreteCompactSections J R L E`.
The additivity of `F` (`discreteZeroFunctor_additive`) and the monicity of `η`
(`mono_discreteCoaugmentation_of_jointlyFaithful`, from `hpoints`) are supplied locally
with `haveI`, as in `DivisibleSystem.TwistedGodement`. `discreteCompactDerived J R L E n` is
by definition the right derived functor of `discreteCompactSections J R L E`, so `hF` and
`hT` are the hypotheses of the generic results. The left exactness of `Φ` needed there is the
published instance `discreteCompactSections_preservesFiniteLimits`. The vanishing of the
cohomology above `D` transports `hT` along the (2.3) isomorphism.

## Provenance and scope

Harris, *Galois properties of cohomological automorphic forms on GL(n)* (1999), §2, read in
the original by Worker 26 (checked against the page images).

Printed p.303 = PDF p.5:

> **Fact 2.** There is an integer `D > 0` such that `H^q_c(U, T) = 0` for all `q > D` and any
> étale morphism `U → U(ẽ)`.

Printed p.304 = PDF p.6:

> For any étale sheaf `T` in smooth `ℤ/ℓ^mℤ[S(ẽ)]`-modules over `U(ẽ)`, Berkovich constructs
> an embedding `T ↪ F(T)`, where `F(T)` is again an étale sheaf in smooth
> `ℤ/ℓ^mℤ[S(ẽ)]`-modules over `U(ẽ)`, and which is acyclic for the functor `RΓ_c`:
> `H^q_c(U(ẽ)_F̄, F(T)) = 0` for `q > 0`.

Printed p.305 = PDF p.7:

> We let `G_m^• = τ^{≤D+1}(F_m^•)`. It is easy to see that truncating in degree `D + 1`
> rather than `D` guarantees that
>
> **Lemma 2.2 bis.** For each `m` the constant sheaf `ℤ/ℓ^mℤ` admits an `RΓ_c`-acyclic
> resolution of finite length `0 → ℤ/ℓ^mℤ → G_m^0 → G_m^1 → ⋯ → G_m^q → ⋯ → G_m^{D+1} → 0`
> such that, for each `q`, `{G_m^q}` is an `ℓ`-divisible system of `S(ẽ)`-modules over
> `U(ẽ)`.
>
> [...] Thus Lemma 2.2 provides an isomorphism
>
> (2.3) `H^q_c(U(ẽ)_F̄, ℤ/ℓ^mℤ) ⥲ Z_m^q / B_m^q = H^q(G_m^•(U(ẽ)_F̄))`

This module is derived. It is the twisted-site case of `DivisibleSystem.AcyclicTruncation`.
Discrete sheaves on the twisted site stand for Harris's étale sheaves in smooth modules
over `U(ẽ)`, and `discreteCompactDerived` stands for `H^q_c(U(ẽ)_F̄, -)` with its action of
`G` (Harris's `S(ẽ)`). `DivisibleSystem.TwistedGodement` and
`Sheaf.Equivariant.TwistedCompactSupport` explain the model. The module treats an arbitrary
`ℓ`-divisible system `T` in place of `ℤ/ℓ^mℤ`. The isomorphism goes from the cohomology of
the section complexes to `H^n_c`, the inverse of Harris's printed direction.

Not constructed or proved here: exactness of `F` (Fact 3); the acyclicity `hF`; Fact 2; the
constant system `ℤ/ℓ^mℤ` on a twisted site; Harris's `S(ẽ)`, `U(ẽ)` and the analytic site;
the `H`-invariants after (2.3); and (2.4)–(2.8).

Universes: `C : Type u` with morphisms in `v`, `G : Type uG`, `I`, `R` and the points in `w`,
and `I' : Type uI`.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`.
