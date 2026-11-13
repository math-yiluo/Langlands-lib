# Berkovich's comparison `H^q(X{G}, F) ≅ H^q(X, b^*F)` for compact `X` (quasi-étale)

Author: Worker 16.

This module defines one proposition,
`Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.AnalyticQuasiEtaleGlobalComparisonStatement`.
It is the quasi-étale case of Berkovich's Theorem 1.6.1(ii): if a topological
group `G` acts continuously on a compact analytic space `X`, then for every
quasi-étale `G`-sheaf `F` the comparison maps `H^q(X{G}, F) → H^q(X, b^*F)` are
isomorphisms in every degree `q`. It is a theorem-statement definition, not a
proof. The isomorphism is the conclusion; it is not supplied as data or as a
hypothesis. The comparison map itself is Worker 26's published construction.

## Objects

All objects are imported from Worker 26's module
`Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleCohomology` (namespace
`Langlands.Sheaf.Equivariant.Analytic`) and the modules it builds on, mainly
Worker 26's `AnalyticGSheaves` and `TwistedGlobalSections` and Worker 21's
analytic spaces, quasi-étale site and continuous actions.

- `K : Type u` is a complete ultrametric normed field (`NormedField`,
  `IsUltrametricDist`, `CompleteSpace`). `X` is an object of Worker 21's
  category of analytic spaces `LocalizedCategory.{u, v, v} (K := K)`.
- `G : Type z` is a topological group (`IsTopologicalGroup`) and
  `ρ : G →* Aut X` an action of `G` on `X` by automorphisms.
- `R : Type (max u (v + 1) uL)` is a commutative ring. Sheaves take values in
  `R`-modules. This coefficient universe is the one of Worker 26's derived
  functors.
- `quasiEtaleGSheafCohomology ρ R q` is Berkovich's `H^q(X{G}, F)`. It is the
  `q`-th right derived functor of `quasiEtaleGSheafSections ρ R`, Berkovich's
  `Γ_{X{G}}`: the smooth part of the representation of `G` on the global
  sections of `F`. Derived functors are computed with injective resolutions in
  the category of quasi-étale `G`-sheaves `QuasiEtaleGSheaf ρ`, and the values
  are smooth representations of `G`.
- `quasiEtaleCohomology X R q` is `H^q(X, -)`, the `q`-th right derived functor
  of the sections over `X` of `R`-module sheaves on the quasi-étale site of `X`.
- `quasiEtaleComparison ρ R q` is the comparison
  `H^q(X{G}, F) → H^q(X, b^*F)`. It is a natural transformation from
  `quasiEtaleGSheafCohomology ρ R q ⋙ smoothForget R G` (the underlying modules
  of `H^q(X{G}, F)`) to
  `quasiEtaleGSheafRestriction ρ R ⋙ quasiEtaleCohomology X R q`. Here
  `quasiEtaleGSheafRestriction` is Berkovich's `b^*`. Worker 26 defines the map
  as the base change, along the exact functors `b^*` and `smoothForget`, of the
  inclusion `Γ_{X{G}}(F) ⊆ (b^*F)(X)` of smooth global sections into all
  global sections.
- `IsCompactSpace X`, from Worker 21's `LocalActionLifts`, says that the
  underlying topological space of `X` is compact and Hausdorff.
- `IsContinuousAction ρ`, from Worker 21's `ContinuousAnalyticAction`, is
  Berkovich's continuity of an action: for every test triple `τ` (Berkovich's
  `ε ∈ E(X)`), the preimage under `ρ` of the set of automorphisms within `τ` of
  the identity is a neighbourhood of `1` in `G`.

## The proposition

| Declaration | Asserted conclusion |
| --- | --- |
| `AnalyticQuasiEtaleGlobalComparisonStatement X G ρ R` | If `IsCompactSpace X` and `IsContinuousAction ρ`, then for every `q : ℕ` the natural transformation `quasiEtaleComparison.{u, v, uL} ρ R q` is an isomorphism (`IsIso`). |

`IsIso` of a natural transformation means that it is a natural isomorphism.
So the proposition asserts that each map `H^q(X{G}, F) → H^q(X, b^*F)` is a
bijection, for every quasi-étale `G`-sheaf `F` of `R`-modules. These maps are
natural in `F` and are the comparison maps that Worker 26 constructed.
Isomorphisms are not merely asserted to exist.

Compactness and continuity are hypotheses of the proposition, not binders of
the definition. The definition has two further instance binders, which are
needed to define the source `H^q(X{G}, -)`. They are the same as in Worker
26's declarations.

- `[Small.{max u (v + 1) uL} G]` is a size condition. It makes the twisted
  quasi-étale site essentially small, which the published sheafification and
  enough-injectives results on that site use. It holds, for example, when `G`
  lies in a universe at most `max u (v + 1) uL`.
- `[(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]`
  says that every covering sieve of a compact quasi-étale object with a lift
  of the action contains a finite family of arrows from such objects, each
  locally equivariant, that generates a covering sieve. Worker 26 uses it to
  make quasi-étale `G`-sheaves an abelian category with enough injectives. It
  is not proved in the Library. Geometrically it combines the finiteness of
  quasi-étale coverings of compact spaces with Berkovich's Key Lemma on lifts.
  If it failed, the proposition could not be formed for that action.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished
1995–1996 manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
(folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`).
Printed page numbers equal PDF page numbers.

- Theorem 1.6.1, p.13: "Let `X` be a `G`-space. Then [...] (ii) if `X` is
  compact, then for any quasi-étale (resp. étale) abelian sheaf `F` on `X(G)`
  one has `H^q(X{G}, F) ⥲ H^q(X, b^*F)` and, in particular, there is a
  spectral sequence `E_2^{p,q} = H^p(G, H^q(X, b^*F)) ⟹ H^{p+q}(X(G), F)`".
- §1.1, p.1: "In what follows all analytic spaces considered are assumed to be
  Hausdorff." Hence `IsCompactSpace X` (compact and Hausdorff) for "`X` is
  compact".
- §1.1, pp.1–2: the topology on the automorphism group `G(X)` is defined by the
  subgroups `G_ε(X)`, `ε ∈ E(X)`. "We say that the action of a topological
  group `G` on an analytic space is continuous if the induced homomorphism
  `G → G(X)` is continuous." "An analytic space `X` endowed with a continuous
  action of a topological group `G` will be called a `G`-space." Hence
  `IsContinuousAction ρ`. For a homomorphism of groups, continuity is
  continuity at `1`, which is what `IsContinuousAction` states.
- §1.2, pp.4–5: `Γ_{X{G}}(F) = lim_→ F(X_{G/N}(G))` over open subgroups `N`,
  and `H^q(X{G}, F)` are the higher direct images of `Γ_{X{G}}`.
- Definition 1.4.1 and Theorem 1.4.2, pp.7–8: quasi-étale `G`-sheaves (the
  action of `G_U` on `F(U)` is discrete for compact quasi-étale `U → X`), and
  the equivalence between quasi-étale sheaves on `X(G)` and quasi-étale
  `G`-sheaves induced by `b`.

## Correspondence and modelling choices

- Berkovich's quasi-étale abelian sheaves on `X(G)` are modelled by Worker
  26's quasi-étale `G`-sheaves `QuasiEtaleGSheaf ρ`, through Theorem 1.4.2, as
  in all of Worker 26's quasi-étale modules. Theorem 1.4.2 is not formalized.
- Berkovich works with abelian sheaves. Here sheaves take values in
  `R`-modules for an arbitrary commutative ring `R` in the coefficient universe;
  abelian sheaves are the case `R = ULift ℤ`. The statement for all `R` is the
  natural generalization. Berkovich's argument (below) uses nothing specific
  to abelian groups.
- Only the isomorphism of Theorem 1.6.1(ii) is stated. Its spectral sequence,
  the étale case ("resp. étale"), part (i) for paracompact `X` and part (iii)
  are not stated. The Library has no invariant cohomology `H^q(X(G), F)` and no
  étale cohomology of `G`-sheaves to state them with.
- The hypotheses are exactly Berkovich's: `X` is a `G`-space and `X` is
  compact. The two instance binders are needed only to form the source
  category and its derived functors; they are not hypotheses of Berkovich's
  theorem.

## Why the proposition is expected to hold

Berkovich proves the quasi-étale case on p.13. Let `F` be a quasi-étale
injective sheaf on `X(G)` and `X` compact. Then `H^q(X, b^*F) = 0` for `q ≥ 1`.
It suffices to check that Čech cohomology `Ȟ^q(U, b^*F)` vanishes for finite
quasi-étale coverings `U = {U_i → X}` by compact `U_i`. For a sufficiently small
open subgroup `N` each `U_i → X` is an `N`-morphism, so `U` gives a covering
`U(N)` of `X(N)`, and `Ȟ^q(U(N), F) = 0` because the pullback of `F` to `X(N)`
is injective. Finally `Ȟ^q(U, b^*F)` is the inductive limit of these groups over
`N`. So `b^*` sends injectives to `Γ(X, -)`-acyclic sheaves. In degree zero,
every global section of `b^*F` is smooth when `X` is compact. Hence
`Γ_{X{G}}(F) = (b^*F)(X)`, and since `b^*` is exact the derived functors agree.

In degree zero the Library model behaves the same way. When `X` is compact and
`ρ` is continuous, the identity of `X`, with the whole group `G` acting by `ρ`,
is an admissible lift in `compactLiftSystem ρ`. The discreteness condition of
`QuasiEtaleGSheaf ρ` then says that every global section is fixed by an open
subgroup. So the inclusion `Γ_{X{G}}(F) ⊆ (b^*F)(X)` is an equality, and
`quasiEtaleComparison ρ R 0` is an isomorphism. In positive degrees the
argument needs Čech cohomology and Berkovich's Key Lemma on lifts, which the
Library does not yet have.

## Relation to the compactly supported comparison

Theorem 1.6.1(ii) concerns ordinary cohomology. Its compactly supported
analogue, Berkovich's Corollary 1.5.2(i), is stated in the manuscript only for
étale sheaves. On the Library's quasi-étale model, with supports in `L`-valued
points, Worker 26's compactly supported comparison
`quasiEtaleCompactComparison` is not an isomorphism for some sheaves on a
noncompact `X`. An example is in `notes/henniart/harris-cohomology-coverage.md`,
section "Retained source gaps and scope decisions". That is why this module
states the ordinary comparison for compact `X`, which uses no points and is
exactly the quasi-étale case of Berkovich's theorem.

## Role in the Harris framework

This proposition is a theorem statement for Task 16, "Formalize the Harris and
Berkovich cohomological theorem-statement framework". That task covers
Berkovich's equivariant-sheaf comparisons as part of the geometric and
cohomological input to Harris's weak automorphic induction. The task's
coverage note `notes/henniart/harris-cohomology-coverage.md` lists which
comparisons are stated and which remain open. No other Library statement uses
this proposition yet.
