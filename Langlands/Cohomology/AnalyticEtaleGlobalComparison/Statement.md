# Berkovich's comparison `H^q(X{G}, F) ≅ H^q(X, b^*F)` for compact `X` (étale)

Author: Worker 16.

This module defines one proposition,
`Langlands.Cohomology.AnalyticEtaleGlobalComparison.AnalyticEtaleGlobalComparisonStatement`.
It is the étale case of Berkovich's Theorem 1.6.1(ii): if a topological group
`G` acts continuously on a compact analytic space `X`, then for every étale
`G`-sheaf `F` the comparison maps `H^q(X{G}, F) → H^q(X, b^*F)` are
isomorphisms in every degree `q`. It is a theorem-statement definition, not a
proof. The isomorphism is the conclusion; it is not supplied as data or as a
hypothesis. The comparison map itself is Worker 26's published construction.
The quasi-étale case is the published companion statement
`Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.AnalyticQuasiEtaleGlobalComparisonStatement`,
and this module follows it binder for binder.

## Objects

All objects are imported from Worker 26's module
`Langlands.Sheaf.Equivariant.AnalyticEtaleCohomology` (namespace
`Langlands.Sheaf.Equivariant.Analytic`) and the modules it builds on, mainly
Worker 26's `AnalyticGSheaves`, `AnalyticEtaleComparison` and
`TwistedExactGlobalComparison`, and Worker 21's analytic spaces, étale site and
continuous actions.

- `K : Type u` is a complete ultrametric normed field (`NormedField`,
  `IsUltrametricDist`, `CompleteSpace`). `X` is an object of Worker 21's
  category of analytic spaces `LocalizedCategory.{u, v, v} (K := K)`.
- `G : Type z` is a topological group (`IsTopologicalGroup`) and
  `ρ : G →* Aut X` an action of `G` on `X` by automorphisms.
- `R : Type (max u (v + 1) uL)` is a commutative ring. Sheaves take values in
  `R`-modules. This coefficient universe is the one of Worker 26's derived
  functors.
- `EtaleGSheaf ρ (ModuleCat R)` is Worker 26's category of étale `G`-sheaves:
  sheaves on the twisted étale site of `X` (Berkovich's `G^d`-sheaves) whose
  sections are locally discrete for `distinguishedLiftSystem ρ`. For every
  section `s` over `U`, the arrows into `U` that factor through a
  distinguished étale object `V` on which the restriction of `s` is fixed by an
  open subgroup acting through a lift of the action form a covering sieve.
- `etaleGSheafCohomology ρ R q` is Berkovich's `H^q(X{G}, F)`. It is the
  `q`-th right derived functor of `etaleGSheafSections ρ R`, Berkovich's
  `Γ_{X{G}}`: the smooth part of the representation of `G` on the global
  sections of `F`. Derived functors are computed with injective resolutions in
  `EtaleGSheaf ρ (ModuleCat R)`, and the values are smooth representations of
  `G`.
- `etaleCohomology X R q` is `H^q(X, -)`, the `q`-th right derived functor of
  the sections over `X` of `R`-module sheaves on Worker 21's étale site of `X`.
  Its coverings are the families of étale morphisms whose point maps are
  jointly surjective.
- `etaleGSheafRestriction ρ R` is Berkovich's `b^*`: the inclusion of étale
  `G`-sheaves into sheaves on the twisted étale site, followed by restriction
  to the étale site of `X`, which forgets the action of `G`. It is exact.
- `etaleComparison ρ R q` is the comparison `H^q(X{G}, F) → H^q(X, b^*F)`. It
  is a natural transformation from
  `etaleGSheafCohomology ρ R q ⋙ smoothForget R G` (the underlying modules of
  `H^q(X{G}, F)`) to `etaleGSheafRestriction ρ R ⋙ etaleCohomology X R q`.
  Worker 26 defines it as the base change, along the exact functors `b^*` and
  `smoothForget`, of the inclusion `Γ_{X{G}}(F) ⊆ (b^*F)(X)` of smooth global
  sections into all global sections.
- `IsCompactSpace X`, from Worker 21's `LocalActionLifts`, says that the
  underlying topological space of `X` is compact and Hausdorff.
- `IsContinuousAction ρ`, from Worker 21's `ContinuousAnalyticAction`, is
  Berkovich's continuity of an action: for every test triple `τ` (Berkovich's
  `ε ∈ E(X)`), the preimage under `ρ` of the set of automorphisms within `τ` of
  the identity is a neighbourhood of `1` in `G`.

## The proposition

| Declaration | Asserted conclusion |
| --- | --- |
| `AnalyticEtaleGlobalComparisonStatement X G ρ R` | If `IsCompactSpace X` and `IsContinuousAction ρ`, then for every `q : ℕ` the natural transformation `etaleComparison.{u, v, uL} ρ R q` is an isomorphism (`IsIso`). |

`IsIso` of a natural transformation means that it is a natural isomorphism.
So the proposition asserts that each map `H^q(X{G}, F) → H^q(X, b^*F)` is a
bijection, for every étale `G`-sheaf `F` of `R`-modules. These maps are
natural in `F` and are the comparison maps that Worker 26 constructed.
Isomorphisms are not merely asserted to exist.

Compactness and continuity are hypotheses of the proposition, not binders of
the definition. The definition has two further instance binders, which are
needed to define the source `H^q(X{G}, -)`. They are the same as in Worker
26's declarations.

- `[Small.{max u (v + 1) uL} G]` is a size condition. It makes the twisted
  étale site essentially small, which the published sheafification and
  enough-injectives results on that site use. It holds, for example, when `G`
  lies in a universe at most `max u (v + 1) uL`.
- `[(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]`
  is Worker 26's class from `LocalActionSmoothPart`. It has two fields. First,
  every arrow of the twisted étale site between objects with admissible local
  actions is compatible with the two actions on open subgroups
  (`IsRestrictionEquivariant`), so that restriction along it preserves
  discreteness of sections. Second, every cone over a cospan is covered by
  objects with admissible local actions that map to the cospan
  (`fiberRefinementSieve`). Worker 26 uses it to make étale `G`-sheaves of modules an abelian
  category with enough injectives. It is not proved in the Library. Worker
  26's module `AnalyticEtaleRefinements` derives it from three conditions on
  the étale site of `X`: distinguished étale neighbourhoods of points, lifts of
  the action to distinguished étale objects, and compatibility of lifts along
  arrows over `X`. Geometrically these are Berkovich's statements on p.7 and
  p.8, which rest on his Key Lemma on lifts. If the class failed, the
  proposition could not be formed for that action.

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
  This module states the étale reading ("resp. étale").
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
- §1.4, pp.7–8: distinguished étale morphisms and their lifted actions (p.7);
  Definition 1.4.1, "A quasi-étale (resp. étale) `G`-sheaf on `X` is a
  quasi-étale (resp. étale) `G^d`-sheaf `F` such that for any quasi-étale
  morphism `U → X` with compact `U` the action of `G_U` on `F(U)` is
  discrete"; and the characterization on p.8: "an étale `G^d`-sheaf `F` is a
  `G`-sheaf if and only if for any étale morphism `U → X` and any element
  `f ∈ F(U)` each point of `U` has a distinguished open neighborhood `𝒰` such
  that the stabilizer of `f|𝒰` is open in `G_𝒰`". Worker 26's `EtaleGSheaf`
  models this characterization.
- §1.5, pp.10–11: the Godement resolution `C^·(F)` of an étale abelian sheaf
  on `X(G)` and Proposition 1.5.1, "For any `F ∈ X(G)~_ét` and `m ≥ 0`,
  `b^*(C^m(F))` is a soft sheaf on `X_ét`."

## Correspondence and modelling choices

- Berkovich's étale abelian sheaves on `X(G)` are modelled by Worker 26's
  étale `G`-sheaves `EtaleGSheaf ρ`, through Berkovich's Theorem 1.4.2 and the
  characterization on p.8, as in all of Worker 26's étale modules. Theorem
  1.4.2 is not formalized.
- Berkovich works with abelian sheaves. Here sheaves take values in
  `R`-modules for an arbitrary commutative ring `R` in the coefficient universe;
  abelian sheaves are the case `R = ULift ℤ`. The statement for all `R` is the
  natural generalization. Berkovich's argument (below) uses nothing specific
  to abelian groups.
- Only the étale isomorphism of Theorem 1.6.1(ii) is stated. Its spectral
  sequence, part (i) for paracompact `X` and part (iii) are not stated. The
  quasi-étale isomorphism is the companion statement named above.
- The hypotheses are exactly Berkovich's: `X` is a `G`-space and `X` is
  compact. The two instance binders are needed only to form the source
  category and its derived functors; they are not hypotheses of Berkovich's
  theorem.

## Why the proposition is expected to hold

Berkovich's proof on p.13 says that (ii) follows from (i), and that (i) for
étale sheaves follows from Proposition 1.5.1 and [Ber3], Lemma 3.2(i). Here
[Ber3] is Berkovich, *Vanishing cycles for formal schemes*, Invent. Math. 115
(1994), 539–571. That paper was not consulted for this module. The argument
runs as follows.

1. Part (i): if `X` is paracompact, the higher direct images of
   `F ↦ (b^*F)(X)` on étale sheaves on `X(G)` are `H^q(X, b^*F)`. The
   Godement resolution `C^·(F)` of §1.5 is built in the category of étale
   sheaves on `X(G)`. By Proposition 1.5.1 each `b^*(C^m(F))` is soft on
   `X_ét`, in the sense of the two conditions on p.10: flabby Galois modules
   as stalks, and surjective restriction to compact subsets. Berkovich cites
   [Ber3], Lemma 3.2(i), for the vanishing of the higher cohomology of such
   sheaves on a paracompact space. So `b^*C^·(F)` is a `Γ(X, -)`-acyclic
   resolution of `b^*F`, and it computes `H^q(X, b^*F)`.
2. Part (ii): a compact Hausdorff space is paracompact. For compact `X`, every
   global section of an étale `G`-sheaf is fixed by an open subgroup, so
   `Γ_{X{G}}(F) = (b^*F)(X)`. The derived functors of `Γ_{X{G}}` followed by
   the exact forgetful functor are the derived functors of `F ↦ (b^*F)(X)`,
   which are `H^q(X, b^*F)` by (i).

In degree zero the Library model behaves the same way, given one fact from
Berkovich's theory that the Library does not prove: étale morphisms are open
maps. Let `s` be a global section of `F`. Local discreteness gives a covering
sieve of `X` whose arrows factor through distinguished étale objects `V` on
which `s` is fixed by an open subgroup acting through a lift. The images of
these `V` cover `X` and are open, so finitely many `V_1, …, V_n` cover the
compact space `X`. Their arrows to `X` are jointly surjective and hence
generate a covering sieve. Each element of the intersection of the
corresponding open subgroups fixes the restriction of `s` to each `V_i`, and
hence fixes `s` by the sheaf condition. So the inclusion
`Γ_{X{G}}(F) ⊆ (b^*F)(X)` is an equality, and `etaleComparison ρ R 0`
corresponds to this identity. In positive degrees the argument needs the
Godement resolution of §1.5, Proposition 1.5.1 and the acyclicity of soft
étale sheaves, which the Library does not yet have.

## Relation to the compactly supported comparison

Theorem 1.6.1(ii) concerns ordinary cohomology. Its compactly supported
analogue for étale sheaves is Berkovich's Corollary 1.5.2(i), whose Library
form is Worker 26's `etaleCompactComparison` in `AnalyticEtaleComparison`.
That construction takes supports in `L`-valued points of `X`, and its
Markdown explains why it is not an isomorphism in general. This module states
the ordinary comparison for compact `X`, which uses no points and is exactly
the étale case of Berkovich's theorem. No compactly supported statement is
made here.

## Role in the Harris framework

This proposition is a theorem statement for Task 16, "Formalize the Harris and
Berkovich cohomological theorem-statement framework". That task covers
Berkovich's equivariant-sheaf comparisons as part of the geometric and
cohomological input to Harris's weak automorphic induction. The task's
coverage note `notes/henniart/harris-cohomology-coverage.md` lists which
comparisons are stated and which remain open. No other Library statement uses
this proposition yet.
