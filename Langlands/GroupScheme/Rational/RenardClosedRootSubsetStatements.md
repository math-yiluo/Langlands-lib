# Renard V.4.2 on closed sets of relative roots, without Borel–Tits 3.22 b)

Module `Langlands.GroupScheme.Rational.RenardClosedRootSubsetStatements`. Namespace
`Langlands.GroupScheme`. Universe parameter `u` (the base field).

The module contains one `Prop`-valued definition, `RenardClosedRootSubsetStatements`. It is the
conjunction, in this order, of

1. `ConvexRootSubsetHullStatement`,
2. `UnipotentRootSubsetCocharacterStatement`,
3. `SymmetricRootSubsetWeylStatement`,
4. `StandardParabolicRootTripleStatement`,
5. `RootSubsetGroupExistenceStatement`,
6. `StandardParabolicRootSubsetGroupStatement`,
7. `ConvexRootSubsetGroupIntersectionStatement`,
8. `UnipotentRootSubsetGroupIntersectionStatement`,

all published in [ClosedRootSubsetStatements](ClosedRootSubsetStatements.md) and taken there at
the same universe `u`. These are the nine components of the published conjunction
`ClosedRootSubsetStatements` except `ClosedRootSubsetGroupIntersectionStatement`. Nothing is
proved in this module, and no definition of the companion module is changed.

Worker 4 wrote this unit under the whole-book task `f5d1f399-a1f8-4ab5-a981-90b92abd4857`, as a
correction of its earlier unit `ClosedRootSubsetStatements`.

## Why a second conjunction

`ClosedRootSubsetGroupIntersectionStatement` is Borel–Tits 3.22 b) for a maximal split torus: in
`relativeRoots i`, for closed `S` and `X` such that `S ∩ X` is convex, `G(S) ∩ G(X) = G(S ∩ X)`
on reduced points. This assertion is false. The published note
[Borel–Tits 3.22(b): a split D4 obstruction](../../../notes/errata/borel-tits-1965-closed-root-intersection.md)
(Worker 248, with checks by Workers 292 and 785) gives a paper counterexample, which Worker 4 has
checked:

- `G = SO₈` over `ℂ`, split, with its diagonal maximal torus `T` and the reduced root system
  `{±εᵢ ± εⱼ}` of type `D₄`;
- `S = {±ε₁ ± ε₂, ±ε₃ ± ε₄}` and `X = {±ε₁ ± ε₃, ±ε₂ ± ε₄}`, both closed and symmetric, of type
  `A₁⁴`, and disjoint, so `S ∩ X = ∅` is convex (cone `{0}`); neither `S` nor `X` is convex;
- `G(∅) = Z_G(T) = T`, while the element `J` exchanging `eᵣ` and `fᵣ` for every `r` is a product
  of root elements for `S` times `−1 ∈ T`, and also such a product for `X`. So
  `J ∈ G(S)(ℂ) ∩ G(X)(ℂ)` and `J ∉ T(ℂ)`.

`Spec ℂ` is reduced, so this contradicts `HasReducedPointIntersection` for `G(S)`, `G(X)` and
`G(∅)`. The note checks that the Library's `RelativeRoot.subgroup` and `torusCentralizer` give
the standard root groups and `T` in this example. It is a paper argument, not a Lean refutation.
In the block description, `G(S) = SO(V₁ ⊕ V₂) × SO(V₃ ⊕ V₄)` and
`G(X) = SO(V₁ ⊕ V₃) × SO(V₂ ⊕ V₄)` with `Vᵣ = ⟨eᵣ, fᵣ⟩`, and their intersection is `T ∪ JT`. The
note also locates the error in the printed proof of 3.22 b) (A. Borel and J. Tits, *Groupes
réductifs*, Publ. Math. IHÉS 27 (1965), printed p.84, registered as
`borel-tits-1965-groupes-reductifs`), and records that §5 of the 1972 *Compléments* lists no
correction to 3.22.

Consequently the published conjunction `ClosedRootSubsetStatements` is false and cannot be
proved. `RenardClosedRootSubsetStatements` is the conjunction that the whole-book formalization
of V.4.2 uses instead.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July
2026, registered as `renard-2026-representations-groupes-reductifs-padiques`, §V.4.2 (printed
p.118 / PDF p.124). The text of V.4.2 is quoted in full in the companion
[ClosedRootSubsetStatements](ClosedRootSubsetStatements.md). Its first proposition, cited from
[7] 3.22, reads:

> **Proposition.** Soient `S`, `T` des parties fermées de `Σ_∅`.
> (i) Si `S` et `T` sont convexes, alors `G(S) ∩ G(T) = G(S ∩ T)`.
> (ii) Si `T` est unipotent, alors `G(S) ∩ U(T) = U(S ∩ T)`.

Renard's (i) assumes that **both** sets are convex. It does not state the form of [7] 3.22 b) in
which only the intersection is convex, so excluding `ClosedRootSubsetGroupIntersectionStatement`
removes nothing that Renard states.

## Components and the sentences of V.4.2

The statements are described in detail in the companion Markdown, section *The statements*.

| Component | Content | Source |
| --- | --- | --- |
| `ConvexRootSubsetHullStatement` | convex sets are the sets containing every root of the cone they span | derived reformulation of the definition of "convexe" |
| `UnipotentRootSubsetCocharacterStatement` | unipotent sets are the closed sets on which some cocharacter is positive | derived reformulation of "unipotente", comparing it with [7] 3.8 (iv) |
| `SymmetricRootSubsetWeylStatement` | reflections of a symmetric set exist in `W_G` and preserve it; so does `W_T` | "`T` est un système de racines, et l'on note `W_T ⊂ W_G` son groupe de Weyl" |
| `StandardParabolicRootTripleStatement` | `(𝒫, ℳ, 𝒩)` is a parabolic triple, with explicit descriptions, convexity, and recovery of `Θ` | proposition citing [7] 5.12–5.18, combinatorial part |
| `RootSubsetGroupExistenceStatement` | `G(T)` and `U(T)` exist, smooth, affine and connected; `U(T)` is unipotent for unipotent `T` | "on note `G(T)`", "on note `U(T)`" |
| `StandardParabolicRootSubsetGroupStatement` | `G(𝒫) = P_Θ`, `G(ℳ) = M_Θ`, `U(𝒩) = N_Θ`, `W_ℳ` is the Weyl group of `M_Θ` | proposition citing [7] 5.12–5.18, group part |
| `ConvexRootSubsetGroupIntersectionStatement` | for convex `S`, `X` in `Σ_∅`, `G(S) ∩ G(X) = G(S ∩ X)` on reduced points | (i), in Renard's reduced `Σ_∅` |
| `UnipotentRootSubsetGroupIntersectionStatement` | for closed `S` and unipotent `X` in `Φ(S, G)`, `G(S) ∩ U(X) = U(S ∩ X)` on reduced points | (ii), in the form of [7] 3.22 c) |

The companion Markdown (*Source issues*) explains why (ii) is stated in the possibly nonreduced
`relativeRoots i`: its reading with sets closed only in `Σ_∅` is false (quasi-split `SU₅`, type
`BC₂`).

## Correction to the companion Markdown

The companion `ClosedRootSubsetStatements.md` justifies (i) through 3.22 b). In *Provenance of
each statement* it says that `ClosedRootSubsetGroupIntersectionStatement` contains V.4.2 (i) in
the nonreduced ambient set. In *Source issues* it says that (i) in `Σ_∅` follows from [7] 3.22 b)
applied to `Φ ∩ C₁` and `Φ ∩ C₂`. In *Why the statements are true* its intersection bullet cites
3.22 b). The implication from `ClosedRootSubsetGroupIntersectionStatement` is correct, but that
statement is false, so these sentences do not justify (i). The identity
`Φ ∩ C = S ∪ (2S ∩ Φ)` and `G(S) = G(Φ ∩ C)` used there remain correct. (i) itself is true, as
explained below.

## Why the components are true

For the first six components and (ii), the arguments in the companion section *Why the
statements are true* stand; (ii) is [7] 3.22 c), whose proof does not use b).

For (i), the hypothesis that `S` and `X` are both convex is used. The following sketch
follows the route of the proof submitted for Task 6515 (`77b1b105-0195-4b71-a588-ede7dd5a2aa6`),
in simplified form; it is not part of this module. Let `S = Σ_∅ ∩ C₁` and `X = Σ_∅ ∩ C₂` for closed convex cones `Cᵢ`. Pass to
the full roots `Φ ∩ Cᵢ`, which give the same groups, and then to an algebraic closure. There
`H = G(S) ∩ G(X)` contains a maximal torus, and its identity component is the group `G(S ∩ X)`
generated by the torus and the root groups common to both. Every component of `H` meets the
normalizer of the torus, and so gives a Weyl element lying in the Weyl groups of the symmetric
parts `Φ ∩ C₁ ∩ (−C₁)` and `Φ ∩ C₂ ∩ (−C₂)`. Each of these is the set of roots in a linear
subspace, because the cones are convex. By the theorem of Steinberg on stabilizers of subspaces,
the intersection of the two Weyl groups is generated by the reflections in roots lying in both
subspaces, that is, in the symmetric part of `S ∩ X`. These reflections lie in `G(S ∩ X)`, so
`H = G(S ∩ X)`. In the `SO₈` example the symmetric parts are not the roots of a subspace, and
both Weyl groups contain `−1`, which is why the argument fails there.

## Status of the components

At Library commit `b44618a4f02405d5be8c906f21cf7817e4eaafb9`, seven components are proved:

| Component | Theorem | Module |
| --- | --- | --- |
| `ConvexRootSubsetHullStatement` | `convexRootSubsetHull` | `Langlands.GroupScheme.Rational.ConvexRootSubsetHullProof` |
| `UnipotentRootSubsetCocharacterStatement` | `unipotentRootSubsetCocharacter` | `Langlands.GroupScheme.Rational.UnipotentRootSubsetCocharacterProof` |
| `SymmetricRootSubsetWeylStatement` | `symmetricRootSubsetWeyl` | `Langlands.GroupScheme.Rational.SymmetricRootSubsetWeylProof` |
| `StandardParabolicRootTripleStatement` | `standardParabolicRootTriple` | `Langlands.GroupScheme.Rational.StandardParabolicRootTripleProof` |
| `RootSubsetGroupExistenceStatement` | `rootSubsetGroupExistence` | `Langlands.GroupScheme.Rational.RootSubsetGroupExistenceProof` |
| `StandardParabolicRootSubsetGroupStatement` | `standardParabolicRootSubsetGroup` | `Langlands.GroupScheme.Rational.StandardParabolicRootSubsetGroupProof` |
| `UnipotentRootSubsetGroupIntersectionStatement` | `unipotentRootSubsetGroupIntersection` | `Langlands.GroupScheme.Rational.UnipotentRootSubsetGroupIntersectionProof` |

`ConvexRootSubsetGroupIntersectionStatement` is the target of Task 6515, whose proof is not yet in
the Library at that commit. Worker 4 checked by `lean_check` that the eight components assemble
into `RenardClosedRootSubsetStatements` with only the standard axioms, assuming the Task 6515
component as a hypothesis.

## Remaining obligations

The proof of `RenardClosedRootSubsetStatements` is a separate obligation: once Task 6515 is
proved, it is the pairing of the eight component theorems.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.GroupScheme.Rational.ClosedRootSubsetStatements` | the eight component statements |
