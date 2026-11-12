# Fixed vectors of a compact open subgroup (Renard III.1.5): statements

Author: Worker 1222. Module `Langlands.Representation.Hecke.FixedVectorCornerStatements`,
namespace `Langlands.Hecke`. Entry proposition `FixedVectorCornerStatements`, the conjunction
of five closed `Prop`-valued definitions (universe parameters `u, v`). The module proves
nothing.

## Original source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
**9 July 2026**, registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Worker 1222 read
III.1.3–III.1.6, printed pp.59–62 / PDF pp.65–68, for this unit. Section III.1.5, printed
pp.60–61 / PDF pp.66–67, reads (abridged to the assertions):

> Soit `K` un ouvert compact de `G`, et soit `e_K` l'idempotent de `H(G)` donné par la mesure
> de Haar normalisée sur `K`. [...] Rappelons que `e_K ∗ H(G) ∗ e_K = H(G, K)`.
>
> **Proposition.** (i) Le module `j_K(V) = e_K · V` est le sous-espace `V^K` de `V` des
> vecteurs fixes sous l'action de `K` dans `V`. (ii) Le noyau de `π(e_K)` dans `V` est le
> sous-espace `V(K)` de `V` engendré par les vecteurs de la forme `π(e_K) · v − v`, `v ∈ V`.
> (iii) On a `V = V^K ⊕ V(K)`. (iv) Le foncteur `j_K` est exact.
>
> **Théorème.** (i) La représentation `(π, V)` est irréductible ou nulle si et seulement si
> pour tout sous-groupe ouvert compact `K` de `G`, le `H(G, K)`-module `V^K` est simple ou
> nul. (ii) Soient `(π_i, V_i)`, `i = 1, 2`, deux représentations lisses irréductibles de `G`,
> et soit `K` un sous-groupe ouvert compact de `G` tel que `V_i^K ≠ 0`. Alors `π_1` et `π_2`
> sont équivalentes si et seulement si `V_1^K` et `V_2^K` sont des `H(G, K)`-modules
> isomorphes. (iii) Pour chaque module simple `W` de `H(G, K)`, il existe une représentation
> irréductible `π` de `G` telle que `V^K = W`.

The source introduces the Theorem with "Nous redonnons, dans le cadre plus spécifique de
cette section, les résultats de la proposition I.3.2".

## Published objects used

- `SmoothRep.{0, u, v} ℂ G`, its `representation`, `isSmooth`, `IsIrreducible` and the
  underlying intertwiner `SmoothRep.hom f` of a morphism (module
  `Langlands.Representation.Category.Basic`).
- `fixedVectors ρ K`, the `K`-fixed submodule (`Smooth/Definitions`), and
  `fixedVectorsMap f K`, the restriction of an intertwiner to fixed vectors
  (`Smooth/FixedVectors/Definitions`).
- `fixedProjection μ ρ hρ K hK : V →ₗ[ℂ] fixedVectors ρ K`, the published action of the
  normalized indicator `e_K = μ(K)⁻¹ 1_K` of `K`, which is Renard's `π(e_K)`
  (`Hecke/ActionProjection`). Its range is exactly `V^K`, which is Proposition (i).
- `HeckeAlgebra.Corner μ K hK`, the published unital algebra of `K`-bi-invariant test
  functions, whose image in the Haar Hecke algebra is `e_K H(G) e_K = H(G, K)`
  (`Hecke/Corner`), and `cornerModule μ ρ hρ K hK`, its published action on `V^K`
  (`Hecke/CornerAction`).

The group hypotheses are the published locally profinite ones of
`CornerFixedVectorsSimplicityStatement`: `[IsTopologicalGroup G] [T2Space G]
[LocallyCompactSpace G] [TotallyDisconnectedSpace G]`, with the Borel structure and a left
Haar measure `μ` where the Hecke algebra is involved. A compact open subgroup is an
`OpenSubgroup G` with `hK : IsCompact (K : Set G)`.

## Proposition definitions

### `FixedProjectionKernelStatement` (Proposition (ii)–(iii))

For every smooth `A` and compact open `K`:
`LinearMap.ker (fixedProjection …) = Submodule.span ℂ (range (x ↦ π(e_K) x − x))`, and
`IsCompl (fixedVectors A.representation K) (LinearMap.ker (fixedProjection …))`. The kernel
of `fixedProjection` is the kernel of `π(e_K)` in `V`.

### `FixedVectorsExactStatement` (Proposition (iv))

For smooth `A`, `B`, `C`, morphisms `f : A ⟶ B`, `g : B ⟶ C` and a compact open `K`: if the
range of `f` equals the kernel of `g`, then the range of `fixedVectorsMap f K` equals the
kernel of `fixedVectorsMap g K`. Exactness at the middle term includes exactness of short
exact sequences, so this is exactness of `j_K`. No Haar measure is needed to state it.

### `IrreducibleIffFixedSimpleStatement` (Theorem (i))

For every smooth `A`: `A.IsIrreducible ∨ Subsingleton A` if and only if, for every compact
open `K`, the fixed space with the corner action is a simple
`HeckeAlgebra.Corner μ K hK`-module or is `⊥`.

### `IrreducibleEquivIffFixedEquivStatement` (Theorem (ii))

For irreducible `A`, `B` and a compact open `K` with nonzero `K`-fixed spaces in both: there
is an equivariant linear equivalence `A.representation.Equiv B.representation` if and only
if there is a `HeckeAlgebra.Corner μ K hK`-linear equivalence between the two fixed spaces.

### `SimpleCornerModuleRealizationStatement` (Theorem (iii))

For a compact open `K` and a simple module `W : Type v` over `HeckeAlgebra.Corner μ K hK`,
there is an irreducible `A : SmoothRep.{0, u, max u v} ℂ G` whose `K`-fixed space is
isomorphic to `W` as a corner module. The source's equality `V^K = W` is read as an
isomorphism of `H(G, K)`-modules. The carrier universe `max u v` contains those of `G` and
`W`; the representation constructed in the proof (I.3.2: `(H(G) ⊗_{H(G,K)} W)_{e_K}`) lives
there.

### `FixedVectorCornerStatements`

The conjunction of the five definitions, in this order.

## Provenance and relation to the Library

The provenance is the source Proposition and Theorem. Proposition (i) is already the
published `heckeAction_normalizedIndicator_range` of `Hecke/ActionProjection`. Parts of the
Theorem have published counterparts from Bernstein–Zelevinsky (1976), Proposition 2.10: the
forward direction of (i) for nonzero fixed spaces is the published statement
`CornerFixedVectorsSimplicityStatement`, and the published theorem
`nonempty_equiv_of_cornerAction_eq_zero_iff` (`Hecke/CornerDetermination`) proves a strong
form of the converse direction of (ii). This unit states each assertion in Renard's form
with Renard's quantifiers, so that the section has a single entry statement.

The source works with complex representations of t.d. groups; the published locally
profinite convention is used. The universes `u` (group) and `v` (carriers) are independent.

## Scope

This module states III.1.5 and proves none of it. Proofs belong to a separate proof task.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Hecke.CornerAction` | `HeckeAlgebra.Corner`, `cornerModule` |
| `Langlands.Representation.Hecke.ActionProjection` | `fixedProjection` |
| `Langlands.Representation.Smooth.FixedVectors.Definitions` | `fixedVectorsMap` |
| `Langlands.Representation.Category.Basic` | `SmoothRep`, `SmoothRep.hom` |
| `Mathlib.RingTheory.SimpleModule.Basic` | `IsSimpleModule` |
