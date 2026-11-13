# Admissible representations and admissible Hecke modules (Renard III.1.7): statement

Module `Langlands.Representation.Hecke.AdmissibleModuleStatement`. Namespace
`Langlands.Hecke`. Universe parameters `u` (the group) and `v` (the representation space).
The module contains one **statement**, the `Prop`-valued definition
`AdmissibleIffHeckeAdmissibleStatement`. It proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. III.1.7 translates admissibility of a representation
into admissibility of its Hecke module, and then deduces its Proposition from I.5.1. The
Library has both notions: `IsAdmissible` for representations and
`NonUnitalModuleAdmissible.IsAdmissible` for modules
([NonUnitalModuleAdmissible](../../Algebra/NonUnitalModuleAdmissible.md)). No published
statement relates them. The III.1.7 Proposition itself is the published, proved
`AdmissibleBidualStatement`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read III.1.7, printed p.62 / PDF p.68:

> Définition. Une représentation lisse `(π, V)` du groupe t.d. `G` est dite admissible, si pour
> tout sous-groupe ouvert `N` de `G`, le sous-espace des vecteurs fixes `V^N` est de dimension
> finie.
>
> Traduisons ceci : comme les sous-groupes ouverts compacts forment une base de voisinages de
> l'identité dans `G`, la représentation `(π, V)` est admissible si et seulement si `V^K` est
> de dimension finie pour tout sous-groupe ouvert compact `K` de `G`. En termes de
> `H(G)`-module, ceci signifie que `e_K · V` est de dimension finie pour tout `K` comme
> ci-dessus. Or pour tout idempotent `e` de `H(G)`, il existe un tel `K` tel que `e ≤ e_K`. On
> a donc `e · V = e_K e · V ⊂ e_K · V`, et l'on voit que la représentation `(π, V)` est
> admissible si et seulement si le `H(G)`-module non dégénéré `V` est admissible au sens de
> I.5.1.

## Published objects used

- `IsAdmissible ρ`: smooth, with finitely generated (here finite-dimensional) `V^N` for every
  open subgroup `N`, Renard's definition ([Smooth/Definitions](../Smooth/Definitions.md)).
- `fixedVectors ρ K`, the `K`-fixed vectors.
- `heckeNonUnitalModule μ ρ hρ` and `heckeNonUnitalModule_isNondegenerate`: the nondegenerate
  `H(G)`-module of a smooth representation, through `heckeAction`
  ([NondegenerateModuleFunctor](NondegenerateModuleFunctor.md)).
- `Homomorphism.isIdempotented μ`: `H(G)` is a ring with idempotents
  ([HomomorphismLeft](HomomorphismLeft.md)).
- `Algebra.NonUnitalModuleAdmissible.IsAdmissible hA hM`: every fixed part `e · M`, for an
  idempotent `e`, is finite-dimensional for the complex scalars recovered from the algebra
  (I.5.1).

## The statement

**`AdmissibleIffHeckeAdmissibleStatement`.** Let `G` be a t.d. group (Hausdorff, locally
compact, nonarchimedean) with a left Haar measure `μ`, and `ρ` a smooth complex
representation on `V`. Then:

1. `ρ` is admissible if and only if `V^K` is finite-dimensional for every compact open
   subgroup `K`;
2. `ρ` is admissible if and only if the nondegenerate `H(G)`-module `V` is admissible in the
   sense of I.5.1.

## Formalization choices

- **Group hypotheses.** These are the hypotheses of the published Hecke-module construction
  (`NonarchimedeanGroup`, Hausdorff, locally compact), Renard's t.d. groups.
- **Scalars.** I.5.1 measures `e · V` with the complex scalars recovered from `H(G)`. On a
  smooth representation these are the original scalars, since `heckeAction` is linear. The
  statement uses the published definition unchanged.
- **The I.5.1 Corollary in terms of representations**, mentioned after the III.1.7
  Proposition, is covered by published proved results: `SmoothAdmissibleDualityStatement`
  (`Ṽ` admissible) and `isIrreducible_smoothContragredient_iff_of_bidual`.

## Why the statement is true

1. An open subgroup `N` contains a compact open subgroup `K`, and `V^N ⊂ V^K`. So
   finite-dimensionality for compact open subgroups gives it for all open subgroups, and the
   converse is immediate.
2. For compact open `K`, the normalized indicator `e_K` is an idempotent of `H(G)`, and
   `e_K · V = V^K` (published `fixedProjection`, III.1.5 (i)). Conversely, every idempotent `e`
   of `H(G)` is a test function, bi-invariant under some compact open `K`. So `e = e_K e` and
   `e · V ⊂ e_K · V = V^K`.

## Remaining obligations

The proof is a separate obligation.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Hecke.HomomorphismLeft` | `Homomorphism.isIdempotented`; through its imports `heckeNonUnitalModule`, `heckeNonUnitalModule_isNondegenerate`, `HeckeAlgebra`, `IsAdmissible`, `fixedVectors` |
| `Langlands.Algebra.NonUnitalModuleAdmissible` | `NonUnitalModuleAdmissible.IsAdmissible` |
