# Proof: connected reductivity and pseudo-reductivity under arbitrary field extension

Author: Worker 47.

This module proves `Langlands.GroupScheme.FieldExtensionReflectionStatement` in an
arbitrary universe `u`. The theorem `Langlands.GroupScheme.fieldExtensionReflection` has
exactly the type `FieldExtensionReflectionStatement.{u}`, with no added hypotheses. The
module also proves one helper theorem, `Langlands.GroupScheme.IsPseudoReductive.of_fieldExtension`.
It adds no definitions and no axioms.

The statement is defined in
[`Reductive.FieldExtensionReflectionStatement`](FieldExtensionReflectionStatement.md). For
fields `k K : Type u` with `[Algebra k K]` and a group scheme
`G : GroupScheme (Spec (CommRingCat.of k))`, write

```text
b   = Spec.map (CommRingCat.ofHom (algebraMap k K)) : Spec K ⟶ Spec k,
G_K = (GroupScheme.baseChange b).obj G.
```

The statement is the conjunction of
`ConnectedReductiveFieldExtensionIffStatement` (`IsConnectedReductive G ↔ IsConnectedReductive G_K`)
and `PseudoReductiveFieldReflectionStatement` (`IsPseudoReductive G_K → IsPseudoReductive G`).
The extension `K/k` and the group `G` are arbitrary.

## Component 1: connected reductivity

`fieldExtensionReflection` proves the equivalence from two published theorems, with no
further argument:

- **Forward direction.** `connectedReductiveFieldExtensionStatement`
  (module `Langlands.GroupScheme.Reductive.FieldExtensionProof`) proves
  `ConnectedReductiveFieldExtensionStatement.{u}`. Applied to `k`, `K` and `G`, it gives
  `IsConnectedReductive G → IsConnectedReductive G_K`.
- **Backward direction.** `IsConnectedReductive.of_fieldExtension`
  (module `Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof`) derives
  `IsConnectedReductive G` from `IsConnectedReductive G_K` alone, for every field extension
  and every group scheme `G`.

## Component 2: pseudo-reductivity descends

`IsPseudoReductive.of_fieldExtension` assumes `IsPseudoReductive G_K` and proves the four
fields of the structure `IsPseudoReductive G`. The first three are proved in the same way as
in the published proof of `IsConnectedReductive.of_fieldExtension`. Throughout, `b` is
surjective, flat and quasi-compact by the published `fieldExtension_fpqc` (module
`Langlands.GroupScheme.BaseChangeReflection`). These three properties are installed as local
instances.

- **Smoothness.** The published `smooth_of_baseChange` (module
  `Langlands.GroupScheme.Rational.UnipotentRadicalProperties`) descends smoothness of the
  structure morphism along the fpqc morphism `b`. It turns the smoothness field of
  `IsPseudoReductive G_K` into `Smooth G.X.hom`.
- **Connectedness.** The published `connectedSpace_of_baseChange` (same module) uses that
  the projection from `G_K` onto `G` is surjective because `b` is. It turns the
  connectedness field of `IsPseudoReductive G_K` into `ConnectedSpace G.X.left`.
- **Affineness.** `G_K` has affine structure morphism over the affine scheme `Spec K`, so
  its underlying scheme, definitionally `pullback G.X.hom b`, is affine (Mathlib's
  `isAffine_of_isAffineHom`). The published
  `Langlands.AlgebraicGeometry.fieldExtensionAffineDescent` (module
  `Langlands.AlgebraicGeometry.FieldExtensionAffineDescentProof`) then makes `G.X.left`
  affine. Since `Spec k` is affine too, Mathlib's instance `isAffineHom_of_isAffine` gives
  `IsAffineHom G.X.hom`.
- **Trivial unipotent radical.** Now that `G.X.hom` is affine, the published
  `HasTrivialUnipotentRadical.of_fieldExtension` (module
  `Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof`) turns the field
  `HasTrivialUnipotentRadical G_K` into `HasTrivialUnipotentRadical G`. That theorem
  base-changes a smooth connected unipotent closed subgroup of `G` with normal image to
  `K`. The hypothesis makes its image trivial over `K`, and fpqc reflection of trivial
  subgroup functors makes it trivial over `k`.

`fieldExtensionReflection` applies `IsPseudoReductive.of_fieldExtension` to obtain the second
component.

## Published inputs

| Theorem | Module |
| --- | --- |
| `Langlands.GroupScheme.connectedReductiveFieldExtensionStatement` | `Langlands.GroupScheme.Reductive.FieldExtensionProof` |
| `Langlands.GroupScheme.IsConnectedReductive.of_fieldExtension` | `Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof` |
| `Langlands.GroupScheme.HasTrivialUnipotentRadical.of_fieldExtension` | `Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof` |
| `Langlands.GroupScheme.fieldExtension_fpqc` | `Langlands.GroupScheme.BaseChangeReflection` |
| `Langlands.GroupScheme.smooth_of_baseChange` | `Langlands.GroupScheme.Rational.UnipotentRadicalProperties` |
| `Langlands.GroupScheme.connectedSpace_of_baseChange` | `Langlands.GroupScheme.Rational.UnipotentRadicalProperties` |
| `Langlands.AlgebraicGeometry.fieldExtensionAffineDescent` | `Langlands.AlgebraicGeometry.FieldExtensionAffineDescentProof` |

The Mathlib results used are `AlgebraicGeometry.isAffine_of_isAffineHom` and the instance
`AlgebraicGeometry.isAffineHom_of_isAffine` (`Mathlib.AlgebraicGeometry.Morphisms.Affine`).
The module imports the statement module, `Langlands.GroupScheme.Reductive.FieldExtensionProof`
and `Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof`; the other published
inputs come in through these imports.

## Provenance and scope

The statement's Markdown gives the sources: J. S. Milne, *Algebraic Groups* (2017),
Proposition 19.13, for component 1, and Conrad–Gabber–Prasad, *Pseudo-reductive groups*,
2nd edition (2015), Definition 1.1.1 and the inclusion `R_{u,k}(G)_K ⊆ R_{u,K}(G_K)` in the
proof of Proposition 1.1.9, for component 2. This proof does not follow either source's
argument. It assembles published Library results. In component 2 the descent of the
trivial unipotent radical plays the role of the CGP inclusion: a smooth connected unipotent
normal `k`-subgroup of `G` base-changes to one of `G_K`.

The route follows the description of Worker 3483's compiled proof in the task's context
(shared draft of Task 3483 in the previous instance). That draft was not available in this
instance, so this Lean file was written anew.

No reflection assertion is assumed. The fields and the extension are arbitrary, including
transcendental and inseparable extensions of imperfect fields. No smoothness, affineness,
connectedness or finite-type premise is placed on `G`. The development check reports only
the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
