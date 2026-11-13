# Characteristic subspaces of a finite-length representation (Renard III.1.10, Proposition): statement

Module `Langlands.Representation.Smooth.FiniteLengthCharacteristicDecompositionStatement`.
Namespace `Langlands`. Universe parameters `uG` (the group) and `uV` (the representation
space).
The module contains one **statement**, the `Prop`-valued definition
`FiniteLengthCharacteristicDecompositionStatement`. It proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. The Proposition of III.1.10 treats representations
that are admissible or of finite length. The admissible case, for the whole centre, is the
published and proved `CentralCharacterDecompositionStatement`
([CentralStatement](../Exponents/CentralStatement.md)). Its decomposition clause assumes that
every vector lies in a finite-dimensional subrepresentation of the centre (`IsCenterFinite`).
It proves this for admissible representations only. A representation of finite length also has
this property when `G` is countable at infinity (the centre acts through the
finite-dimensional algebra `End_G(V)`, by Schur's lemma), but no published statement derives
it, so the finite-length case is not available from the published one. The published
[RenardSchurStatements](RenardSchurStatements.md) says that "the Proposition of III.1.10 on
characteristic subspaces is not restated here". This unit states the finite-length case.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read III.1.10, printed pp.63–64 / PDF pp.69–70:

> Supposons que `G` soit dénombrable à l'infini et soit `Z` un sous-groupe contenu dans le
> centre `Z(G)`. […]
>
> Proposition. Soit `(π, V)` une représentation lisse de longueur finie ou admissible de `G`.
> Alors, pour tout caractère `χ` de `Z`, posons
> `V_χ = {v ∈ V | ∃ m ∈ ℕ, ∀ z ∈ Z, (π(z) − χ(z) Id)^m · v = 0}`,
> et appelons cet espace le sous-espace caractéristique de `V` pour le caractère `χ`. Alors
> `V = ⊕_χ V_χ`. Si `(π, V)` est de longueur finie, seul un nombre fini de facteurs sont non
> nuls.
>
> Démonstration. Si `(π, V)` est de longueur finie, on raisonne par récurrence sur la
> longueur, le cas où `(π, V)` est irréductible étant traité par le lemme de Schur. […]

## Published objects used

- `SmoothRep.{0, uG, uV} ℂ G`, its `representation`, and `SmoothRep.HasFiniteLength`: finite
  composition length of the `ℂ[G]`-module ([Category/Basic](../Category/Basic.md)). Every
  `ℂ[G]`-submodule of a smooth representation is smooth, so this is finite length in `M(G)`.
- Mathlib's `iSupIndep`, `Submodule` suprema and infima, `LinearMap.ker`.

## The statement

**`FiniteLengthCharacteristicDecompositionStatement`.** Let `G` be a t.d. group (Hausdorff,
locally compact, totally disconnected) countable at infinity (`SigmaCompactSpace G`), `Z` a
subgroup of the centre and `A` a smooth complex representation of finite length. For a
character `χ : Z →* ℂˣ` put

```text
V_χ = ⨆_m ⨅_{z ∈ Z} ker (π(z) − χ(z))^m .
```

Then the family `(V_χ)_χ` is independent, its supremum is `V`, and only finitely many `V_χ`
are nonzero.

## Formalization choices

- **`V_χ`.** The kernels `⨅_z ker (π(z) − χ(z))^m` increase with `m`, so their supremum is
  their union. That union is Renard's `V_χ`, with one exponent `m` for all `z ∈ Z`.
- **`V = ⊕_χ V_χ`** is the independence of the family together with `⨆_χ V_χ = V`.
- **Characters.** `χ` ranges over all homomorphisms `Z → ℂˣ`, as in the source. For a smooth
  `V` only finitely many have `V_χ ≠ 0`, and they are the central characters on `Z` of the
  composition factors.
- **Hypotheses.** Countability at infinity is the standing hypothesis of III.1.10. It is used
  through Schur's lemma (III.1.8, the published proved `SigmaCompactSchurStatement`) on the
  composition factors.
- **Relation to the published admissible case.** The statement could also be derived from
  `CentralCharacterDecompositionStatement` by proving that a finite-length representation is
  center-finite and finitely generated, and then grouping characters of `Z(G)` by restriction
  to `Z`. The unit states the source's assertion directly. The admissible case is not restated: for `Z = Z(G)` it is the published
  `CentralCharacterDecompositionStatement`, and a subgroup `Z` is obtained by grouping the
  characters of `Z(G)` by their restriction to `Z`.

## Why the statement is true

We follow Renard's proof, by induction on the length. For irreducible `V`, Schur's lemma gives
a character `χ₀` of `Z` with `π(z) = χ₀(z)` on `V`, so `V = V_{χ₀}`. In general let `V₀` be an
irreducible subrepresentation, on which `Z` acts by `χ₀`. By induction
`V/V₀ = ⊕_χ (V/V₀)_χ` with finitely many nonzero terms. If `v` maps into `(V/V₀)_χ`, then
`(π(z) − χ(z))^m v ∈ V₀` for all `z ∈ Z`, so
`(π(z) − χ₀(z))(π(z) − χ(z))^m v = 0`. The operators `π(z)`, `z ∈ Z`, commute, and each is
killed on the span of `Z · v` by a polynomial with roots in `{χ(z), χ₀(z)}`. Splitting `v`
along the generalized eigenspaces for these two characters gives `v ∈ V_χ + V_{χ₀}`.
Independence holds because, for `χ ≠ χ′`, some `z` has `χ(z) ≠ χ′(z)`, and generalized
eigenspaces of `π(z)` for distinct eigenvalues are independent.

## Remaining obligations

The proof is a separate obligation.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Category.Basic` | `SmoothRep`, `SmoothRep.representation`, `SmoothRep.HasFiniteLength` |
| `Mathlib.Basic.Complex.Basic` | `ℂ` |
