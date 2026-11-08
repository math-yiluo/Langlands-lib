# Schur's lemma and its consequences for t.d. groups: statements

Author: Worker 6. Module `Langlands.Representation.Smooth.RenardSchurStatements`, namespace `Langlands.Renard.Smooth`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, III.1.7–III.1.11, printed pp.62–65 / PDF pp.68–71. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

This is a statement unit: nothing is proved.

## Conventions

In every statement, `G` is a group with a topology making it a Hausdorff, locally compact, totally disconnected topological group, Renard's t.d. groups. "Countable at infinity" is Mathlib's `SigmaCompactSpace G`. Representations are Mathlib's `Representation ℂ G V` with the published `IsSmooth` and `IsAdmissible` predicates. `IsAdmissible` includes smoothness and finite-dimensional `N`-fixed vectors for every open subgroup `N`, which is Renard's Definition III.1.7. Irreducibility is Mathlib's `Representation.IsIrreducible`, which excludes the zero representation. The smooth contragredient is the published `smoothContragredient`, acting on `SmoothDual π`, and `smoothBidual` is the canonical map `V → Ṽ̃` (module `Smooth/Contragredient/Definitions`).

## The Lean statements

### `AdmissibleBidualStatement` (III.1.7, Proposition)

Renard: a smooth representation is admissible if and only if `V ≃ Ṽ̃`. For smooth `π`, the Lean statement asserts both:

- `IsAdmissible π ↔ Function.Bijective (smoothBidual hπ)`, for the canonical map;
- `IsAdmissible π ↔ Nonempty (π.Equiv (smoothContragredient (smoothContragredient π)))`, for an arbitrary equivalence.

The forward implications are the published `SmoothAdmissibleDualityStatement` clauses (module `Smooth/Contragredient/AdmissibleDualityStatement`). Both reverse implications hold because `Ṽ̃^K ≅ (V^K)**` for compact open `K` (III.1.6), and an infinite-dimensional space is not isomorphic to its double dual.

### `SigmaCompactSchurStatement` (III.1.8, Proposition)

For `G` countable at infinity and `π` smooth and irreducible:

1. every `G`-endomorphism `f` of `π` is `c • id` for some `c : ℂ`;
2. for every smooth irreducible `τ` (carrier in an independent universe) with no equivalence `π ≃ τ`, every intertwiner `π → τ` is zero.

Renard's proof shows that `V` has countable dimension, because `G/K` is countable (II.3.2), and applies Theorem B.II. The published `CountableDimensionalSchurStatement` (module `Representation/Schur/CountableDimensionStatement`) is the algebraic input. The published `AdmissibleSchurStatement` (module `Smooth/Schur/Statement`) covers admissible representations without countability, so the Remark after the Proposition is not restated.

### `InvariantContragredientPairingStatement` (III.1.9, Proposition)

For `G` countable at infinity, `π` irreducible and admissible, and a bilinear form `B : V →ₗ SmoothDual π →ₗ ℂ` with `B(π(g) x, π̃(g) λ) = B(x, λ)`:

1. some `c : ℂ` satisfies `B(x, λ) = c · λ(x)` for all `x` and `λ`;
2. if `B ≠ 0`, it is nondegenerate in each variable.

The published `SmoothInvariantPairingDualityStatement` (module `Smooth/Contragredient/InvariantPairingStatement`) concerns perfectness of invariant pairings between an admissible and a smooth representation. It is related but asserts neither conclusion.

### `CentralCharacterStatement` (III.1.10, central character, Lemma and Remark)

For `G` countable at infinity and a subgroup `Z` of the centre:

1. every smooth irreducible `π` has a central character on `Z`: some `χ : Z →* ℂˣ` with `π(z) x = χ(z) x`;
2. **Lemma.** If `π₁` and `π₂` admit central characters `χ₁ ≠ χ₂` on `Z`, every intertwiner `π₁ → π₂` is zero. Smoothness is not needed and is not assumed;
3. **Remark.** Every element `z` of Mathlib's `CatCenter (SmoothRep.{0, u, v} ℂ G)`, the endomorphisms of the identity functor and Renard's `ℨ(G)` through III.1.4, acts on every irreducible `V` by a scalar: `z_V(x) = c • x`.

For admissible representations and `Z = Z(G)`, part 1 is the third clause of the published `AdmissibleSchurStatement`, which also asserts local constancy. The Proposition of III.1.10 on characteristic subspaces is not restated here. For admissible representations it is the published `CentralCharacterDecompositionStatement` (module `Exponents/CentralStatement`).

### `HeckeCompletenessStatement` (III.1.11, Theorem)

For `G` countable at infinity with a left Haar measure `μ` and a nonzero `T` in the published Hecke algebra `Hecke.HeckeAlgebra μ`, some irreducible `π : SmoothRep.{0, u, v} ℂ G` satisfies `Hecke.heckeAction μ π T ≠ 0`. Here `heckeAction` is Renard's `π(T)`, with `H(G)` identified with test functions through `μ`. Irreducible smooth representations of such `G` have countable dimension, so they can be realized in every carrier universe `v`.

`RenardSchurStatements` is the conjunction of the five statements.

## Remarks

- The proofs are not formalized here. Renard deduces III.1.7 from Proposition I.5.1, III.1.8 from Theorem B.II, III.1.9 and III.1.10 from III.1.8, and III.1.11 from Lemma B.III via the non-nilpotent element `(f* ∗ f) μ`.
- The universes of the group and of the representation carriers are independent throughout.
