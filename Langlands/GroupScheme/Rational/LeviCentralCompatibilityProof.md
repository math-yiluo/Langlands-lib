# Split components of nested Levis and characters of standard Levis: the conjunction

Worker 962, Task 7818. Module
`Langlands.GroupScheme.Rational.LeviCentralCompatibilityProof`, namespace
`Langlands.GroupScheme`, universe parameter `u` (the universe of the base
field).

The theorem `Langlands.GroupScheme.leviCentralCompatibility` proves
[`LeviCentralCompatibilityStatements.{u}`](LeviCentralCompatibilityStatements.md).
Its type is exactly that proposition. By definition the proposition is the
conjunction

`LeviSplitComponentInclusionStatement.{u} ∧ StandardLeviCharacterAnnihilatorStatement.{u}`.

## Scope

The scope is that of the paired statement file:

- Both conjuncts hold over an arbitrary field `k` (in universe `u`) for a
  connected reductive group `G`.
- `LeviSplitComponentInclusionStatement` concerns rational Levi factors
  `lM : M ⟶ P` and `lL : L ⟶ Q` of two parabolic subgroups `p : P ⟶ G` and
  `q : Q ⟶ G`, and a morphism `m : M ⟶ L` with `m ≫ lL ≫ q = lM ≫ p`, so
  that `M ⊆ L` inside `G`. For any split components `aL : A_L ⟶ L` and
  `aM : A_M ⟶ M` (Renard's *composantes déployées*), it gives a homomorphism
  `f : A_L ⟶ A_M` of commutative group schemes with
  `CommGroupScheme.groupHom f ≫ aM ≫ m = aL`.
- `StandardLeviCharacterAnnihilatorStatement` concerns a maximal split torus
  `i : T ⟶ G`, a generic cocharacter `ν`, a set `J` of simple relative roots
  for `ν`, a closed subgroup `j : L ⟶ G` that represents the standard Levi of
  `J`, a morphism `t : T ⟶ L` with `t ≫ j = i`, and integral reflection data
  `D`, which supply the coroots. It states that the range of
  `rationalCharacterRestrictReal t` (real rational characters of `L`
  restricted to `T`) equals `corootAnnihilator i D J`, the real characters of
  `T` that vanish on the coroots of `J`.

## Lean proof

The proof is the anonymous constructor

`⟨leviSplitComponentInclusion, standardLeviCharacterAnnihilator⟩`.

It pairs two published theorems, each at the universe `u`:

| Conjunct | Published theorem | Module |
| --- | --- | --- |
| `LeviSplitComponentInclusionStatement.{u}` | `Langlands.GroupScheme.leviSplitComponentInclusion` | `Langlands.GroupScheme.Rational.LeviSplitComponentInclusionProof` |
| `StandardLeviCharacterAnnihilatorStatement.{u}` | `Langlands.GroupScheme.standardLeviCharacterAnnihilator` | `Langlands.GroupScheme.Rational.StandardLeviCharacterAnnihilatorProof` |

This file proves nothing beyond the pairing. The mathematical arguments are
in the two component proofs and their Markdown
([inclusion](LeviSplitComponentInclusionProof.md),
[characters](StandardLeviCharacterAnnihilatorProof.md)).

The theorem depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`: V.3.6 (printed
p. 111 / PDF p. 117) and V.3.13 (printed p. 112 / PDF p. 118). The statement
file explains how the two conjuncts formalize those sections.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.GroupScheme.Rational.LeviCentralCompatibilityStatements` | the target `LeviCentralCompatibilityStatements` |
| `Langlands.GroupScheme.Rational.LeviSplitComponentInclusionProof` | `leviSplitComponentInclusion` |
| `Langlands.GroupScheme.Rational.StandardLeviCharacterAnnihilatorProof` | `standardLeviCharacterAnnihilator` |
