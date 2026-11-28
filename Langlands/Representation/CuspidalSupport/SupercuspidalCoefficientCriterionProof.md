# Supercuspidality by coefficients (Renard VI.2.1, Theorem (a) ⇔ (b)): proof

Module `Langlands.Representation.CuspidalSupport.SupercuspidalCoefficientCriterionProof`,
namespace `Langlands.Aubert.General.RepresentedParabolic`, universe parameters `u, v`.

The theorem `supercuspidalCoefficientCriterion` proves exactly the published statement
`SupercuspidalCoefficientCriterionStatement.{u, v}` (module
`Langlands.Representation.CuspidalSupport.SupercuspidalCoefficientCriterionStatement`).
[Statement](SupercuspidalCoefficientCriterionStatement.md)

```lean
theorem supercuspidalCoefficientCriterion :
    SupercuspidalCoefficientCriterionStatement.{u, v}
```

## What is proved

Let `k : Type u` be a nonarchimedean local field (with `T2Space`), `G` a connected
reductive group scheme over `Spec k`, and give `G(k)` the canonical topology
`RationalPointFamily.pointTopology`, with the `LocallyCompactSpace` and
`NonarchimedeanGroup` binders of the statement. Then for every smooth complex
representation `A : SmoothRep.{0, u, v} ℂ G(k)`, `IsSupercuspidal A` holds if and only if,
for every `w ∈ A` and every linear form `ℓ` that is a smooth vector of the dual action,
there is a compact `C ⊆ G(k)` with
`Function.support (matrixCoefficient A.representation ℓ w) ⊆ C · Z`, where `Z` is the
centre of `G(k)`.

The theorem has no hypotheses: it keeps the universes `u` (field) and `v` (carrier) of the
statement and adds no rank, splitness, characteristic or admissibility condition. Its
axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Proof

The Lean term is one application:

```lean
supercuspidalCoefficientCriterionReduction
  Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence
```

- `supercuspidalCoefficientCriterionReduction` (module
  `Langlands.Representation.CuspidalSupport.SupercuspidalCoefficientCriterionReduction`)
  proves `SupercuspidalCoefficientCriterionReductionStatement.{u, v}`, that is,
  `JointSpecialCompactBasisExistenceStatement.{u} → SupercuspidalCoefficientCriterionStatement.{u, v}`.
  [Reduction](SupercuspidalCoefficientCriterionReduction.md) Its two directions are:
  - (b) ⇒ (a), `isSupercuspidal_of_coefficients_compactModCenter`, which uses no
    premise: coefficients compactly supported modulo `Z` restrict to compactly supported
    coefficients on the common norm kernel `⁰G`, because `⁰G` is open and closed and
    `⁰G ∩ Z` is compact (Renard V.2.6), and the Library's (c) ⇒ (a),
    `isSupercuspidal_of_compactRestriction`, then gives supercuspidality;
  - (a) ⇒ (b), `coefficients_compactModCenter_of_isSupercuspidal`, which uses the joint
    statement: at one special vertex it takes the compact `K0`, the finite Cartan cover
    `G(k) = K0 · F₀ · C_A^+ · K0`, a uniform bound `B` on the simple-root pairings of the
    torus parts at which a coefficient of the cuspidal representation does not vanish, and
    the finiteness modulo `Z` of the torus elements with pairings in `[0, B]`; it obtains
    the compact set `C = K0 · F₀ · T0 · K0` with `T0` finite.
- `Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence` (module
  `Langlands.BruhatTits.SpecialCompact.JointBasisProof`) proves
  `JointSpecialCompactBasisExistenceStatement.{u}` (Renard V.5.1–V.5.2 at one geometric
  special vertex) for every universe `u`, with no hypotheses.
  [Joint statement proof](../../BruhatTits/SpecialCompact/JointBasisProof.md)

Both universes match: the reduction is stated at `.{u, v}` with premise at `.{u}`, and the
joint proof is universe polymorphic, so Lean instantiates it at the field universe `u`.

## Relation to Renard's proof

Renard (VI.2.1, printed pp.137–139 / PDF pp.143–145) proves the theorem as the cycle
(b) ⇒ (c) ⇒ (a) ⇒ (b), where (c) says that the restriction to `⁰G` is compact. The
Library's proof follows the same cycle; the differences of route (a group lemma in place of
quotient groups for (b) ⇒ (c), and a direct uniform bound over a finite Cartan cover in
place of Renard's contraposition with sequences for (a) ⇒ (b)) are described in the
Markdown of the reduction module.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, VI.2.1,
Théorème, equivalence of (a) and (b).

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.CuspidalSupport.SupercuspidalCoefficientCriterionReduction` | `supercuspidalCoefficientCriterionReduction`, and through it the target statement |
| `Langlands.BruhatTits.SpecialCompact.JointBasisProof` | `jointSpecialCompactBasisExistence` |
