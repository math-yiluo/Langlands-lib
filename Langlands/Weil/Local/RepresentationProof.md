# The nine-clause structure aggregate for the actual local Weil group

Author: Worker 265. This proof contribution proves the existing proposition
`Langlands.Weil.Local.LocalWeilRepresentationStatements.{u,v}` from
`Langlands.Weil.Local.RepresentationStatements`. The closing theorem is
`Langlands.Weil.Local.localWeilRepresentationStatements.{u,v}`. Its type is
exactly the named proposition, which unfolds to

```lean
∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p),
  LocalWeilContinuityFor.{u, v} F ∧
  LocalWeilGaloisTypeFor.{u, v} F ∧
  LocalWeilUnramifiedCorrectionFor.{u, v} F ∧
  LocalWeilIrreducibleReductionFor.{u, v} F ∧
  LocalUnramifiedCharacterClassificationFor F ∧
  LocalWeilCharacterNormalizationFor.{u, v} F ∧
  LocalCharacterInertiaFor F ∧
  LocalNormFaithfulnessFor F ∧
  LocalFrobeniusHypothesesFor F
```

The theorem covers every prime `p` and every actual finite p-adic field `F`
in universe `u`. Representation carriers lie in the independent universe
`v`. The proof adds no hypothesis, witness or assumed comparison. The local
Weil group, inertia, degree, projection, unramified characters and norm are
the actual constructions of `Langlands.Weil.Local.Assembly` that the
statement already uses. The statement pair
[RepresentationStatements.lean](RepresentationStatements.lean) and
[RepresentationStatements.md](RepresentationStatements.md) is unchanged, and
so are the pairs it imports.

## Implemented proof

The proof introduces the prime `p`, its `Fact p.Prime` instance and the
field `F`. It then builds the nine-fold conjunction as an anonymous
constructor, one published theorem per conjunct, in the stated order. Each
component theorem takes the implicit prime, its instance and the explicit
field `F`. The components with a representation-carrier universe are
applied at `.{u, v}`, and the others at `.{u}`. Nothing is reproved, and
no component module is modified.

| # | Conjunct | Published theorem used | Module |
| --- | --- | --- | --- |
| 1 | `LocalWeilContinuityFor.{u,v} F` | `localWeilContinuity.{u,v} F` | `Langlands.Weil.Local.ContinuityProof` |
| 2 | `LocalWeilGaloisTypeFor.{u,v} F` | `localWeilGaloisTypeFor.{u,v} F` | `Langlands.Weil.Local.GaloisCorrectionProof` |
| 3 | `LocalWeilUnramifiedCorrectionFor.{u,v} F` | `localWeilUnramifiedCorrectionFor.{u,v} F` | `Langlands.Weil.Local.GaloisCorrectionProof` |
| 4 | `LocalWeilIrreducibleReductionFor.{u,v} F` | `localWeilIrreducibleReductionFor.{u,v} F` | `Langlands.Weil.Local.IrreducibleReductionProof` |
| 5 | `LocalUnramifiedCharacterClassificationFor F` | `localUnramifiedCharacterClassificationFor.{u} F` | `Langlands.Weil.Local.CharacterNormProof` |
| 6 | `LocalWeilCharacterNormalizationFor.{u,v} F` | `localWeilCharacterNormalizationFor.{u,v} F` | `Langlands.Weil.Local.CharacterNormProof` |
| 7 | `LocalCharacterInertiaFor F` | `localCharacterInertia.{u} F` | `Langlands.Weil.Local.ContinuityProof` |
| 8 | `LocalNormFaithfulnessFor F` | `localNormFaithfulnessFor.{u} F` | `Langlands.Weil.Local.CharacterNormProof` |
| 9 | `LocalFrobeniusHypothesesFor F` | `localFrobeniusHypothesesFor.{u} F` | `Langlands.Weil.Local.CharacterNormProof` |

All names are in the namespace `Langlands.Weil.Local`. The module imports
the four component modules by their Lean names and nothing else.

## Checks

`lean_check` compiles the module without errors or warnings. The inspected
closing theorem has level parameters `u` and `v`. Its axioms are only
`propext`, `Classical.choice` and `Quot.sound`.

The module ends with two `example` declarations. Each assigns the unapplied
constant `@localWeilRepresentationStatements.{u, v}`, with no supplied
arguments, to a complete type:

- the named proposition `LocalWeilRepresentationStatements.{u, v}`;
- the fully unfolded telescope shown above, with the explicit prime, the
  prime instance, the field and all nine conjuncts.

Both compile. This follows
[complete-declaration-checks](../../../notes/lean/complete-declaration-checks.md).
These examples are development checks, not the formal exact-target check.

## Provenance

This aggregate is an internal packaging of the nine accepted actual-local
structure results. It adds no mathematics beyond the conjunction. No original
source states the full conjunction verbatim. The source of each clause is
recorded in the declaration and source map of
[RepresentationStatements.md](RepresentationStatements.md). The sources are
Henniart 1980, §2.1–2.6 (literature ID
`henniart-1980-weil-representations`), and Tate 1979, (1.4.1), (1.4.6),
(2.1)–(2.2.1) and 4.1.3 (literature ID
`tate-1979-number-theoretic-background`). Several clauses are derived
consequences, as that map records.

The proofs of the components, and their own provenance, are explained in
their Markdown files:

- [ContinuityProof.md](ContinuityProof.md), by Worker 106: conjuncts 1 and 7;
- [GaloisCorrectionProof.md](GaloisCorrectionProof.md), by Worker 32:
  conjuncts 2 and 3;
- [IrreducibleReductionProof.md](IrreducibleReductionProof.md), by
  Worker 265: conjunct 4;
- [CharacterNormProof.md](CharacterNormProof.md), by Worker 85:
  conjuncts 5, 6, 8 and 9.

Worker 265 wrote this assembly. The components are earlier Library work,
used by their Lean names.

## Scope

The theorem asserts only the nine structure results on representations of
the actual local Weil group of a single finite p-adic field. It does not
assert or use the local Langlands correspondence, a reciprocity map or any
correspondence between Weil representations and representations of
`GL_n(F)`. Restriction and induction along finite extensions,
Weil–Deligne blocks and the assembly of the correspondence are separate
tasks.
