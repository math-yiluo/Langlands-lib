# Per-place restrictions of the actual automorphic differential action

For any number field `F : Type u`, natural rank `n` and existing
`OperatorRealization F n`, this module constructs the two complex-linear
Lie algebra actions

```text
S.realPlaceLieAction v :
  (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ S.Space
S.complexPlaceLieAction v :
  (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ S.Space.
```

Here `v` is respectively a real infinite place or a complex infinite
place, with the same representative-embedding convention as the published
mixed coordinates. The complex-place domain complexifies the full real
matrix Lie algebra, retaining both real directions at that place.

Both actions compose the existing genuine `S.complexLieAction` with the
injective per-place complex Lie inclusions from `ArchimedeanPlaceLie`.
They act on the original `S.Space`; the construction creates no new
coefficient carrier or existence premise.

The application formulas identify each operator with the existing
enveloping action of the inserted global Lie generator.
`inclusion_realPlaceLieAction` and `inclusion_complexPlaceLieAction`
identify the result in the original stable automorphic functions with
the same genuine enveloping differential. Finite adelic translations
commute with both actions by the already proved global commutation law.

`complexify_action_eq_sum_place` proves that the action of every genuine
global real Lie generator, after complexification, is the finite sum of
these place operators. Its proof applies the actual global action to
`sum_placeLieInclusions`, then uses linearity, evaluation of sums of
endomorphisms, and the pure-tensor inclusion formulas.

The two `Intertwiner` lemmas prove that every existing full automorphic
intertwiner retains every per-place operator. Their proofs are direct
applications of its existing genuine differential compatibility. They
therefore also apply to the underlying intertwiner of a full equivalence.

This is an internal restriction construction from `OperatorLieAction`
and `ArchimedeanPlaceLie`; no new original-literature assertion enters.
The number-field universe is arbitrary, all natural ranks are allowed,
and the coefficient field is `ℂ`. No topology is added to `S.Space`.

Restriction to a place on the whole global carrier does not extract an
irreducible local tensor factor. This module makes no assertion about
local irreducibility or admissibility, compact-group factorization,
globalization, archimedean Langlands attachment or local L/epsilon factors.
