# Proof of the quotient by a finite locally free equivalence relation with affine classes

Authors: Worker 934 wrote this Lean module and this Markdown.

The theorem `Langlands.AlgebraicGeometry.finiteLocallyFreeEquivalenceRelationQuotient.{u}`
proves the proposition
`Langlands.AlgebraicGeometry.FiniteLocallyFreeEquivalenceRelationQuotientStatement.{u}` for
an arbitrary universe `u`, with exactly its stated hypotheses. Given `t s : R ⟶ U` forming a
finite locally free equivalence relation whose classes `t(s⁻¹{u})` each lie in an affine
open, it produces a scheme `M` and a finite, flat, locally finitely presented, surjective
`q : U ⟶ M` with `IsPullback t s q q`.

## Sources

The mathematical source is Stacks Project, Properties of Algebraic Spaces, Proposition
66.14.1 ([Tag 07S6](https://stacks.math.columbia.edu/tag/07S6)), registered as
`stacks-obtaining-a-scheme-07S5-07S6-07S7-html-2026-11-02`, in the case `E = U` of its
footnote 1; the statement Markdown explains the correspondence.

The proof is the ported FLT theorem
`AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation` from the
Anthropic Lean formalisation of Fermat's Last Theorem (registered source
`anthropic-flt-complete-lean-source-6e837e75`, commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`; Apache License 2.0, Copyright 2026 Anthropic,
PBC; licence files in `licenses/Anthropic-FLT/`). This candidate adds its port, in six
modules whose Markdown files list the source files, their SHA-256 hashes and every change:

- `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation`
  and its proof module
  `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation`
  (invariant affine cover, affine quotients, gluing). This proof module is adapted: its two
  affine-case inputs are the published Library theorems
  `Langlands.AlgebraicGeometry.FiniteLocallyFreeQuotient.existsAffineQuotient` (Stacks Tag
  03BM) and
  `AlgebraicGeometry.Scheme.exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation`
  (Stacks Tag 03JE).
- `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict`
  and `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict`
  (gluing local quotients over an invariant open cover).
- `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback`
  and `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback`
  (base change of a finite locally free quotient).

## Proof

The FLT theorem has hypotheses on a pair `s t : R ⟶ X`, with the relation "`x = φ ≫ s` and
`y = φ ≫ t`". The proof applies it with `X := U` and with its `s` and `t` taken to be the
`s` and `t` of the statement. The statement's affine-class hypothesis is then literally the
FLT hypothesis `haff`, and the six morphism-property hypotheses become instances.

- `hj` (the FLT `hmono`): if `a ≫ s = b ≫ s` and `a ≫ t = b ≫ t`, then `a` and `b` agree
  after composing with `prod.lift t s` (check both product projections), so `a = b` because
  `prod.lift t s` is a monomorphism.
- `hequiv`: the relation "`r ≫ s = x` and `r ≫ t = y` for some `r : T ⟶ R`" is an
  equivalence relation on `T ⟶ U`. Reflexivity is the statement's diagonal hypothesis.
  Symmetry uses the statement's reversal hypothesis: for `r` there is `r'` with
  `r' ≫ t = r ≫ s` and `r' ≫ s = r ≫ t`. Transitivity uses the composition hypothesis: if
  `r ≫ s = x`, `r ≫ t = y`, `r' ≫ s = y` and `r' ≫ t = z`, then `r' ≫ s = r ≫ t`, so it
  gives `r''` with `r'' ≫ t = r' ≫ t = z` and `r'' ≫ s = r ≫ s = x`.

The FLT theorem returns `M`, `q : U ⟶ M` and the equation `s ≫ q = t ≫ q` with `q` finite,
flat, locally of finite presentation and surjective, `IsPullback s t q q`, and a
coequalizer property. The proof keeps the four morphism properties and turns
`IsPullback s t q q` into the required `IsPullback t s q q` with `IsPullback.flip`. It
discards the equation, which `IsPullback` already contains, and the coequalizer property,
which the statement does not ask for.

## Declarations

- theorem `Langlands.AlgebraicGeometry.finiteLocallyFreeEquivalenceRelationQuotient`

## Dependencies

- `Langlands.AlgebraicGeometry.FiniteLocallyFreeEquivalenceRelationQuotientStatement`
  (the statement).
- `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation`
  (ported with this proof; it imports the other five ported modules and the published
  Library modules listed in their Markdown).

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
