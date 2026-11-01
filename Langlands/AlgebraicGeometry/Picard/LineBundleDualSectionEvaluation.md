# Evaluation against a global section of a dual line bundle

This internal helper constructs an actual morphism from a line bundle to the
structure module on an arbitrary scheme. It proves that the morphism is an
isomorphism on the open where the chosen dual section generates. There are no
Noetherian, quasi-affine, reducedness, or nonemptiness hypotheses.

All declarations below are in
`Langlands.AlgebraicGeometry.Picard.LineBundle` and are polymorphic in the
universe of the scheme.

`dual D` packages the module sheaf `Langlands.Scheme.Modules.dual D.obj` as a
line bundle, using the published `isLocallyFreeRankOne_dual`.

For a global section `t : GlobalSections D.dual.obj`, `evalSection D t` is the
actual composite

```text
D --right unitor inverse--> D ⊗ O_X
  --identity ⊗ sectionHom(t)--> D ⊗ D^∨
  --dualTensorEval--> O_X.
```

The source and target are module sheaves, and `O_X` is
`SheafOfModules.unit X.ringCatSheaf`. This construction uses the published
section morphism and tensor evaluation.

`isIso_restrict_evalSection D t U hU` proves that restriction of this composite
to `U` is an isomorphism when
`hU : U ≤ trivializationOpen D.dual.obj t`. The maximality comparison for the
trivialization open makes the restricted `sectionHom` an isomorphism. Transport
along `restrictFunctorIsoPullback` gives the same fact for pullback. Naturality
and invertibility of `pullbackTensorComparison` show that the pullback of
`identity ⊗ sectionHom(t)` is an isomorphism. The right unitor and
`dualTensorEval` are isomorphisms, the latter by the rank-one evaluation
theorem. Their pulled-back composite is therefore an isomorphism. Transport
back to restriction proves the assertion.

`isIso_stalk_evalSection_of_mem D t hx` applies this result to the whole
trivialization open and uses `isIso_stalk_restrict_iff` to obtain an
isomorphism of the underlying additive stalks at every
`x ∈ trivializationOpen D.dual.obj t`.

## Provenance and scope

This is an internal construction derived from the Library's section morphism,
rank-one dual evaluation, and pullback tensor comparison. Its proof is the
categorical composition argument described above and requires no additional
literature assertion. It supplies the dual-section map for the ideal-embedding
task. It does not assert a global monomorphism for an arbitrary dual section;
choosing a suitable section and proving global injectivity remain separate
obligations.
