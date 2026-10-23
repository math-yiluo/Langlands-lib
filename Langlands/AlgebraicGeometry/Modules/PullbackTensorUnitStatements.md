# Pullback compatibility with the explicit tensor unitors

This module states the left and right tensor-unit laws for the canonical
scheme-module pullback comparisons. Its declarations are propositions in
`Langlands.Scheme.Modules`, with arbitrary universe `u`. They quantify over
every pair of schemes `X Y : Scheme.{u}`, every morphism `f : X ⟶ Y`, and
every module sheaf `M : Y.Modules`.

Write `F` for the existing `AlgebraicGeometry.Scheme.Modules.pullback f`,
`O_X` for `structureSheaf X`, and `O_Y` for `structureSheaf Y`. Write
`δ(A,B)` for `pullbackTensorComparisonApp f A B`, and `ε` for
`(pullbackUnitIso f).hom : F(O_Y) ⟶ O_X`. The tensors and their morphisms
are the published `tensorObj` and `tensorMap`. The unitors are the published
`tensorLeftUnitor` and `tensorRightUnitor`, constructed by sheafifying the
presheaf unitors and composing with the sheafification counit.

`PullbackTensorLeftUnitorStatement` asserts that the composite

```text
F(O_Y ⊗ M) --δ(O_Y,M)--> F(O_Y) ⊗ F(M)
  --ε ⊗ id--> O_X ⊗ F(M) --tensorLeftUnitor(F(M)).hom--> F(M)
```

equals `F.map (tensorLeftUnitor M).hom`.

`PullbackTensorRightUnitorStatement` asserts that the composite

```text
F(M ⊗ O_Y) --δ(M,O_Y)--> F(M) ⊗ F(O_Y)
  --id ⊗ ε--> F(M) ⊗ O_X --tensorRightUnitor(F(M)).hom--> F(M)
```

equals `F.map (tensorRightUnitor M).hom`.

`PullbackTensorUnitCoherenceStatement` is the conjunction of these two
propositions. In particular, each equality uses the fixed comparison maps
from the published `PullbackTensor` and `PullbackUnit` modules. It does not
quantify over freely chosen tensor or unit comparisons.

These statements need no monoidal instance on `X.Modules` or `Y.Modules`.
The explicit tensor unitors are already defined without such an instance,
and `structureSheaf X` is definitionally `SheafOfModules.unit X.ringCatSheaf`,
which is the unit object used by `pullbackUnitIso`. No tensor-comparison
invertibility, geometric condition on `f`, or coherence hypothesis is
assumed.

This is internal categorical infrastructure. The equations have the form of
the forward-unitor laws `CategoryTheory.Functor.OplaxMonoidal.left_unitality_hom`
and `right_unitality_hom` in the pinned Mathlib module
`CategoryTheory/Monoidal/Functor.lean`, specialized as explicit diagrams to
the published scheme-module tensor, unitors and pullback comparisons. That
provenance identifies the intended coherence laws; this module neither
installs an oplax monoidal structure nor applies those theorems to assume
the desired equations.

The imported tensor constructions and their source provenance remain
unchanged. The present diagrams are a separate obligation from
`PullbackUnitCoherenceStatement`, whose three laws characterize the unit
comparison by adjunction and express its compatibility with pullback
identity and composition.

This module supplies only Prop-valued definitions, with no proofs or
instances asserting them. Proving both laws is a focused prerequisite for
the full monoidal pullback construction. The remaining associativity and
symmetry laws, invertibility of the tensor comparison, and comparison of
these explicit unitors with the unitors of a subsequently constructed
monoidal structure are not asserted or proved here.
