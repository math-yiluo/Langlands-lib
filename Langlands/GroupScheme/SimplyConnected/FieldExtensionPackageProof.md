# The field-extension package for semisimplicity, simple connectedness and covers

Author: Worker 4036.

The theorem `Langlands.GroupScheme.simplyConnected_fieldExtension` proves
exactly the published
`Langlands.GroupScheme.SimplyConnectedFieldExtensionStatement.{u}` from
`Langlands.GroupScheme.SimplyConnected.FieldExtensionStatement`. Its type is
the bare statement constant, with no added hypotheses, for an arbitrary
universe `u`.

The statement is the conjunction

```lean
IsSemisimpleFieldExtensionStatement.{u} ∧ IsSimplyConnectedFieldExtensionStatement.{u} ∧
  IsSimplyConnectedCoverFieldExtensionStatement.{u}
```

Each component quantifies over arbitrary fields `k K : Type u` of any
characteristic and an arbitrary `Algebra k K`, and concerns the actual base
change `GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))`.
The extension need not be algebraic, separable, finite or perfect.

## Implemented proof

The proof is the anonymous constructor of the nested conjunction, with the
three component proofs at the same universe `u`:

1. `isSemisimpleFieldExtension : IsSemisimpleFieldExtensionStatement.{u}`,
   published in `Langlands.GroupScheme.SimplyConnected.SemisimpleFieldExtensionProof`.
2. `isSimplyConnectedFieldExtension : IsSimplyConnectedFieldExtensionStatement.{u}`,
   published in `Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof`.
3. `isSimplyConnectedCover_fieldExtension : IsSimplyConnectedCoverFieldExtensionStatement.{u}`,
   from `Langlands.GroupScheme.SimplyConnected.FieldExtensionProof`. That
   theorem assembles the four fields of `IsSimplyConnectedCover π_K` for every
   supplied cover `π` from components 1 and 2, the published central-isogeny
   base-change theorem `centralIsogenyBaseChange`, and the published universal
   property `simplyConnectedCentralCoverUniversalProperty` over `K`; its
   Markdown describes the details.

The module imports only `Langlands.GroupScheme.SimplyConnected.FieldExtensionProof`,
which in turn imports the statement module and the two published component
proofs.

## Provenance and dependencies

This is a derived assembly of three proofs. No definition, target statement
or imported file is changed. No `sorry`, `admit` or new axiom is used.

The mathematical sources of the package are recorded in the statement's
Markdown: CGP, *Pseudo-reductive groups*, second edition (2015), source
`conrad-gabber-prasad-2015-pseudo-reductive`, Corollary A.4.11(1), printed
pp.500-501 (PDF pp.526-527); and Milne, *Algebraic Groups* (2017), source
`milne-2017-algebraic-groups`, Propositions 19.10 and 19.13, printed p.400
(PDF p.416). The Lean proof follows the Library interfaces rather than the
sources' arguments.
