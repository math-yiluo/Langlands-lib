# Absence of degenerate mirabolic submodules over local fields: proof

Lean module: `Langlands.Representation.Whittaker.LocalFieldMirabolicNondegeneracyProof`.

## Statement

`Langlands.Whittaker.localFieldMirabolicNondegeneracy` proves the Library statement
`Langlands.Whittaker.LocalFieldMirabolicNondegeneracyStatement.{uF, uV}` at independent universes
`uF` (the field) and `uV` (the representation space). This is Theorem 4.9 of Bernstein and
Zelevinsky, *Induced representations of reductive p-adic groups I*, Ann. Sci. ÉNS 10 (1977)
(literature id `bernstein-zelevinsky-1977-induced-i`, printed p. 456, PDF p. 17). An irreducible
nondegenerate representation of `GL_(n+1)(F)` has no nonzero degenerate `P`-submodules. In the
statement, `F` is any field with instances `ValuativeRel F`, `TopologicalSpace F` and
`IsNonarchimedeanLocalField F`, of any characteristic, and nondegeneracy is the Library's
`IsGeneric`. A `P`-submodule is degenerate when its full upper-unipotent character quotient
vanishes. The theorem has no hypotheses beyond those of the statement.

## Proof

The proof is one term. The bridge
`Langlands.Whittaker.LocalFieldMirabolicNondegeneracyBridge.localFieldMirabolicNondegeneracy_of_packaged`
(module `Langlands.Representation.Whittaker.LocalFieldMirabolicNondegeneracyBridge`) derives the
statement from its form for packaged fields: every `F : Langlands.AllFieldBZ.LocalFieldPackage`
with `T : F.TopologicalData`. That form is the all-field theorem
`Langlands.AllFieldBZ.Whittaker.PadicMirabolicNondegeneracy.mirabolicNondegeneracy` (module
`Langlands.AllFieldBZ.Representation.Whittaker.PadicMirabolicNondegeneracy`). The bridge takes
`F` explicitly, so the argument is `fun _ => mirabolicNondegeneracy`.

The all-field theorem is the end of a port. Worker 5677 proved Theorem 4.9 for the Library's p-adic
field package `Langlands.PadicField p` in an unpublished draft, using the Library's proof of
Theorem 4.11. Worker 71's port script restated that argument and the field-dependent part of
its Library import closure over `Langlands.AllFieldBZ.LocalFieldPackage`, in the modules
`Langlands.AllFieldBZ.*`. Their foundation is `Langlands.AllFieldBZ.LocalField.Definitions`. The
Markdown of those modules describes each step.

## Guide to the port modules

The modules `Langlands.AllFieldBZ.*` in this contribution are exactly the import closure of this
module inside `Langlands.AllFieldBZ`. Each has its own Markdown file.

- **Naming.** A module `Langlands.AllFieldBZ.<Path>` is the port of the Library module
  `Langlands.<Path>`, and a declaration `Langlands.AllFieldBZ.X` is the port of `Langlands.X`.
  Declarations in namespaces outside `Langlands` get the suffix `_allFieldBZ`. A port module
  imports its original module and ports only the declarations whose statements or proofs depend on
  the p-adic field package `Langlands.PadicField p`. Field-independent declarations are used from
  the original. The Markdown of each generated module lists its ported declarations and the
  systematic changes: `PadicField p` becomes `LocalFieldPackage`, and the prime `p` and its
  `Fact p.Prime` instance are dropped.
- **Hand-written modules.**
  - The foundation `Langlands.AllFieldBZ.LocalField.Definitions`.
  - `Langlands.AllFieldBZ.Representation.Geometric.IntersectionLeviDiagonalCharacterInfinite`. It
    replaces a Library theorem that assumes characteristic zero by one that assumes only that `F`
    is infinite.
- **Hand-edited proofs.** The Lean source marks each one with a `-- MANUAL` comment, and the
  module's Markdown explains it under "Hand edits":
  - `Group.GL.NormalizedCharacter` and `Group.GL.BlockContractionProof`, where the p-adic proofs
    used the canonical norm.
  - `HarmonicAnalysis.PadicScalarHaarScalingProof`, for the topological instances.
  - `Representation.Classification.SupercuspidalDerivativesProof`. Worker 5677's edit uses the
    published all-field Whittaker multiplicity one `Langlands.Whittaker.localFieldMultiplicityOne`.
- **Ports of unpublished drafts.** The three modules
  `Langlands.AllFieldBZ.Representation.Whittaker.PadicMirabolicNondegeneracy{Order,Embedding,}`
  port Worker 5677's unpublished p-adic deduction of Theorem 4.9 from Theorem 4.11. They do not
  import those drafts.
- **Build time.** Lake builds of three modules take a long time:
  - `Derivative.MirabolicProductMinusLeftPsiInduction`, 23 to 25 minutes.
  - `Derivative.MirabolicProductMinusLeftPhiInductionNormalization`, about 19 minutes.
  - `Derivative.MirabolicProductMinusLeftPhiStagesComparison`, about 16 minutes.

  Their Markdown has a build note. The Library's original p-adic modules are just as slow.

## Provenance

Worker 5677 wrote this module. Worker 71 added the docstrings and this Markdown.
