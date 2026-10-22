# Finite selection, Galois enlargement and orbit counting

This is Worker 30's statement contribution of elementary prerequisite propositions.
It uses actual finite sets, functions, group actions and intermediate fields.
It does not define substitutes for Weil or supercuspidal representation classes,
and it does not yet specialize these arguments to those classes. No theorem
in this file has been proved or independently accepted.

## Exact content

`FiniteSeparationStatement` starts with a finite subset `P` of a type `X`.
For an evaluation function on tests `T`, its internal hypothesis says that every
distinct pair in `P` has a test with different values. Its conclusion selects
a finite family of tests whose simultaneous equalities imply equality in `P`.
The values belong to an arbitrary type `R`; they can later be entire local
factor functions, so the proposition does not confuse equality of such
functions with equality at one value of the complex variable. Empty and
singleton candidate sets are allowed.

`FiniteTestLiftingStatement` asks for preimages only of the selected finite
test family under a specified function `S → T`. It concludes existence of
a finite family of lifts covering all those tests, with every selected lift
mapping into the original test family. It does not assume an equivalence of
the whole source and target.

`FiniteLiftedSeparationStatement` combines the preceding two uses of a finite
family: if the specified tests already separate and each of them lifts,
finitely many lifts separate by evaluation through the projection. This
component needs no separate finiteness assumption on `P`, since the finite
separating family is already supplied. The missing lower-rank surjectivity in
the intended application remains a substantive theorem input. It is not
created by the finite-choice conclusion.

`FiniteGaloisEnlargementStatement` quantifies actual intermediate fields of
an actual extension `K/F`. Each member of the finite input family is assumed
finite-dimensional and Galois over `F`. The conclusion is an intermediate
field `L` with both properties, containing every input field. There is no
assumption that the ambient extension is finite, Galois or algebraically
closed. The finite compositum inside it supplies the expected witness; the
empty family is covered by the embedded base field. These are theorem
obligations, not fields of an auxiliary-extension structure.

`FiniteCountingStatement` states that a map injective on a finite source set
and mapping into a finite target set of the same finite cardinality is onto
that target set. Both finiteness assumptions precede the natural-cardinality
equality. In particular, the convention that `Set.ncard` is zero for an
infinite set cannot be used to infer any surjectivity.

`FiniteOrbitCountingStatement` assumes an actual action of a group `U` on
`X` and `Y`, an equivariant injection `f`, and families of finite source and
target subsets indexed by `I`. The corresponding finite subsets have equal
natural cardinality, and `f` carries each source subset into its target
subset. Every element of `Y` can be moved by an element of `U` into one of
these target subsets. The conclusion is surjectivity of `f` on all of `Y`.
The intended argument first obtains surjectivity on each finite target
subset, then uses the inverse group element and equivariance to return to
the original target element. No finiteness of `U`, `X`, `Y` or `I`, uniqueness
of orbit representatives, or freeness of the group actions is asserted.

`FiniteAuxiliaryStatement` conjoins exactly these six components. All nine
type universes are independent. The group, action, field and algebra
instances appear only in components that use them, apart from their explicit
presence in the common closing target. Each substantive assertion is a
`Prop` definition; none is an axiom or assumed theorem-valued structure field.

## Original-source correspondence and generalization

Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un
corps p-adique* (2000), section 4.3, printed pp.452–453, first uses a finite
candidate set with fixed central character and conductor. Distinct candidates
are separated by lower-rank supercuspidal epsilon factors, the tests are
twisted to finite-order central character, and lower-rank surjectivity
provides parameter lifts. Finitely many such lifts are retained. The
compositum of their auxiliary extensions and the field fixed by the input
parameter's kernel supplies a common extension. Both pages were read directly.

- Literature ID: `henniart-2000-simple-proof`.
- Retained PDF: `C:/Central-Library/Henniart--Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique--2000.pdf`.
- SHA256: `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.

The first four propositions isolate and generalize the elementary finite-set
and compositum steps in that argument. They do not assert that the local
candidate set is finite, establish the local converse theorem, construct
the parameter lifts, or compare local factors after enlarging an extension.
The general intermediate-field statement is an elementary field-theoretic
generalization, rather than a literal theorem numbered in Henniart's paper.

Henniart, *La conjecture de Langlands locale numérique pour GL(n)* (1988),
section 2.8, printed pp.506–507, passes from injections on representation
classes to injections on normalized finite sets; equality of their finite
counts gives bijectivity there and then surjectivity in the original ranks.
This is the provenance of the last two elementary propositions. Section 2.8
and its concluding paragraph on p.507 were read directly.

- Literature ID: `henniart-1988-numerical`.
- Retained PDF: `C:/Central-Library/Henniart--La conjecture de Langlands locale numerique pour GL(n)--1988.pdf`.
- SHA256: `3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`.

The group-action formulation is a sufficient elementary criterion extracted
from this reasoning. It is not a replacement statement for Henniart's
Theorem 1.2. In particular, no conductor formula, equality of local counts,
normalization at a uniformizer, or preservation of an unramified twist is
assumed merely by naming `source`, `target` or `U`. Those actual mathematical
objects and their properties must be supplied and proved in the local
specialization. The unresolved Swan-zero summation-range issue in the
printed numerical formulas is not hidden by an infinite-cardinality equality.

## Dependencies and remaining scope

The only implementation dependency is the prepared Lean 4.34.0 environment
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1, with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. Imports provide the genuine
set-cardinality, group-action, intermediate-field, finite-dimensionality and
Galois predicates. There are no project theorem imports. Native compilation
and printing of all seven declaration bodies completed with exit code zero.
The printed types were read in full: the six components and their conjunction
return `Prop`, retain the stated internal hypotheses and all nine independent
universes, and impose no omitted ambient finiteness or Galois hypothesis.
This is elaboration evidence, not a proof of the propositions.

The broad host task still requires propositions over actual local Weil and
supercuspidal classes, actual conductors and central characters, the entire
rank induction and its lower-rank lifting hypotheses, the global comparison
after enlargement, independence of global and twist choices, and the full
numerical correspondence theorem. The other construction owners retain
their interfaces. This elementary draft and its future publication cannot
by themselves complete those requirements.

## Module placement and compatibility

Worker 30 authored the proposition definitions and source explanations above.
Worker 0 drafted this organizational migration in the earlier test run under
placement task `6ca20150-e0aa-456a-8d26-2678a9b0c81e` and restored the four-file
draft for this run. Worker 66 executes and validates the move under current task
`239c0ee4-c0db-4113-bf9a-20d742b145f3`. The initial workspace Library base is
`30ceb5a0d89d8094c1663fc19f35416519b9a125`, containing 269 Lean modules before
this move. During validation the Library advanced to
`115fa73cc7e02f57b8baadcc0d37433783a7152a`, adding three unrelated paired
modules. Those accepted files were copied unchanged for the final whole-tree
validation; the migration still changes exactly four paths. The preceding mathematical account is retained verbatim, including
its historical environment identifier and retained-source paths. The current
prepared environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, pinning the same
Lean 4.34.0 and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
This placement makes no mathematical change and proves none of the six
component assertions.

| Previous module | Canonical module | Compatibility |
| --- | --- | --- |
| `Langlands.Henniart.FiniteAuxiliaryStatement` | `Langlands.Correspondence.FiniteAuxiliaryStatement` | The previous module imports the canonical module and declares no duplicate objects. |

The same map applies to the paired `.lean` and `.md` paths. All declaration
names retain the namespace `Langlands.Henniart`, with no declaration rename:

| Previous declaration | Retained declaration in the canonical module |
| --- | --- |
| `Langlands.Henniart.FiniteSeparationStatement` | `Langlands.Henniart.FiniteSeparationStatement` |
| `Langlands.Henniart.FiniteTestLiftingStatement` | `Langlands.Henniart.FiniteTestLiftingStatement` |
| `Langlands.Henniart.FiniteLiftedSeparationStatement` | `Langlands.Henniart.FiniteLiftedSeparationStatement` |
| `Langlands.Henniart.FiniteGaloisEnlargementStatement` | `Langlands.Henniart.FiniteGaloisEnlargementStatement` |
| `Langlands.Henniart.FiniteCountingStatement` | `Langlands.Henniart.FiniteCountingStatement` |
| `Langlands.Henniart.FiniteOrbitCountingStatement` | `Langlands.Henniart.FiniteOrbitCountingStatement` |
| `Langlands.Henniart.FiniteAuxiliaryStatement` | `Langlands.Henniart.FiniteAuxiliaryStatement` |

The canonical Lean file is byte-identical to the previous defining file, with
SHA-256 `24f6ee46420d7b901c2adc7ff882bffb8ee3b1acc9f52d693519834fca86ec8c`.
All complete bodies, nine independent universes, instance binders, internal
hypotheses and the closing conjunction order are retained. The retained original
Markdown prefix has SHA-256
`2a32e47fd3cca84c7c602bb67bfe490cd1c0b23105164387a9d158b34dc4feef`.

At both inspected Library commits there is no importer of the previous module
and no external documentation link to its previous path. The current staging and
shared draft trees likewise contain no such import or external documentation
link. Worker 66 refreshed coordination with Workers 7, 29 and 30 before editing;
Worker 30 confirmed that no additional submitted consumer needs migration, and
that later finite-witness and numerical statements will use the canonical import.
The legacy pair remains available throughout pending-consumer integration.

Worker 29's current proof task `2ebda30e-f5d6-447d-b368-04732d6569b5`
(previously `553d05f3-bbc4-42cb-9dd8-37954c346486`) retains the sequence:
publish this placement first, then adopt the published canonical statement pair,
change the proof import to `Langlands.Correspondence.FiniteAuxiliaryStatement`,
and repeat complete-target and allowed-assumption checks before proof submission.
Its closing theorem remains `Langlands.Henniart.finiteAuxiliary`. The proof task
has no submitted candidate at this inspection. Worker 0 confirmed the same
sequence. Worker 7 previously reported no affected assembly consumer; the
compatibility re-export also protects any consumer not yet reported in this run.
Their local/global construction and correspondence assembly scopes are unchanged.

### Validation

Worker 66 validated the move in the current prepared environment. Both the
original and canonical aggregate statements were inspected successfully as
`Prop` definitions with the nine independent levels `uX`, `uY`, `uT`, `uS`,
`uR`, `uI`, `uU`, `uF`, `uK`. Both import paths compile. All seven definitions
were printed before and after the move with explicit universes, explicit
arguments, full names and axiom closures. Their 14 diagnostic messages agree
exactly after removing appended Lake progress and completion lines. The
complete aggregate telescope and six-component conjunction agree.

A separate private diagnostic copied the published baseline source under a
fresh namespace, changing only its namespace and matching end name. Lean
accepted `rfl` equality between each old and new unapplied definition at its
complete universe list, including all nine independent universes of the
aggregate. This checks definitional equality of the complete types and bodies;
it does not assume or prove any component proposition. Raw expression
fingerprints from the inspector are not used as an equality test. Each
statement's axiom closure remains limited to `propext`, `Classical.choice`
and `Quot.sound`.

The initial complete overlay of 270 Lean modules compiled with the declaration
diagnostic and both import paths. After the three unrelated Library additions,
a private import-only module imports all 273 Lean modules of the complete
overlay over `115fa73cc7e02f57b8baadcc0d37433783a7152a`. The final incremental
Lake build completed successfully with no errors or warnings. Every public Lean file has nonempty
same-stem Markdown. Exactly the canonical and legacy pairs are changed or
added; the diagnostic modules stay private and are not submitted.

The two original literature files were also rechecked at their current
Central-Library paths, and their SHA-256 fingerprints match those retained
above. Worker 66 read Henniart 2000 section 4.3 on printed pp.452–453 and
Henniart 1988 section 2.8 on printed pp.506–507. These confirm the retained
finite-selection/compositum and finite-counting provenance and the explicitly
stated generalization boundaries. No source interpretation was changed.

Worker 0's earlier test-run checks compiled both import paths and compared all
seven declaration printouts. A diagnostic copy of the finite auxiliary proof
with only its statement import changed also compiled there, including a direct
unapplied assignment at all nine universes and only `propext`, `Classical.choice`
and `Quot.sound` in its axiom closure. These are historical development checks,
not current acceptance evidence; no proof source is included in this placement.
Independent statement review and Library publication remain required.
