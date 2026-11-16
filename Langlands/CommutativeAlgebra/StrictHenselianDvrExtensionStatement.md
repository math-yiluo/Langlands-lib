# A faithfully flat strictly Henselian extension of a DVR

`Langlands.CommutativeAlgebra.StrictHenselianDvrExtensionStatement.{u}` states
that every commutative domain discrete valuation ring `R : Type u` admits an
algebra `A : Type u` which is a commutative domain DVR, is Henselian, has
separably closed residue field, and is faithfully flat as an `R`-module.
There is no completeness, excellence, finite residue field, or characteristic
assumption.

This is a derived existential consequence of the Stacks Project:

- [Tag 04GP, Lemma 10.155.2](https://stacks.math.columbia.edu/tag/04GP)
  constructs a strict Henselization with separably closed residue field.
- [Tag 07QM, Lemma 15.46.1(1)](https://stacks.math.columbia.edu/tag/07QM)
  gives faithful flatness.
- [Tag 0AP3, Lemma 15.46.11](https://stacks.math.columbia.edu/tag/0AP3)
  says that the strict Henselization of a noetherian local DVR is again a DVR.
  A domain DVR in Mathlib is noetherian and local, so the source hypotheses
  apply.

The registered source
`stacks-strict-henselian-dvr-extension-2026-11-16` retains the original HTML
pages as `04GP.html`, `07QM.html`, and `0AP3.html`. The source pages were read
at their lemma statements and proofs; each has no individual comments. No
matching project erratum was found.

The Lean formulation forgets the strict Henselization's universal property,
its chosen residue-field embedding, and the intermediate Henselization. It
retains only the properties needed to descend finiteness along its spectrum.
The same-universe requirement is the smallness convention for a construction
from finite algebra presentations and a same-universe separable closure; the
source does not discuss Lean universes.

This file declares a proposition and contains no proof or construction of the
extension.
