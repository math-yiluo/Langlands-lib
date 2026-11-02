# Canonical norm depth and multiplicative conductor

Author: Worker 84. Proposition definitions for task
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1.
No truth of these propositions or existence of an auxiliary character is asserted.

`CanonicalPrincipalUnitDepthStatement` says that for every finite p-adic
field `F`, every `F.TopologicalData` realization `T`, and every natural
unit-filtration level `n`, there is a natural number `s` such that

\[
 |x-1|_{\mathrm{can}}<p^{-s}\quad\Longrightarrow\quad x\in U_T^n
 \qquad (x\in F^\times).
\]

The radius depends on the field, its realization and the filtration level,
and is independent of a character. The norm is the actual
`F.canonicalNorm`, which extends the usual p-adic norm on the base field.
The filtration is exactly `T.principalUnits`, including `U_T^0=O_T^\times`.
The statement supplies no explicit formula for `s` or ramification index.

`CanonicalCharacterDepthStatement` compares two properties of a family of
continuous complex quasicharacters, selected by any predicate `P`:

- At every canonical depth `s`, some character satisfying `P` is nontrivial
  at some unit `x` with `|x-1|can < p^(-s)`.
- At every natural threshold `r`, some character satisfying `P` has
  `r ≤ T.multiplicativeConductor χ`.

These are asserted to be equivalent. The witnesses can vary with the
threshold. The same predicate is retained; it can encode finite order,
an exact stabilizer, or other conditions, but neither such a predicate nor
a character satisfying it is assumed to exist. All characters use precisely
the topology supplied by `T`. The aggregate
`CanonicalConductorDepthStatement.{u}` is the conjunction of the two
proposition definitions, with one arbitrary carrier universe. Every prime,
including two, is covered.

This is a derived interface, rather than a verbatim theorem of the
literature. Harris, *The local Langlands conjecture for GL(n) over a p-adic
field, n < p* (1998), Lemma 4.7 and its proof, printed pp.201 and 204–206,
uses unbounded conductor while retaining the stabilizer condition (4.12).
The passage on printed p.205 / PDF p.29 was read directly again for this
unit. Source `harris-1998-local-langlands`, SHA-256
`7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
The Library's `AuxiliaryCharacterStatement` instead specifies nontriviality
in canonical norm balls. This unit isolates the elementary topological
comparison needed between those conventions. It neither constructs the
characters in Harris's argument nor repairs his characteristic-two
construction, nor transports the norm stabilizer to the Weil group.

The project dependency `Langlands.HarmonicAnalysis.Conductor` supplies
the actual principal-unit filtration, the least triviality level
`multiplicativeConductor`, and the quasicharacter topology convention.
`F.canonicalNorm` is imported through its local-field dependencies.
The expected proof uses openness of valuation lattices, the published
comparison of `T.topology` to the canonical norm topology, cofinality of
principal units among neighborhoods of one, and the conductor's proved
minimality. Those results give cofinal neighborhood systems, rather than
an equality of the canonical norm and the residue-normalized absolute value.

Compilation and independent review of these proposition definitions do
not prove either comparison; a theorem requires a separate proof contribution.
