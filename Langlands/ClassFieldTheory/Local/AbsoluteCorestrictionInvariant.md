# Absolute corestriction preserves local invariants

Author: Worker 42.

`Langlands.ClassFieldTheory.Local.InvariantFamily.AbsoluteCorestriction`
is a proposition on one raw `InvariantFamily.{u,v} p`. For every pair
`F E : PadicField.{u} p`, every specified finite extension structure
`Algebra F.Carrier E.Carrier` compatible with the two structures over
`Padic p`, and every supplied compatible algebra on their actual algebraic
closures, it asserts

```
I.absolute F (absoluteCorestriction F.Carrier E.Carrier 2 x) =
  I.absolute E x
```

for every `x : absoluteCohomology E.Carrier 2`. The lower-field invariant
of the upper-to-lower transfer equals the upper-field invariant, with no
degree multiplier. The existing `InvariantFamily.AbsoluteRestriction`
instead puts the extension degree on the lower-field invariant.

The finite extension need not be normal or Galois. The specified closure
data are
`Algebra (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier)` and
`IsScalarTower F.Carrier (AlgebraicClosure F.Carrier)
(AlgebraicClosure E.Carrier)`. There is no additional tower condition over
`E.Carrier`. The predicate quantifies over all such supplied compatible
closure embeddings.

The parameter `p` is arbitrary with `[Fact p.Prime]`. The fields share an
arbitrary universe `u`, matching the published absolute corestriction API;
there is no restriction to `Type 0`. The second universe `v` of the raw
family, used by its relative component, remains independent. This
predicate uses only the absolute component. Its local `CharZero F.Carrier`
instance is proved by `Algebra.charZero_of_charZero (Padic p) F.Carrier`
from the specified p-adic algebra, rather than added as a hypothesis.

## Actual maps and declaration correspondence

`Invariants` supplies the raw family: its absolute component is an additive
map from the actual continuous absolute Galois `H²` to
`RationalModIntegers`, the actual quotient `Q/Z`. The raw family assumes
no invariant laws. `Cohomology` supplies `absoluteCohomology K 2` with
discrete algebraic-closure unit coefficients.

`AbsoluteCorestriction` supplies `absoluteCorestriction K L 2`. It first
transports upper-field cohomology to the cohomology of the actual open
image of absolute Galois restriction, then applies genuine continuous
corestriction. Its intrinsic finite-stage certificate identifies this map
with ordinary cohomological transfer on each compatible finite normal
stage. The result is a morphism of underlying modules; this predicate
applies its underlying function and makes no assertion about continuity
between cohomology topologies.

The Lean pair defines precisely this compatibility predicate. It neither
constructs an invariant nor proves the predicate, injectivity of
corestriction, or existence of a class formation. A later simultaneous
local realization target must bind the same raw family for this clause
and the other invariant and fundamental-class clauses. The compatibility
law is not an input to the imported corestriction construction.

## Original source and convention

The source is Jean-Pierre Serre, *Local Fields*, Greenberg translation
(1979), registered as `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
retained at `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.

Chapter XI, section 2, Proposition 1(ii), printed page 167 / PDF page 173,
states the invariant equality for corestriction for every extension in a
class formation. The proof continues on printed page 168 / PDF page 174.
This predicate records the equality part of that proposition, specialized
to actual p-adic absolute cohomology. It does not also assert the
injectivity conclusion of Proposition 1(ii) or formalize its proof.
Chapter XIII, section 4, Theorem 1, printed pages 195–196 / PDF pages
200–201, identifies the local multiplicative formation as a class
formation, making the earlier proposition applicable locally. Serre uses
the inflation direct limit for absolute `H²`; the Library's continuous
cohomology and finite-stage comparison provide the actual objects and
maps used here.

This clause preserves the arithmetic invariant convention of
`Invariants`: its normalization assigns the positive reciprocal degree
to the arithmetic fundamental class. The clause contains no reciprocity
map or Frobenius choice. The inverse relation between arithmetic and
geometric reciprocity remains as documented in `Invariants`.

Worker 42 read the cited original passages and visually checked
Proposition 1(ii). The *Local Fields* entries on PDF pages 2–3 of Serre's
2019 book corrections do not change these passages; the separate
correction to the connecting arrow on printed page 193 does not alter
the corestriction equality. No project-specific errata file for the
1979 source was present.
