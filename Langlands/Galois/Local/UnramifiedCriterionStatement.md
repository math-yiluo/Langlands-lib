# Canonical unramified criterion using absolute inertia

Author: Worker 107.

`Langlands.PadicField.CanonicalUnramifiedCriterion.{u}` is a proposition
asserting that, for every prime `p`, every `F : PadicField.{u} p`, and every
`E : Langlands.LocalClassField.FiniteIntermediateExtension F.Carrier` for
which `IsGalois F.Carrier E.field` holds,

```lean
F.canonicalTopologicalData.ramificationIndex =
    (E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex ↔
  F.absoluteInertia F.canonicalTopologicalData ≤ E.field.fixingSubgroup
```

The prime is an explicit universally quantified natural number, with its
primality certificate. The common universe `u` is arbitrary. Finiteness is
supplied by `E`, and the only additional extension hypothesis is that this
same field is Galois over `F.Carrier`. Neither side of the equivalence is
assumed. In particular, there is no unramifiedness or valuation-compatibility
hypothesis supplied by the caller.

## Objects and meaning

`FiniteIntermediateExtension` packages an actual intermediate field of
`AlgebraicClosure F.Carrier` and its finite-dimensionality certificate.
`E.asPadicField (p := p)` retains that field's operations and uses the
composite algebra map from `Padic p` through `F.Carrier`. Both local-field
realizations are the existing `canonicalTopologicalData` constructions.
These are exactly the fields, p-adic algebra tower, and canonical absolute
ramification indices appearing in
`Langlands.ClassFieldTheory.Local.UnramifiedH2Exhaustion`.

Each `ramificationIndex` is the natural-number value of the normalized
integer order of the same rational prime `p`. The subgroup
`F.absoluteInertia F.canonicalTopologicalData` is the existing inertia
constructed from the residue action on the actual algebraic closure, using
the canonical base valuation. The published `AbsoluteProof` identifies it
with the kernel of the absolute residue homomorphism and proves its closed
normal subgroup properties. The right-hand side says every element of
this inertia subgroup fixes every element of `E.field` pointwise. The
fixing subgroup is taken in the same absolute Galois group
`Field.absoluteGaloisGroup F.Carrier`.

No new closure, valuation, residue action, intermediate field, or local-field
realization is introduced. This file defines the criterion as a proposition;
it does not prove it. The imported definitions and the published residue
exactness theorem alone do not establish this arithmetic equivalence. It
is also not an H² exhaustion or splitting result; that downstream target
and its imports are unchanged.

## Original source and derived formulation

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
Springer GTM 67 (1979), registered source `serre-1979-local-fields`, retained
at `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Worker 107 read these original passages:

- Chapter III, section 5, Theorems 2–3 and Corollaries 1–3, printed pages
  54–55 / PDF pages 61–62: finite unramified extensions and residue-field
  lifting, their embeddings, and the maximal unramified extension.
- Chapter IV, section 1, Proposition 1 and the corollary to Proposition 2,
  printed pages 62–63 / PDF pages 69–70: residue inertia and its fixed field,
  the maximal unramified subextension of a finite Galois extension.
- Chapter I, section 7, Proposition 21 and its corollary, and Proposition 22,
  printed pages 22–23 / PDF pages 30–31: inertia, ramification, and restriction
  through finite Galois towers.
- Chapter I, section 4, printed pages 14–15 / PDF pages 22–23: unramifiedness
  means relative ramification index one and separable residue extension;
  normalized valuations restrict with the relative ramification index.
- Chapter II, section 5, opening paragraph, printed page 36 / PDF page 44:
  the absolute ramification index is the normalized order of `p`.

No project errata entry for this registered source was present when checked.

The displayed Lean formula is a derived specialization of these results,
not a verbatim theorem of Serre. Here the base and extension are p-adic
local fields, so their residue fields are finite and therefore perfect.
The residue separability condition is consequently automatic. For the
compatible canonical valuations, normalized orders satisfy
`v_E(p) = e(E/F) * v_F(p)`, with `v_F(p) > 0`. Thus equality of the absolute
indices is equivalent to relative ramification index one. Passing the
finite inertia fixed-field characterizations through the algebraic closure
identifies the fixed field of absolute inertia with the maximal unramified
extension. Containment of the finite field `E.field` in that fixed field
is precisely the displayed subgroup inclusion. These observations explain
the mathematical provenance; formal proofs of the canonical valuation
comparison and of this absolute finite-level criterion remain obligations
of a separate proof contribution.
