# Solvability of totally ramified finite local Galois groups

Author: Worker 109.

`Langlands.PadicField.TotallyRamifiedGaloisSolvability.{u}` is a
`Prop`-valued definition. For every natural number `p` with `[Fact p.Prime]`,
every `F : PadicField.{u} p`, and every
`E : Langlands.LocalClassField.FiniteIntermediateExtension F.Carrier`
with `[IsGalois F.Carrier E.field]`, it asserts, on setting
`n := Module.finrank F.Carrier E.field`,

```lean
(E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
    n * F.canonicalTopologicalData.ramificationIndex →
  Group.IsSolvable Gal(E.field/F.Carrier)
```

The common universe `u` is arbitrary. The finite-dimensionality certificate
is part of `E`; no degree bound or nontriviality hypothesis is added, so
extensions of degree one are included. The arithmetic equality is the sole
hypothesis beyond the indicated field, finiteness and Galois conditions.
There is no solvability, cyclic decomposition, inertia comparison,
ramification quotient, norm-surjectivity or class-field-theory assumption.
The target is restricted to totally ramified extensions.

## Existing objects and canonical arithmetic translation

`FiniteIntermediateExtension` is the subtype of actual intermediate fields
of `AlgebraicClosure F.Carrier` that are finite-dimensional over `F.Carrier`.
`E.field` is that intermediate field, with its existing field and algebra
structures. `E.asPadicField (p := p)` repackages it as a finite extension of
`Padic p`, using the composite algebra map through `F.Carrier`.
Both `canonicalTopologicalData` terms are the existing constructed canonical
local-field data. This statement introduces no field, valuation or Galois-group
model.

For `T : F.TopologicalData`, the existing definition is
`T.ramificationIndex = (T.ord (p : F.Carrier)).toNat`, where `T.ord` is the
normalized additive integer order. The same construction is used on
`E.asPadicField`. Thus the displayed equality is exactly
`e_abs(E) = [E:F] * e_abs(F)` in natural numbers, with the extension's
absolute index on the left and the degree first in the product on the right.
It is not a direct reference to a separately defined relative index.

Its mathematical translation uses compatibility of the canonical valuations:
normalized orders restrict as `v_E(x) = e(E/F) * v_F(x)` for nonzero `x` in
`F`. Applying this to `p`, whose order in `F` is positive, gives
`e_abs(E) = e(E/F) * e_abs(F)`. Cancellation then identifies the hypothesis
with `e(E/F) = [E:F]`. For finite extensions of these complete discretely
valued fields, the degree formula `[E:F] = e(E/F) * f(E/F)` identifies
this with residue degree one, hence total ramification. The compatible
canonical valuation comparison and its link to the relative degree formula
are proof obligations, not extra assumptions or proofs in this file.

`Gal(E.field/F.Carrier)` is Mathlib's actual group of `F.Carrier`-algebra
automorphisms of `E.field`. `Group.IsSolvable` is Mathlib's predicate saying
that this group's derived series eventually reaches the trivial subgroup.
It is the current name of the predicate also available under the deprecated
root alias `IsSolvable`; no substitute predicate is defined here.

## Original source and derivation

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
Springer GTM 67 (1979), registered source `serre-1979-local-fields`, retained
at `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Worker 109 read the following original passages; PDF page numbers count
from one:

- I.4, printed pages 14–15 / PDF pages 22–23: relative ramification and
  residue degrees, total ramification, Proposition 10's degree formula,
  and restriction of normalized valuations.
- II.5, opening paragraph, printed page 36 / PDF page 44: the positive
  absolute ramification index is the normalized order of `p`.
- IV.1, Proposition 1 and the corollary to Proposition 2, printed pages
  62–63 / PDF pages 69–70: the finite ramification filtration, its eventual
  triviality, its inertia term `G₀`, the residue quotient, and the maximal
  unramified fixed field.
- IV.2, Proposition 7 and Corollaries 1, 3 and 5, printed pages 67–68 /
  PDF pages 74–75: ramification quotients embed in unit quotients;
  `G₀/G₁` is cyclic, `G₁` is a finite `p`-group in residue characteristic
  `p`, and `G₀` is solvable.
- V.4, Proposition 7, printed page 90 / PDF page 97: the norm argument
  uses solvability of a totally ramified finite Galois group to reduce
  to cyclic prime-degree extensions. This supplies downstream motivation;
  this module states no norm theorem.

No project errata entry for this source was present when checked.

The Lean formulation is a derived specialization of Serre's inertia
solvability result, with total ramification expressed using the Library's
canonical absolute indices. For a totally ramified finite Galois extension,
the residue extension is trivial and the inertia subgroup is the whole
Galois group. Serre's cyclic tame quotient and finite `p`-group wild inertia
therefore imply solvability of that whole group. This describes provenance,
not an implemented Lean proof.

## Statement and proof boundary

This module only defines the proposition. A subsequent proof must establish
the canonical arithmetic comparison, identify the actual finite inertia
subgroup with the full automorphism group under the stated equality, and
obtain solvability from genuine ramification-filtration and group-theoretic
results. It must use proved comparisons with the existing constructions;
none of these bridges may be supplied as a new hypothesis of this target.
Existing residue exactness or the canonical unramified criterion by itself
does not prove inertia solvability. Independent acceptance of this statement
will establish its fidelity as a theorem target, not its truth in Lean.
