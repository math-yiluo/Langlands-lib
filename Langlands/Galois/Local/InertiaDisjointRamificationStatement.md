# Total ramification from disjointness with the inertia fixed field

Author: Worker 107.

## Exact proposition and scope

`Langlands.PadicField.InertiaDisjointTotallyRamified.{u}` is a proposition
definition, not a proved theorem. For every prime `p`, expressed by
`p : ℕ` and `[Fact p.Prime]`, every `F : PadicField.{u} p`, and every
`D : Langlands.LocalClassField.FiniteIntermediateExtension F.Carrier`, it states

```lean
let U := IntermediateField.fixedField (F.absoluteInertia F.canonicalTopologicalData)
D.field.LinearDisjoint U →
  (D.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
    Module.finrank F.Carrier D.field * F.canonicalTopologicalData.ramificationIndex
```

The universe `u` is arbitrary. The degree-one case and non-Galois finite
extensions are included. The only additional hypothesis is the displayed
linear disjointness. There is no assumption of a residue degree, total
ramification, Galoisness, norm surjectivity, or cohomological vanishing.
Only the implication displayed above is stated; no converse is asserted.

## Fields, scalar maps, and index convention

`D.field` is the actual intermediate field of
`F.Carrier ⊆ AlgebraicClosure F.Carrier`, with its inherited field operations,
base algebra, and finite-dimensionality instance from
`FiniteIntermediateExtension`. `U` is the fixed field in this same algebraic
closure of the existing absolute inertia subgroup constructed using
`F.canonicalTopologicalData`. No alternate maximal unramified field is supplied.

`D.field.LinearDisjoint U` is Mathlib's `IntermediateField.LinearDisjoint`.
Here the second argument is the carrier of the actual intermediate field `U`,
with its inherited algebras over `F.Carrier` and into the algebraic closure.
The scalar tower is the inclusion tower. The predicate is linear disjointness
of the two corresponding subalgebras of this closure; equivalently, the
multiplication map from their tensor product over `F.Carrier` is injective.
The statement uses this actual predicate, without replacing it by an
intersection condition.

`D.asPadicField (p := p)` retains the field operations of `D.field` and uses
the composite scalar map
`Padic p → F.Carrier → D.field`. The finrank in the conclusion uses the
inherited `F.Carrier`-algebra on that same `D.field`. The conclusion therefore
concerns the very extension in the hypothesis.

In `Langlands.LocalField.Normalization.Definitions`, the ramification index
of topological data `T` is
`(T.ord (p : F.Carrier)).toNat`. Its normalized additive order is
`-WithZero.log (T.discreteValuation x)`, with order zero at zero.
For the nonzero prime `p`, the index is the positive absolute ramification
index, namely the order of `p`, rather than the relative ramification index
of `D/F`. Thus total relative ramification is expressed here as
`e_abs(D) = [D : F] * e_abs(F)`. This uses the usual restriction formula
`v_D(p) = e(D/F) * v_F(p)` and the equality `e(D/F) = [D : F]` for a totally
ramified finite local extension. No normalization equating `e_abs(F)` with
one is imposed.

## Original source and derived formulation

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
Springer GTM 67 (1979), registered source `serre-1979-local-fields`,
file `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Worker 107 read these original passages:

- Chapter V, section 4, Lemmas 6–7 and the proof of Proposition 7,
  printed pages 89–90 / PDF pages 96–97. Lemma 7 derives total
  ramification of a finite model from linear disjointness with the maximal
  unramified extension.
- Chapter III, section 5, Theorems 2–3 and Corollaries 1–3,
  printed pages 54–55 / PDF pages 61–62. These provide unramified lifting,
  the maximal unramified extension, and the maximal unramified subextension
  of an arbitrary finite extension.
- Chapter IV, section 1, Proposition 1 and the corollary to Proposition 2,
  printed pages 62–63 / PDF pages 69–70. These identify the inertia fixed
  field with the maximal unramified subextension at finite Galois levels.
- Chapter I, section 4, definitions, Proposition 10, and the valuation
  restriction formula preceding Proposition 11, printed pages 14–15 /
  PDF pages 22–23. These give the ramification and residue degree
  conventions and the relation between normalized valuations.

No project errata entry for this source was present when checked.

This is the finite-model arithmetic implication used in Serre V.4 Lemma 7,
specialized to p-adic fields and formulated using the actual canonical
inertia fixed field. The source argument is that a nontrivial residue
extension would produce a nontrivial unramified subextension of `D/F`.
Finite residue fields are perfect, so III.5 applies even when `D/F` is not
Galois. Such an unramified subextension lies in the inertia fixed field and
contradicts linear disjointness. The residue degree is therefore one,
which gives the displayed absolute-index formula. This explains the
derived formulation; it is not a Lean proof supplied by this module.

In the proof of V.4 Proposition 7, compatible finite models are first
placed over a common finite unramified stage, and are linearly disjoint
from the maximal unramified extension over that stage. After that stage
has been identified with `F` and its actual inertia fixed field, this
proposition supplies total ramification for each such finite model.
It does not choose or enlarge the common stage, construct the finite
models, or prove their disjointness. Those steps and the subsequent norm
and solvability arguments are separate obligations.

A future proof must justify the residue and unramified-subextension
argument for arbitrary finite `D`. Applying a finite Galois unramified
criterion directly to a potentially non-Galois `D` would not suffice.
This module adds only the proposition target and proves none of these
arithmetic implications.
