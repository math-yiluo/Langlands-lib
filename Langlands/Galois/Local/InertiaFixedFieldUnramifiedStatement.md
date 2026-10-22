# Finite unramified exhaustion of the actual inertia fixed field

Author: Worker 298.

`Langlands.PadicField.InertiaFixedFieldUnramifiedExhaustion.{u}` is a
proposition. It quantifies over every natural number `p` with a primality
certificate `[Fact p.Prime]` and every `F : PadicField.{u} p`, in an arbitrary
common universe `u`. For such `F` it names

```lean
U := IntermediateField.fixedField (F.absoluteInertia F.canonicalTopologicalData)
```

an intermediate field of `F.Carrier ⊆ AlgebraicClosure F.Carrier`, and
asserts the conjunction of two clauses.

1. For every `E : Langlands.LocalClassField.FiniteIntermediateExtension F.Carrier`
   with `[IsGalois F.Carrier E.field]`,

   ```lean
   F.canonicalTopologicalData.ramificationIndex =
       (E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex →
     E.field ≤ U
   ```

2. For every `s : Finset (AlgebraicClosure F.Carrier)` with `∀ x ∈ s, x ∈ U`,
   there exist `E : Langlands.LocalClassField.FiniteIntermediateExtension F.Carrier`
   and a proof of `IsGalois F.Carrier E.field` such that

   ```lean
   F.canonicalTopologicalData.ramificationIndex =
       (E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex ∧
     ∀ x ∈ s, x ∈ E.field
   ```

The finite set `s` is arbitrary, so the empty set is included; for it the
second clause only asks for one finite Galois extension with equal canonical
absolute ramification indices. No hypothesis on `F`, `E` or `s` beyond those
displayed is supplied. In particular neither this exhaustion, nor the finite
unramified criterion, nor any unramifiedness or valuation-compatibility
condition is a hypothesis.

Together the two clauses say that `U` is the directed union of its finite
Galois intermediate fields whose canonical absolute ramification index equals
that of `F`: clause 1 puts every such field inside `U`, and clause 2 says that
every finite subset of `U` lies in one of them. Two such fields lie in a third
by clause 2 applied to the union of finite generating sets, so the family is
directed. The finite-set form is chosen so that finitely many structure
constants in `U` can be placed in a single finite unramified level.

## Objects used

All objects are existing constructions; this module introduces no new field,
closure, valuation, inertia group or local-field realization.

- `F.absoluteInertia F.canonicalTopologicalData` is the existing absolute
  inertia subgroup of `Field.absoluteGaloisGroup F.Carrier`, defined in
  `Langlands.Galois.Local.AbsoluteDefinitions` from the residue action on the
  actual algebraic closure with the canonical base valuation. That module also
  supplies the instance `Langlands.PadicField.absoluteInertia_normal`, and the
  published `AbsoluteProof` identifies the subgroup with the kernel of the
  absolute residue homomorphism and proves that it is closed.
- `IntermediateField.fixedField` is Mathlib's fixed field of a subgroup of
  `AlgebraicClosure F.Carrier ≃ₐ[F.Carrier] AlgebraicClosure F.Carrier`, the
  group to which Mathlib's definition of `Field.absoluteGaloisGroup F.Carrier`
  unfolds; `x ∈ U` means that every element of the inertia subgroup fixes
  `x`. The same expression
  `U` appears in
  `Langlands.ClassFieldTheory.Local.InertiaFixedFieldNormSurjectivity`.
- `FiniteIntermediateExtension F.Carrier` packages an actual intermediate
  field of `AlgebraicClosure F.Carrier` with its finite-dimensionality
  certificate. `E.field ≤ U` is the actual order of intermediate fields of the
  same closure, and `x ∈ E.field`, `x ∈ U` are membership in them.
- `E.asPadicField (p := p)` keeps the operations of `E.field` and uses the
  composite scalar map from `Padic p` through `F.Carrier`. Each
  `canonicalTopologicalData.ramificationIndex` is the natural number given by
  the normalized order of the rational prime `p` in the existing canonical
  local-field realization, that is, the absolute ramification index.

The fields, extensions and ramification-index equality are written exactly as
in `Langlands.PadicField.CanonicalUnramifiedCriterion` and
`Langlands.ClassFieldTheory.Local.UnramifiedH2Exhaustion`.

## Original source and derived formulation

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
Springer GTM 67 (1979), registered source `serre-1979-local-fields`, file
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Worker 298 read the following passages in this file:

- Chapter III, section 5, Theorems 2 and 3 and Corollaries 1–3, printed
  pages 54–55 / PDF pages 61–62. Finite unramified extensions correspond to
  finite separable residue extensions (Theorems 2–3). Corollary 1 defines the
  maximal unramified extension `K_nr` as the inductive limit of the
  unramified extensions corresponding to the finite subextensions of the
  separable residue closure, Galois over `K`. Corollaries 2–3 describe the
  unramified subextensions of a finite extension and its maximal unramified
  subextension.
- Chapter IV, section 1, Proposition 1 and the corollary to Proposition 2,
  printed pages 62–63 / PDF pages 69–70. For a finite Galois extension `L/K`,
  the inertia group `G_0` is a normal subgroup, and the largest unramified
  subextension of `L/K` is the fixed field of `G_0`.
- Chapter V, section 4, Lemma 7 (with Lemma 6, which it applies), printed
  pages 89–90 / PDF pages 96–97. Lemma 7 uses `K_nr` as the union of the
  increasing directed family of its finite subextensions and places the
  finitely many structure constants of a finite extension of `K_nr` in one
  finite level.

No project errata entry for this registered source was present when checked.

The displayed proposition is a derived formulation of these results, not a
verbatim theorem of Serre. Serre's `K_nr` is built abstractly as an inductive
limit; here it is replaced by the actual fixed field `U` of the existing
absolute inertia subgroup in the existing algebraic closure, and no separate
maximal unramified field is introduced. The base and extensions are p-adic
local fields, so residue fields are finite, hence perfect, and every residue
extension is separable; unramifiedness of a finite extension therefore means
relative ramification index one. For the compatible canonical valuations the
normalized orders satisfy `v_E(p) = e(E/F) · v_F(p)` with `v_F(p) > 0`, so
relative ramification index one is the same as equality of the canonical
absolute ramification indices. With these identifications, clause 1 says
that every finite unramified Galois subextension lies in the inertia fixed
field, and clause 2 says that the inertia fixed field is the union of those
subextensions, which is Corollary 1 of III.5 combined with the corollary in
IV.1, in the form used in V.4 Lemma 7.

## Status and unproved bridges

This module defines the proposition only; it proves neither clause. A proof
is a separate task. A likely route, not carried out here, is as follows.

- Clause 1 should follow from the published theorem
  `Langlands.PadicField.canonicalUnramifiedCriterion` (forward direction)
  together with Mathlib's Galois correspondence
  `IntermediateField.le_iff_le` relating `E.field ≤ fixedField H` and
  `H ≤ E.field.fixingSubgroup`.
- Clause 2 needs that `U` is normal over `F.Carrier`, which should follow
  from normality of the absolute inertia subgroup, so that the normal closure
  of the finite field generated by `s` is a finite Galois intermediate field
  contained in `U`; the reverse direction of the same criterion then yields
  the equality of ramification indices.

These are expectations about a future proof, not results established by this
module. It does not state extension descent, existence of unramified
extensions of every degree, norm surjectivity, or any cohomology vanishing.
