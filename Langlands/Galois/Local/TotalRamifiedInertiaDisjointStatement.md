# Disjointness of a totally ramified field and the inertia fixed field

Authors: Worker 104 (Lean definition, original-source reading and Markdown)
and Worker 366 (exact interface and finite-stage proof-route specification).

## Exact proposition

`Langlands.PadicField.TotallyRamifiedInertiaDisjoint.{u}` is a `Prop`-valued
definition. It states, for every `p : ℕ` with `[Fact p.Prime]`, every
`F : PadicField.{u} p`, and every
`D : Langlands.LocalClassField.FiniteIntermediateExtension F.Carrier` with
`[IsGalois F.Carrier D.field]`, the implication

```lean
(D.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
    Module.finrank F.Carrier D.field * F.canonicalTopologicalData.ramificationIndex →
  D.field.LinearDisjoint
    (IntermediateField.fixedField (F.absoluteInertia F.canonicalTopologicalData))
```

The universe `u` is arbitrary. The degree of `D/F` is any finite degree,
including one. Galoisness is explicitly required. The sole arithmetic
hypothesis is the displayed equality of canonical absolute ramification
indices. In particular, the proposition assumes neither prime degree,
linear disjointness, finite-dimensionality of the inertia fixed field,
norm surjectivity, nor another arithmetic theorem. It makes no assertion
for a non-Galois `D`.

This module supplies a statement target, not a proof of that target.
Acceptance or compilation of the proposition definition does not prove
the implication.

## Actual fields, maps and normalization

`FiniteIntermediateExtension F.Carrier`, from
`Langlands.ClassFieldTheory.Local.ReciprocitySystem`, packages an actual
intermediate field of `F.Carrier ⊆ AlgebraicClosure F.Carrier` together
with its finite-dimensionality certificate. `D.field` is that intermediate
field with its inherited operations and `F.Carrier`-algebra. The finrank and
Galois instance in the proposition refer to this same algebra.

`D.asPadicField (p := p)` repackages that same field using the composite
scalar map `Padic p → F.Carrier → D.field`. Its
`canonicalTopologicalData`, and the corresponding canonical data of `F`,
are the existing spectral-norm local-field structures. For topological
data `T`, `ramificationIndex` is `(T.ord (p : F.Carrier)).toNat`;
`ord` is the normalized additive order, with value zero at zero.
Consequently these are absolute indices over `Padic p`. The hypothesis
expresses total relative ramification by
`e_abs(D) = [D:F] * e_abs(F)`, using the usual restriction relation
`v_D(p) = e(D/F) * v_F(p)` and `e(D/F) = [D:F]`.
It does not normalize `e_abs(F)` to one.

Write `U` for
`IntermediateField.fixedField (F.absoluteInertia F.canonicalTopologicalData)`.
The subgroup here is the existing absolute inertia subgroup from
`Langlands.Galois.Local.AbsoluteDefinitions`: the kernel of the actual
residue action on the algebraic closure, using the canonical data of `F`.
The fixed field `U` is an intermediate field of that very same
`AlgebraicClosure F.Carrier`. It is not a separately supplied model of a
maximal unramified field.

`D.field.LinearDisjoint U` is Mathlib's
`IntermediateField.LinearDisjoint`. Its second argument is the carrier
of `U`, with the inherited algebra over `F.Carrier`, its inclusion algebra
into the closure, and the corresponding scalar tower. Thus it expresses
linear disjointness of the actual subfields in their common closure,
equivalently injectivity of the multiplication map from their tensor
product over `F.Carrier`. No alternate scalar maps or replacement fields
are introduced.

## Original source and derived formulation

The source is Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay
Greenberg, Springer GTM 67 (1979), registered as
`serre-1979-local-fields`, file
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Worker 104 read the following passages in the retained original:

- Chapter V, section 4, printed pages 87–88 / PDF pages 94–95.
  On page 87 Serre proves that a finite totally ramified extension `L/K`
  and a finite unramified extension `K'/K` are linearly disjoint, using
  ramification and residue-degree bounds for their compositum.
  He identifies the compositum with `K' ⊗_K L`.
  On page 88 he passes to the direct limit of unramified extensions and
  identifies `L_nr` with `L ⊗_K K_nr`.
- Chapter III, section 5, Theorems 2–3 and Corollaries 1–3,
  printed pages 54–55 / PDF pages 61–62. These construct finite
  unramified extensions from separable residue extensions and describe
  the maximal unramified extension as their direct limit.
- Chapter IV, section 1, Proposition 1 and the corollary to Proposition 2,
  printed pages 62–63 / PDF pages 69–70. These identify the inertia
  subgroup and its fixed field at finite Galois levels.
- Chapter I, section 4, definitions, Proposition 10 and the valuation
  restriction formula preceding Proposition 11, printed pages 14–15 /
  PDF pages 22–23. These give the relative ramification and residue
  conventions and the normalized valuation restriction formula.

No project errata entry for this source was present when checked.

Serre's `K` corresponds to `F.Carrier`, `L` to `D.field`, and `K_nr`
to the actual fixed field `U`. The finite residue field of a p-adic field
is perfect, as required by the source setup. The finite disjointness
argument on page 87 precedes Serre's Galois assumption on page 88 and his
later specialization to cyclic prime degree. Our target retains Galoisness
for `D/F` but allows every finite degree. The direct-limit paragraph is
written in that later specialized context; its tensor-product passage
derives from the general finite disjointness argument and needs no
prime-degree norm argument.

The exact Lean proposition is a derived formulation, not a standalone
theorem quoted verbatim from Serre. Besides passing from finite
unramified stages to their union, it specializes to p-adic fields,
expresses total ramification through absolute canonical indices, and
uses the actual inertia fixed field in the specified closure.
The finite-level inertia identification and unramified exhaustion explain
the correspondence with Serre's `K_nr`; they are mathematical comparisons,
not a new definition declaring this field unramified.

## Proof obligations and existing interfaces

The Library theorem
`Langlands.PadicField.inertiaFixedFieldUnramifiedExhaustion`, in
`Langlands.Galois.Local.InertiaFixedFieldUnramifiedProof`, already states
and proves that every finite subset of `U` lies in a finite Galois
intermediate field with the same canonical absolute index as `F`;
it also proves containment in `U` for every such finite field.

An intended future proof of this target can choose an `F`-basis of
`D.field` and consider a finite linear relation over `U`. The exhaustion
theorem places its finitely many coefficients in one finite unramified
stage `E`. Finite total/unramified disjointness makes that basis linearly
independent over `E`; using the actual inclusions transfers the vanishing
of all coefficients back to `U`. Mathlib's
`IntermediateField.LinearDisjoint.of_basis_left` then yields the stated
disjointness. The finite disjointness clause is the first conclusion of
the separate Library target
`Langlands.LocalClassField.TotalUnramifiedCompositum`, in
`Langlands.ClassFieldTheory.Local.TotalUnramifiedCompositumStatement`.
This module neither proves that finite arithmetic nor assumes its target
as a hypothesis.

The later proof must supply the finite arithmetic input and the
coefficient descent with the actual scalar structures. An intersection
calculation alone cannot be passed directly to Mathlib's
`IntermediateField.LinearDisjoint.of_inf_eq_bot`: that lemma requires
both fields to be finite-dimensional over the base, and no such
assumption on `U` is present here.

The existing target
`Langlands.PadicField.InertiaDisjointTotallyRamified` gives the reverse
implication and has different scope, allowing non-Galois finite fields.
The present module states only the forward implication for finite Galois
fields. It does not assert norm surjectivity, bounded prime norm
solvability, or any subsequent arithmetic passage.
