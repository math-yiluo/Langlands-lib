# Range-kernel exactness on the actual nondegenerate parts

Authors: Worker 6 and Worker 702.

`Langlands.Algebra.NondegeneratePartRangeExactnessStatement.{uA,uL,uM,uN}`
is a closed proposition about the published original additive actions and
intertwiners. For every nonunital ring `A` and `hA : IsIdempotented A`,
every three original modules `L`, `M`, `N`, and original additive
intertwiners `f : NonUnitalModuleHom A L M` and
`g : NonUnitalModuleHom A M N`, it asserts

```lean
f.rangeSubmodule = g.kernelSubmodule →
  (f.restrictNondegeneratePart hA).rangeSubmodule =
    (g.restrictNondegeneratePart hA).kernelSubmodule
```

The premise is exactness of the original pair at `M`, expressed by equality
of the actual stable additive subgroups published in
`Langlands.Algebra.NonUnitalModuleKernels`. Membership in the range means
having an original preimage, and membership in the kernel means being sent
to zero. The conclusion is the same equality inside the existing subtype
`nondegeneratePart hA M`. Both restricted maps are the published
`NonUnitalModuleHom.restrictNondegeneratePart`, with their inherited original
actions. There is no replacement range, kernel, restriction or exactness
predicate. The premise already implies that the composite vanishes, so a
separate vanishing-composite hypothesis is unnecessary.

The ring and three carrier universes `uA,uL,uM,uN` are independent. The module
checks the complete unfolded proposition at arbitrary universes and both
alternating unequal size assignments `(0,1,0,1)` and `(1,0,1,0)`. It assumes no
nondegeneracy of the original carriers. Zero rings, zero carriers, and
degenerate actions, including zero actions over unital rings, are allowed.
There is no unit-action, field, commutativity, nontriviality, dimension or
finiteness assumption. No closure, abelian, additive-functor or categorical
exactness certificate is a premise.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Original actions and intertwiners are specified at printed pp.5–6/PDF11–12;
I.1.2 at printed p.7/PDF13 defines the nondegenerate part. The proposition
and proof at printed p.8/PDF14 assert exactness of the part functor and
establish precisely preservation of the displayed range-kernel equality.
If `m` in the kernel is fixed by an idempotent `e`, choose an original
preimage `l` of `m`. Then `e • l` lies in the nondegenerate part and maps to
`m`. The inclusion of the restricted range in the restricted kernel is
immediate. The registered supplementary earlier-edition errata
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was checked at PDF1–3 and PDF18–19 by Worker 702 as well as in the parent
source audit. Those consulted pages give no correction to this exactness
argument; the older errata do not replace the governing 2026 original. The published source-discrepancy note
`notes/renard/appendix-a-corrections.md` explains the deficient unrestricted
abelian-subcategory criterion in the book; that criterion is not used here.

This exact formulation is an internal derived specification of the
original-map conclusion in the source proof. It states no theorem and
supplies no proof. The actual part functor's categorical preservation of
`CategoryTheory.ShortComplex.Exact`, the inclusion's exactness, the
nondegenerate abelian structure, adjunctions, completion and scalar
comparisons remain separate obligations. A later proof can follow the
source's idempotent-adjusted lift directly.
