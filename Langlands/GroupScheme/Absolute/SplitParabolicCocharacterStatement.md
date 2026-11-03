# Split parabolics containing a fixed maximal torus: statement

Worker 1270.

`Langlands.GroupScheme.SplitParabolicCocharacterStatement.{u}` asserts the
following. Over every field `k : Type u`, let `G` be connected reductive,
let `j : T.toGrp ⟶ G` be a maximal torus with `T` split, and let
`i : P ⟶ G` be a geometric parabolic. If `f : T.toGrp ⟶ P` satisfies
`f ≫ i = j`, there is an actual cocharacter `nu : cocharacterLattice T`
such that

```
SubgroupFunctor.range i =
  Dynamic.parabolic (CommGroupScheme.groupHom nu ≫ j).
```

The cocharacter takes values in the specified torus `T`. The equality is
of the published subgroup functors, so it holds on every test scheme over
`Spec k`. All objects and maps are defined over `k`. There is no
restriction on characteristic or perfectness, and no assumption that
`G` is semisimple. The full-group parabolic and empty root system are
included. `IsParabolicSubgroup` supplies closedness and smoothness of `P`.

## Source and derivation

The source is Milne, *Algebraic Groups* (2017), source
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`,
Section 21.i, printed pp.452–455 (one-based PDF pp.468–471), especially
Theorem 21.91 and Corollary 21.92. The section starts with split reductive
`G`, then reduces to the semisimple quotient by the radical. Theorem
21.91 classifies parabolics containing a chosen Borel by subsets `I` of
the corresponding simple roots. Corollary 21.92 identifies the parabolic
of a dominant cocharacter by the simple roots on which its pairing is
zero. The associated Borel-pair results are Theorem 17.10 and the
paragraph after Definition 17.12, printed pp.354–355 (PDF pp.370–371),
and Theorem 21.32, printed p.434 (PDF p.450). The official 2017 errata
snapshot dated 2026-11-02 was read; it has no correction to 21.91 or
21.92. The derivation below does not use the necessity assertion of
21.68(d), whose small-characteristic defect is recorded in the errata.

This is a **derived formulation**, with three retained structural steps.
First, choose over an algebraic closure a Borel inside the parabolic
containing the given torus. The geometric parabolic is connected by
Corollary 17.49, printed p.367 (PDF p.383), and conjugacy of its maximal
tori permits this choice with the specified torus. For a split maximal
torus every such geometric Borel comes from a regular integral
cocharacter (21.32); the character and cocharacter lattices are unchanged
by extension of the field. Thus that Borel is defined over `k`, and its
containment in `P` descends. Apply 21.91 to obtain the subset `I`.
Choose a rational dominant cocharacter whose simple-root pairings are
zero on `I` and strictly positive on its complement, and multiply by a
positive denominator to obtain an integral cocharacter. Corollary 21.92
then gives the required parabolic.

Second, the source's reduction from reductive to semisimple groups must
be retained: parabolics correspond under the quotient by the central
radical, and the image of the split maximal torus is a split maximal
torus of the quotient. A rational cocharacter of the quotient torus
lifts to the original torus. Clearing denominators and using positive
scaling of a cocharacter preserves its dynamic parabolic. The inverse
image of the quotient dynamic parabolic is the original dynamic
parabolic, since the quotient kernel is central. These assertions are
structural inputs to a future proof; this statement does not assume
them as premises or supply their proofs.

Third, the source identifies smooth closed subgroup schemes. Equality
of their ranges is the displayed all-test formulation of that equality.
If a proof first compares geometric points, it must use reducedness of
the smooth closed representatives, descent of their defining ideals,
and the representation of the dynamic functor to obtain this stronger
all-test equality. Equality of rational-point subgroups alone does not
suffice.

This module only defines a proposition. It proves no classification,
root-sign comparison, representability result, or descent theorem, and
it does not assert `ParabolicDynamicStatement`.
