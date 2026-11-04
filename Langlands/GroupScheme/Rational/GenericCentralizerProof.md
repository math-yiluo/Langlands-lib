# Proof: generic centralizers

`Langlands.GroupScheme.genericCentralizer : GenericCentralizerStatement.{u}` proves the
published statement `GenericCentralizerStatement` of
`Langlands.GroupScheme.Rational.Statement` at an arbitrary universe `u`. The statement
covers a field `k : Type u`, a connected reductive group scheme `G` over `Spec k`, a
maximal split torus `i : T.toGrp ⟶ G` and a cocharacter `ν` of `T` that is generic
(`IsGenericCocharacter i ν`: `ν` pairs nontrivially with every relative root). For these
data the dynamic centralizer `Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)` equals
the centralizer `torusCentralizer i` of the whole torus. Both sides are subgroup functors on
all test schemes.

## Proof as implemented

The theorem applies the conditional theorem `genericCentralizerStatement_of` from
`Langlands.GroupScheme.Rational.GenericCentralizerReduction` to four published proofs. The
Markdown of that module describes the argument in full. The four inputs are:

- `dynamicSmooth : DynamicSmoothStatement` (module `Dynamic.SmoothProof`): every
  representative of `Dynamic.parabolic χ`, `Dynamic.centralizer χ` or `Dynamic.unipotent χ`
  is smooth, for a smooth affine group over a field.
- `dynamicConnected : DynamicConnectedStatement` (module `Dynamic.ConnectedProof`): such
  representatives of the dynamic parabolic and centralizer have connected underlying space
  when `G` does. The unipotent representative is always connected.
- `dynamicLie : DynamicLieStatement` (module `Dynamic.LieProof`): for an affine group `G`
  locally of finite type over a field, an element `X` of the Lie algebra `lieKernel G k`
  lies in `Dynamic.centralizer χ` if and only if it has weight `0` for `χ`. The statement
  has similar clauses for the dynamic parabolic and unipotent subgroups, which are not
  used here.
- `lieSubgroupEquality : LieSubgroupEqualityStatement` (module
  `Lie.SubgroupEqualityProof`): let `H` be smooth and affine over a field with connected
  underlying space, and `j : K ⟶ H` a closed subgroup with `K` smooth. If every element of
  the Lie algebra of `H` is the image of an element of the Lie algebra of `K`, then
  `range j` is everything.

In outline, the reduction proves `torusCentralizer i ≤ Dynamic.centralizer (ν ≫ i)`
directly. For the other inclusion, `CocharacterCentralizers` reduces it to
`Dynamic.centralizer (ν ≫ i) ≤ Dynamic.centralizer (c ≫ i)` for every cocharacter `c` of
`T`. That inclusion compares two cocharacter centralizers inside the smooth connected
closed representative `H` of `Dynamic.centralizer (ν ≫ i)`. Genericity of `ν` makes the
weight-zero space of `ν ≫ i` on `Lie(G)` equal to the weight-zero space of the whole torus
(`weightSpace_zero_genericCocharacter`), so the centralizer of `c` in `H` has the whole Lie
algebra of `H` and is therefore all of `H`.

## Provenance

The target is Borel–Tits, *Groupes réductifs* (1965), 4.15(a), and Milne, *Algebraic
Groups* (2017), Theorem 25.6(b). The cited sources and the comparison with them are in the
Markdown of `Rational.GenericCentralizerReduction` and of the statement module. The derived
part of the argument is the comparison of two cocharacter centralizers through their Lie
algebras. This module adds no hypotheses: the four structural statements that the
reduction assumes are discharged by their published proofs.

The opposite-open-cell input now imports the unchanged proposition from
[`Absolute.OppositeCellStatement`](../Absolute/OppositeCellStatement.md).
Consequently this proof and `Dynamic.ConnectedProof` do not import
`Absolute.BorelStatement`. The rank-one dependency separation contributed by
Worker 1547 reuses these shared declarations: the repeated
`RankOneCentralizerInput` helpers and `genericCentralizerForRankOne` are
consolidated into `oppositeCellStatement`, the `DynamicConnected` helpers,
`dynamicConnected` and `genericCentralizer`, with their full mathematical scope
preserved. The open-cell and connectedness proofs retain the implementations
of Workers 254 and 1162.
