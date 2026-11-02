# Compactness of actual dynamic-parabolic quotients

This unit states the compactness target for both coset conventions of an actual
dynamic parabolic over an arbitrary nonarchimedean local field. It defines a
proposition and supplies no proof of compactness.

## Source and derived formulation

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, V.5.1 corollary, printed page 123 / PDF page 129.
The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The corollary asserts that every parabolic subgroup is conjugate under the
adapted compact subgroup `K₀` to a standard parabolic and that `G/P` is compact.
This unit isolates the compactness assertion. The opening of V.5, printed page
122 / PDF page 128, attributes the section's results to Renard's reference [14],
Bruhat–Tits, *Groupes réductifs sur un corps local*, IHÉS Publications
Mathématiques 41 (1972), 5–251. No independent reading of [14] is claimed here.

The formulation is derived: it expresses compactness on the shared framework's
actual rational-point carriers for parabolics attached to rational cocharacters,
and includes both existing coset conventions. It does not prove that dynamic
parabolics exhaust the algebraic parabolics, nor identify a quotient with rational
points of a flag variety. Those comparisons, if used in a future proof, retain
their own construction and proof obligations.

## Exact proposition

`Langlands.BruhatTits.DynamicParabolicQuotientCompactStatement` is a `def`
returning `Prop`, with a single arbitrary universe `u`. It universally quantifies
these actual data:

- `F : Type u` with `[Field F] [ValuativeRel F] [TopologicalSpace F]`
  and `[IsNonarchimedeanLocalField F]`;
- `G : Langlands.GroupScheme (Spec (CommRingCat.of F))`;
- `hG : Langlands.GroupScheme.IsConnectedReductive G`, an explicit proof
  argument, since reductivity is a proposition rather than a typeclass;
- every rational cocharacter
  `χ : (Langlands.GroupScheme.Gm (Spec (CommRingCat.of F))).toGrp ⟶ G`.

For these data, the point group is exactly

```lean
Gpts := (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
```

with its existing group-object law under
`open scoped CategoryTheory.MonObj`. The subgroup is exactly

```lean
P := (Langlands.GroupScheme.Dynamic.parabolic χ).carrier
  (Over.mk (𝟙 (Spec (CommRingCat.of F))))
```

The statement installs `hG.isAffineHom` and derives `IsAffine G.X.left` by
`isAffine_of_isAffineHom G.X.hom`. It then explicitly equips this exact point
carrier with
`Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology F G.X`,
imported from its owning module
`Langlands.AlgebraicGeometry.PointTopology.RationalPoints`.
That published topology is induced from the affine evaluation topology on
`RingPoint F G.X F` through `rationalPointEquiv F G.X`; the comparison preserves
the underlying scheme morphism. No topology is supplied as an extra parameter.

The conclusion is exactly

```lean
CompactSpace (Gpts ⧸ P) ∧
  CompactSpace (Langlands.Induction.LeftQuotient P)
```

Here `Gpts ⧸ P` is `Quotient (QuotientGroup.leftRel P)`, with classes `g * P`.
`Langlands.Induction.LeftQuotient P`, imported from
`Langlands.Group.LeftQuotient`, is
`Quotient (QuotientGroup.rightRel P)`, with classes `P * g`.
Both carry the ordinary quotient topology induced by the explicitly installed
canonical topology on `Gpts`. Neither carrier is replaced by an abstract
isomorphic group or a flag-variety point space.

## Scope and remaining obligations

The quantifiers retain equal and mixed characteristic, nonsplit and nonquasisplit
connected reductive groups, all rational cocharacters including the trivial one,
rank zero, empty relative root sets, and the improper parabolic `P = ⊤`.
No characteristic, rank, properness, splitness, quasi-splitness or tameness
restriction appears. There is no compactness, Iwasawa decomposition, supplied
compact subgroup, flag-orbit, quotient-comparison or arbitrary-topology
certificate among the hypotheses. In particular, the proposition requires no
supplied `IsTopologicalGroup`, continuous inversion or group-topology comparison:
compactness is meaningful on these quotient spaces before those continuity
properties have been proved.

A proof of this exact proposition remains a separate obligation. The general
inversion-induced comparison of these two quotient conventions is also a
separate construction beside the existing quotient API; it is neither assumed
nor constructed here. The `K₀`-conjugacy assertion of the source corollary and all
remaining Chapter V structural and in-book deductions retain their obligations.
This statement uses the shared algebraic-group and point-topology definitions
outside the Renard tree and changes none of those definitions or consumer holds.

Author: Worker 125. Worker 6 contributed the source locator, exact target design
and scope guidance used in this formulation.
