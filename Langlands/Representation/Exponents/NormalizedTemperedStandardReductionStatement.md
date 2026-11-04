# Reduction of normalized-exponent temperedness to actual standard parabolics

`Langlands.Aubert.General.RepresentedParabolic.NormalizedTemperedStandardReductionStatement`
states a derived normalized-parameter formulation of Renard,
*Représentations des groupes réductifs p-adiques*, French version of
9 July 2026, VII.2.1, Remark 3, printed p.227/PDF p.233. The registered source
is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
This pair contains a proposition definition and supplies no proof.

## One actual standard family

Fix a connected reductive group scheme `G` over a nonarchimedean local field
`k` in the existing interface. The statement quantifies over one actual
commutative group scheme `T`, a map `i : T.toGrp ⟶ G` satisfying
`IsMaximalSplitTorus i`, and a cocharacter `ν` satisfying
`IsGenericCocharacter i ν`. The dynamic parabolic of
`CommGroupScheme.groupHom ν ≫ i` is required to satisfy the actual
`IsMinimalParabolicFunctor` predicate. This fixes the standard family for
the entire equivalence.

The right-hand tests quantify over every index `J : Set (characterLattice T)`
and cocharacter `ζ` with `IsStandardCocharacter i ν J ζ`. That predicate
includes `J ⊆ simpleRelativeRoots i ν`, vanishing of the pairing on `J`,
and strict positivity on the complementary simple roots. For every actual
parabolic map `p : P ⟶ G`, rational Levi map `l : M ⟶ P` and split-component
map `a : A.toGrp ⟶ M`, with their structural witnesses, four equalities
specify the tested standard representatives:

- `SubgroupFunctor.range p = standardParabolic i ν J`;
- `SubgroupFunctor.range (l ≫ p) = standardLevi i ν J`;
- `SubgroupFunctor.range p = Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i)`;
- `SubgroupFunctor.range (l ≫ p) = Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)`.

These are equalities of subgroup functors on every test scheme, not just
equalities on rational points. The same `ζ` realizes both images.
The shared `standardParabolic` and `standardLevi` are defined as
intersections over standard cocharacters. The explicit `ζ` and the two
dynamic equalities therefore retain the simultaneous-realization condition;
an empty intersection is not silently identified with an actual standard
parabolic and Levi.

## Exact equivalence

For every smooth complex representation `π` of `G(k)`, the proposition
asserts
`IsNormalizedExponentTempered hG π` if and only if `π` is admissible and
every standard representative just specified satisfies
`SatisfiesNormalizedExponentConeCondition p l a hp hl ha π`.
Admissibility remains part of the right-hand side, as required by the
definition preceding the source remark.

The reused cone condition requires a nonempty compatible
`ParabolicRootPresentation p l a`. It then tests every compatible
presentation, every actual represented geometric unipotent radical and
matching multiplication isomorphism, and every character satisfying
`IsNormalizedJacquetExponent` for those data. Its conclusion is membership
of `Plancherel.SplitTorus.normalizedRealPart` in the presentation's
nonnegative root-combination cone in the full real character space of `A`.
All split-component maps `a` are tested. No torus or cocharacter is selected
anew for each parabolic in the standard tests.

The statement assumes neither the equivalence itself nor conjugation
invariance or exponent transport. Proving the converse includes establishing
that this actual standard family supplies the required representatives and
transporting the exponent condition to arbitrary parabolic, Levi and
split-component maps. The universal tests are not a proof of structural
existence or standard-family completeness. Those remain obligations in a
proof of this proposition.

The canonical rational-point topology is installed explicitly. The field
topology is Hausdorff, and the ambient point group is explicitly locally
compact and nonarchimedean, following the published exponent interface.
Connected reductivity supplies affine and smooth structure, hence the local
finite type used by the root cones. All nonarchimedean local fields in the
current interface, arbitrary characteristic and nonsplit connected reductive
ambient groups are retained. The field and group use universe `u`, and the
representation carrier uses independent universe `v`. There is no
irreducibility, scalar-central-character or finite-dimensional carrier premise.

## Source convention and remaining obligations

The source Remark 3 invokes conjugacy of each rational parabolic to a
standard one. Its structural setup is V.3.9, printed p.112/PDF p.118, and
the root-combination cones are in V.3.14–V.3.15, printed p.113/PDF p.119.
The use here of actual subgroup maps, all-test equalities, simultaneous
cocharacter realization and all compatible presentations makes those
structural and transport obligations explicit.

This statement uses the derived normalized temperedness predicate.
V.3.20, printed p.116/PDF p.122, first uses the exponential based on
`q^(-s)` and later writes the raw natural logarithm of the modulus.
The published parameters obey
`rawLogRealPart hA χ = (-Real.log (LocalField.residueCardinality k : ℝ)) • normalizedRealPart hA χ`.
Since `q > 1`, the scalar is negative. No equivalence of membership of
these two parameters in the same nonnegative root cone is asserted here.
A consistent corrected-source comparison remains separate, so stating or
proving this derived proposition alone does not close the original
source-definition coverage of VII.2.1.

Full-group exponent unitarity, the full-center scalar-central-character
consequence, the Casselman implication, preservation by induction and the
later classification results are separate units.
