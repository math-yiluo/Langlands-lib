# Every cocharacter lies in a maximal split torus

Author: Worker 1294.

`Langlands.GroupScheme.cocharacterMaximalSplitTorus` proves exactly
`CocharacterMaximalSplitTorusStatement.{u}` from the unchanged module
`Langlands.GroupScheme.Rational.MaximalSplitTorusStatement`.

For every field `k : Type u`, every group scheme `G` over `Spec k` whose
structure morphism is affine and locally of finite type, and every
cocharacter `χ : (Gm (Spec k)).toGrp ⟶ G`, the theorem produces a commutative
group scheme `T`, a homomorphism `j : T.toGrp ⟶ G` satisfying the published
`IsMaximalSplitTorus j`, and a cocharacter `ν : cocharacterLattice T` with
`CommGroupScheme.groupHom ν ≫ j = χ`.

The proof first uses `isSplitTorus_gm` and
`IsSplitTorus.exists_factor_isSplitSubtorus` from
[`SplitTorusImage`](SplitTorusImage.md). This gives a commutative split
image torus `D`, a split-subtorus embedding `i : D.toGrp ⟶ G`, and a factor
`π : (Gm (Spec k)).toGrp ⟶ D.toGrp` with `π ≫ i = χ`.

Next, `exists_maximalSplitTorus_extension G i hi` from
[`MaximalSplitTorusExtension`](MaximalSplitTorusExtension.md) gives an actual
maximal split torus `j : T.toGrp ⟶ G` and a homomorphism
`f : D.toGrp ⟶ T.toGrp` with `f ≫ j = i`. The composite `π ≫ f` has
commutative source and target, so `Additive.ofMul (π ≫ f)` is the required
cocharacter `ν`. Its underlying group homomorphism is definitionally
`π ≫ f`. Associativity and the two factorization equations give the claimed
equality.

The extension theorem obtains existence from a nonempty bounded set of ranks
of split subtori containing the original one. Its
[`SplitTorusFiniteRank`](SplitTorusFiniteRank.md) prerequisite bounds these
ranks by the dimension of the actual ambient Lie kernel. Its
[`SplitTorusMonomorphism`](SplitTorusMonomorphism.md) prerequisite proves
that a monomorphism of split tori with equal finite ranks is an isomorphism,
using the surjection on integral character lattices. These are structural
proof inputs, not extra hypotheses on this theorem.

This is internal derived content with the provenance explained in the
published target's Markdown. The implementation composes the image and
maximal-extension results described above. The base field has arbitrary
characteristic and need not be perfect or algebraically closed. The group
scheme need not be smooth, connected or reductive. The trivial cocharacter
is included: the image theorem handles its trivial split image and the
extension theorem still constructs a maximal split torus. No conjugacy
statement or prior existence of maximal split tori is assumed.
