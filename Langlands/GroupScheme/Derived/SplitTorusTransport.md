# Transport of derived-torus witnesses between actual derived-subgroup inclusions

Author: Worker 1464.

This internal module supplies a comparison isomorphism and proved transport
lemmas for the first existential layer of
`SimplyConnectedDerivedCoverSplitTorusStatement`. It does not prove the
existence of a maximal split torus of the derived group inside an assigned
ambient torus.

## Comparison of the supplied derived groups

Over an arbitrary scheme `B : Scheme.{u}`, let `d : D ⟶ G` and
`d' : D' ⟶ G` both satisfy the published `IsDerivedSubgroup` predicate.
They are closed immersions representing the same full subgroup functor
`derivedSubgroup G`, on all test schemes.

`IsDerivedSubgroup.iso hd hd' : D ≅ D'` applies the published
`SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy` to
`hd.isRepresentedBy` and `hd'.isRepresentedBy`. This compares the actual
representations; it does not choose a new derived subgroup.

The proved identities `iso_hom_comp` and `iso_inv_comp` say that its
homomorphism and inverse commute with the inclusions into `G`.
`eq_iso_hom` proves uniqueness: any group-scheme homomorphism `f : D ⟶ D'`
with `f ≫ d' = d` equals the comparison homomorphism. Its proof uses the
published extensionality lemma for maps into a representing subgroup.

## Transport of a derived-torus witness

For an arbitrary field `k : Type u`, group schemes `G`, `D` and `D'`
over `Spec k`, and two supplied derived-subgroup inclusions as above,
fix any commutative group scheme `S` and homomorphism
`i : S.toGrp ⟶ G`. No reductivity or maximality of `i` is assumed for
this transport result.

`exists_maximalSplitTorus_factor_iff` proves equivalence of the two
existential statements, for `D` and `D'`, that there are a commutative group
scheme `S_D`, a maximal split torus `j` in the supplied derived group and a
closed homomorphism `e : S_D ⟶ S` such that the composites into `G` agree.

For the forward direction, keep `S_D` and `e` and replace `j` by
`j ≫ (hd.iso hd').hom`. The published
`IsMaximalSplitTorus.comp_iso` preserves maximality under this ambient
isomorphism. The closedness of `e` is an unchanged hypothesis, and
`iso_hom_comp` proves the commuting equation by associativity. The reverse
direction uses the comparison in the opposite direction and the same
argument.

## Provenance and scope

The construction is internal and follows directly from
[`RepresentedSubgroup`](../RepresentedSubgroup.md),
[`Derived.Basic`](Basic.md) and
[`Rational.SplitRankTransport`](../Rational/SplitRankTransport.md).
No external mathematical assertion is assumed or introduced.
The statements use actual group-scheme morphisms and the equality of the
full range functors. They make no rational-point or characteristic
restriction.

The result discharges the representation-transport step needed when a
geometric construction first produces a torus in one representative of
the derived subgroup and the consumer supplies another. The geometric
existence, covering-torus and cocharacter arguments in the final target
remain separate obligations.
