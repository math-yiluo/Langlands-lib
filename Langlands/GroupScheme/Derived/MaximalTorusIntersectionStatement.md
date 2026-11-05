# A maximal torus intersects the actual derived subgroup in a torus

Author: Worker 1435.

`Langlands.GroupScheme.DerivedMaximalTorusIntersectionStatement.{u}` is a
proposition definition. It states a geometric input for the cocenter quotient
and contains no proof of that input.

For every field `k : Type u`, take group schemes `G` and `D` over `Spec k`, a
commutative group scheme `T`, and homomorphisms `d : D ⟶ G` and
`t : T.toGrp ⟶ G`. The hypotheses are precisely `IsConnectedReductive G`,
`IsDerivedSubgroup d`, and `IsMaximalTorus t`, in their existing Library
meanings. The conclusion is

```lean
IsTorus (subgroupIntersection t d)
```

`subgroupIntersection t d` is the categorical pullback `T ×_G D` in group
schemes. It is the full scheme-theoretic intersection, retaining all its scheme
structure. The conclusion concerns this entire object, rather than a reduced
subscheme, an identity component, its geometric points, or a torus with the
same dimension. It asserts that the object becomes a finite product of
multiplicative groups over some field extension.

The field, characteristic and universe are unrestricted. In particular,
perfectness of the ground field and splitness of `G` or `T` are not hypotheses.
No smoothness, connectedness, reductivity or semisimplicity of `D` is assumed
separately. Those properties of an actual derived subgroup, if used in a
proof, must follow from the displayed hypotheses and proved Library results.
The torus property of the intersection also supplies its smoothness and
geometric connectedness through the existing torus geometry results.

## Source and scope

Kaletha and Prasad, *Bruhat–Tits Theory: A New Approach* (2023), source
`kaletha-prasad-2023-bruhat-tits-new-approach`, §2.6(a), printed p. 93 / PDF
p. 124, works over an arbitrary field and states that a maximal torus
intersects the derived subgroup in a maximal torus of that subgroup. The
present proposition records only the torus consequence of that assertion.
It uses the actual Library derived inclusion and the actual pullback to make
the intersection precise; it does not assert maximality of its second
projection into `D`.

The authors' *Corrections and additions*, version of 1 November 2024, source
`kaletha-prasad-2024-corrections`, PDF p. 25, lists changes in §2.6(d), the
text before Definition 2.6.20, and Definition 2.6.23. None changes §2.6(a).

This isolates the connected-kernel input needed for integral cocharacter
surjectivity in `CocenterQuotientExistenceStatement`. The existing
`DerivedMaximalTorusProductSurjectivityStatement` asserts surjectivity of
multiplication by the derived subgroup and does not identify this
intersection as a torus. `DerivedCoverMaximalTorusPreimageStatement` instead
concerns the full inverse image in a supplied simply connected cover. Neither
is used as an assumed proof of this proposition. A proof of the present
statement is a separate obligation.
