# The two steps of the unipotent envelope in Chevalley's theorem

This module states two proposition targets, not proofs. Together they give
`Langlands.GroupScheme.ChevalleyUnipotentEnvelopeStatement.{u}`.

Worker 1328 adapted and checked the statement draft by Worker 1385.

Both statements fix an algebraically closed field `k : Type u` and a smooth
connected affine group scheme `G` over `Spec k`. Both also take a closed
subgroup `i : U ⟶ G` with `U` smooth, connected and unipotent. All
containments are inclusions of range subgroup functors on every test scheme.
Normality is the existing all-test-scheme `SubgroupFunctor.IsNormal`. No
reductivity assumption is imposed on `G`, and neither statement assumes that
`U` is normal or that `T` normalizes `U`. The Lean predicates are exactly
`IsClosedSubgroup`, `Smooth`, `ConnectedSpace`, `IsUnipotent`,
`IsBorelSubgroup`, `IsMaximalTorus` and `SubgroupFunctor.IsNormal`, with
containment expressed as `SubgroupFunctor.range i ≤ SubgroupFunctor.range b`.
Affineness and smoothness make `G` finite type over `k`; its closed smooth
subgroup `U` is also finite type. Thus these hypotheses give the group
varieties used in the source.

## Flag step

`UnipotentTorusBorelsToAllBorelsStatement.{u}`: let
`T : CommGroupScheme (Spec (CommRingCat.of k))` and `t : T.toGrp ⟶ G`
satisfy `IsMaximalTorus t`. Suppose the range of `i` lies in the range of
every `b : B ⟶ G` satisfying `IsBorelSubgroup b` and
`SubgroupFunctor.range t ≤ SubgroupFunctor.range b`. Then the range of `i`
lies in the range of every Borel subgroup of `G`.

## Envelope step

`UnipotentAllBorelsEnvelopeStatement.{u}`: suppose `U` lies in every Borel
subgroup of `G`. Then some smooth connected unipotent normal closed subgroup
`n : N ⟶ G` contains `U`. Its conclusion is literally the existential
conclusion of `ChevalleyUnipotentEnvelopeStatement.{u}`: it requires
`IsClosedSubgroup n`, `Smooth N.X.hom`, `ConnectedSpace N.X.left`,
`IsUnipotent N`, `(SubgroupFunctor.range n).IsNormal` and
`SubgroupFunctor.range i ≤ SubgroupFunctor.range n`, in that order.

## Provenance

Both statements are derived from Luna's proof of Chevalley's theorem in
J. S. Milne, *Algebraic Groups* (2017). Neither is a verbatim statement of
the source. Theorem 17.56 (printed p.371) identifies the reduced identity
component of the intersection of the Borels through `T`. Its proof in
Section 17.h (printed pp.373–375) has two parts. The source applies them to
`I_u(T)`, the unipotent part of that reduced identity component.

The first part is Theorem 17.65 (printed p.374) and the argument after it
(p.375). Theorem 17.65 shows that the sets `B(B)`, for Borels `B` through
`T`, are open affine subsets of the flag variety. The source shows that they
are stable under `I_u(T)` using only that `I_u(T)` lies in a parabolic
subgroup containing some Borel through `T`. For an arbitrary `U` satisfying
the flag step's premise, that same Borel contains `U`, so the same stability
argument applies; it does not require normalization by `T`.

The open sets `B(B)` cover the flag variety: the closure of each `T`-orbit
contains a `T`-fixed Borel. For any `U`-orbit, the Borel fixed point theorem
(Corollary 17.3, printed p.353) supplies a `U`-fixed point in its closure.
Choose an open set `B(B)` containing that point. Its closed `U`-stable
complement cannot meet the orbit, since otherwise it would contain the
orbit's closure. The orbit therefore lies in this affine open set. The
Kostant–Rosenlicht theorem 17.64 (printed pp.373–374) makes the orbit closed
there, so it contains the chosen fixed point and is a singleton. Thus `U`
fixes every point of the flag variety and lies in every Borel subgroup.
These steps use only smoothness, connectedness, unipotence and containment
in the Borels through `T`. The flag step states their conclusion with `U`
in place of `I_u(T)`.

The second part (p.375) uses Remark 17.31 (printed p.361). The reduced
identity component of the intersection of all Borels is the radical `R(G)`.
A smooth connected unipotent subgroup of `R(G)` lies in its unipotent part
`R(G)_u = R_u(G)` (Theorem 16.33(b), printed pp.335–336). That part is a smooth
connected normal unipotent subgroup of `G`. The envelope step states this
conclusion without naming a canonical radical construction: it asks only
for some closed subgroup `N` with the stated properties. `U` lies in that
reduced identity component because `U` is smooth and connected, hence
reduced.

The source's subgroup inclusions are inclusions of algebraic subgroup
schemes. Since the groups used here are smooth over the algebraically
closed field, containments detected on their rational points give these
scheme inclusions, hence containment on every test scheme as stated in Lean.

A private compiled assembly theorem checks that the flag step takes the
target's hypothesis unchanged and gives exactly the premise of the envelope
step. The latter then returns the target's conclusion without conversion.
That assembly theorem is not part of this statement module or its submission;
this module supplies neither a proof of either step nor a proof of the target.

The official author errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` has no correction to
Theorems 16.33, 17.56, 17.64 or 17.65, to Corollary 17.3, or to Remark 17.31.

Source: `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
