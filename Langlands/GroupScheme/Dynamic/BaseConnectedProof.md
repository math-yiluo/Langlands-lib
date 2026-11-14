# Connected dynamic fibres without smoothness over any base

Original proof: Worker 3483. Verification and submission: Worker 525.

The theorem `Langlands.GroupScheme.dynamicBaseConnected` proves the
unchanged published proposition
`Langlands.GroupScheme.DynamicBaseConnectedStatement.{u}` for every
universe `u`. It imports the statement from
[`BaseConnectedStatement`](BaseConnectedStatement.md).

For any scheme `S`, affine locally finitely presented `S`-group `G` and
cocharacter `χ`, it proves geometric connectedness of every representative
of `U_G(χ)`. If `G → S` is geometrically connected, it also proves this
for every representative of `P_G(χ)` or `Z_G(χ)`. No smoothness or
reducedness hypothesis is added. The conclusion concerns the fibres of
the representative's structure morphism, including after arbitrary
field-valued base change; it does not assert that its total space over
an arbitrary base is connected.

## Proof route

The implementation uses the Library's actual group schemes, dynamic
subgroup functors and representatives on all test schemes, including
nonreduced test schemes. The helpers are in the namespace
`Langlands.GroupScheme.DynamicBaseConnected`.

The rational unit of a connected group scheme is a section. The
published `geometricallyConnected_of_connected_section` therefore gives
geometric connectedness, without smoothness. Over a perfect field, the
reduction is smooth by `ReducedSubgroup.smooth_redOver`; its inclusion is
a surjective closed embedding, hence a homeomorphism. The reduction is
connected, so `CharacterLatticeProof.isIntegral_of_smooth` makes it
integral. Thus the original group is irreducible. For an arbitrary field,
base change to an algebraic closure, apply this perfect-field argument,
and descend irreducibility along the continuous surjective projection.
These helpers require only local finite type and connectedness of the
group; they do not require affineness.

For an affine connected field group locally of finite type, the theorem
`dynamicFieldOppositeCell`, imported from
[`FieldOppositeCellProof`](FieldOppositeCellProof.md), gives an open immersion
`U(-chi) × P(chi) → G`. The product is nonempty by the units. It is
connected as a nonempty open subspace of an irreducible space. Projection
to `P` has a section using the unit of `U`, so every supplied parabolic
representative is connected. The limit homomorphism from the explicit
parabolic to any centralizer representative has a section, which gives
connectedness of that representative too.

For `U`, the existing theorem
`DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent` already
works without smoothness or finite type, through the coordinate
contraction and idempotent argument.

Finally, after every field-valued base change of the arbitrary base
scheme, `SubgroupFunctor.IsRepresentedBy.baseChange` and the dynamic
base-change equalities give the corresponding actual representatives.
Affineness and local finite type are stable under base change; the
target's local finite presentation supplies local finite type.
Geometric connectedness of the ambient group gives connectedness of its
field-valued fibres for the `P` and `Z` branches. The three field
arguments establish the geometric connectedness predicate for the
representative structure morphism.

## Sources and provenance

The target is the connectedness assertion in Conrad, *Reductive group
schemes* (2014), Theorem 4.1.7(2), together with its arbitrary-base
extension after Example 4.1.9, pp.112–114, registered as
`conrad-2014-reductive-group-schemes`. The retained source is
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
Equivalently, the target is the relevant
assertions of Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second
edition (2015), Proposition 2.1.8(4), printed p.53/PDF p.79, registered as
`conrad-gabber-prasad-2015-pseudo-reductive`. The retained source is
`Conrad-Gabber-Prasad--Pseudo-reductive groups (book, 2nd edition)--2015.pdf`,
SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
Both source statements assume finite presentation and do not require
smoothness for the connectedness assertion. The target's relative
affineness and local finite presentation imply finite presentation, as
explained in its unchanged statement Markdown.

CGP's proof of part (4), printed p.56/PDF p.82, likewise passes to
fibres and uses the field open cell, irreducibility of a connected field
group, and the split parabolic-to-centralizer map. The Lean proof supplies
the irreducibility step through the existing reduction and rational-section
geometric-connectedness constructions, then applies the field open-cell
theorem. These intermediate lemmas are derived from the imported Library
results; neither the target proposition nor an unproved irreducibility
proposition is assumed as a parameter.

The affine base-change and geometric connectedness transport lemmas are reused from [BaseSmoothConnectedProof](BaseSmoothConnectedProof.md), with their original hypotheses and conclusions.
