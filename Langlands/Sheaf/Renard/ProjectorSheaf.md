# Renard II.2.5: intrinsic projector-sheaf gluing

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, II.2.5, printed pp.39–40 / PDF pp.45–46,
the sheaf proof (II.2.5.1)–(II.2.5.2). Its registered identifier is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

This unit uses the actual compact-open basis and original-action presheaf of
`ProjectorPresheaf`. It proves the published intrinsic `SheafCondition`, and
`basisSheaf` bundles the actual normalized presheaf with this proof. The value
universe remains exactly the module universe `v`, independent of space universe
`u`. `familySheafCondition` and `unique_gluing` allow an index type in an
independent universe `w`, without a size, finiteness or countability premise.

The implementation follows Renard's finite binary gluing argument through the
published finite-union characteristic recurrence. Write `P_i` for the original
action of the indicator of `U_i`, and `Q_t` for the indicator action of their
finite union. Literal compatibility, tested on the actual compact-open
intersection, proves `P_i s_j = P_j s_i`. At each induction step the new vector
is `s_i + m - P_i m`. The maintained invariant is
`P_j m = Q_t s_j` for every member `j` of the original cover, including members
outside the selected finite family. This is the action form of (II.2.5.2).
All partial vectors are fixed by the target open's indicator.

Compactness extracts a finite subcover. Equality of its union with the actual
target open identifies their characteristic tests. The invariant then gives
the required restriction equation on every original cover member.
`finiteAction_eq` proves uniqueness by the same finite-union recurrence:
agreement after every selected member's projector implies agreement after the
union projector. The target's fixedness then identifies the vectors.

Empty finite unions act by zero, providing the induction base. Consequently
empty domains and empty covers are included in the intrinsic proof;
`empty_gluing` also exposes the unique zero gluing directly from normalization.
`empty_space_value` treats the empty space without a nonemptiness hypothesis.

Renard presents this construction for nondegenerate original test modules.
The additive gluing argument uses only the specified original nonunital module
laws, so its all-module form is an internal strengthening. It assumes neither
a separate complex action, a smooth extension, nondegeneracy, nor any output
separation or gluing property. Scalar sheaves, compact-section recovery,
equivalences and stalk comparisons remain separate constructions.
