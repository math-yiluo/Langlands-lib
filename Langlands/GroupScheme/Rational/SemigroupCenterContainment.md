# Full-centre containment from a fixed split torus

Worker 1372.

This module proves the formal semigroup consequence of an actual fixed closed
split torus. It also gives a conditional full-centre containment theorem using
`FixedCenterContainingTorusStatement`. It does not prove that structural
existence proposition.

`range_le_semigroupSubgroup_of_fixed_splitTorus` works over any field and for
any affine ambient group scheme, without a smoothness or connectedness
assumption on that ambient group. It assumes split acting and embedded tori,
a closed inclusion of the embedded torus, an action fixing its points on every
test scheme, and an additive semigroup containing zero. Its conclusion is the
all-test inclusion of the torus range in the actual semigroup subgroup.

The implemented proof equips the embedded torus with the actual trivial action.
Its Lie weights are supported at zero. The existing trivial-action theorem
therefore identifies its semigroup subgroup with the whole torus, using the
proved smoothness and connectedness of split tori. The inclusion is equivariant
by the supplied fixedness identity. The existing semigroup transport theorem
for closed inclusions maps this whole-torus semigroup subgroup into the ambient
semigroup subgroup. This argument uses only the closed-inclusion transport
proof and does not assume general semigroup functoriality, realization,
intersection comparison or a quotient theorem.

`center_le_semigroupSubgroup_of_fixedCenterContainingTorus` specializes to a
connected reductive group over an algebraically closed field. It retains
`FixedCenterContainingTorusStatement.{u}` as an explicit premise, extracts
the fixed closed split torus and composes its full-centre containment with the
generic inclusion just proved. The conclusion concerns the complete centre
functor, including infinitesimal points. No smoothness of the centre is
required or deduced.

The formal deductions are internal consequences of the published all-test
constructions and the new structural proposition. Their source motivation is
the centre reduction in Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second
edition (2015), proof of Proposition 3.3.10(c), printed p.113 / PDF p.139:
when zero belongs to the semigroup, the maximal torus used there, and hence
the full centre, lies in the semigroup subgroup. The companion statement's
Markdown records the exact structural source and remaining proof obligation.
These lemmas do not establish semigroup images under nonsmooth centre
quotients or the full normal intersection comparison.
