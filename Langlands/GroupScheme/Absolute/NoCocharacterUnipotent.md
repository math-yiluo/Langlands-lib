# Connected groups without cocharacters over algebraically closed fields

Author: Worker 1487.

This internal supporting unit proves
`AlgClosedNoCocharacterUnipotentStatement.{u}`: for any algebraically
closed field `k : Type u`, a smooth connected affine group scheme `G`
is unipotent if every actual group scheme homomorphism `Gm ⟶ G` is zero.
There is no solvability or characteristic assumption.

It also proves the exact published
`AlgClosedTrivialMaximalTorusUnipotentStatement.{u}`, as well as the
closed-torus formulation: absence of nontrivial closed tori implies
unipotence under the same field and geometric hypotheses.

## Implemented proof

Embed `G` as a closed subgroup of a general linear group. The published
proper flag scheme has solvable closed subgroups fixing rational points.
The closed-orbit theorem supplies a reduced proper orbit `O`, its actual
action and a rational point `x`. Let `S` be the full scheme stabilizer of
`x`, and let `H = (S_red)^0` be its reduced identity component. The
published reduced-subgroup construction makes `H` a smooth connected
closed subgroup of `G` with open image in `S`. It fixes the image of `x`
in the flag scheme, so it is solvable.

Every cocharacter into `H` becomes zero after composition with its
monic inclusion in `G` and is therefore zero itself. The solvable
no-cocharacter criterion makes `H` unipotent. The actual smooth
homogeneous quotient `Q = G/H` exists. The orbit map identifies `O` as
an fpqc homogeneous quotient by `S`; the published properness transfer
for a subgroup with open image in a stabilizer makes `Q` proper. This
uses neither smoothness nor connectedness of the whole stabilizer `S`.

The proper homogeneous quotient criterion for a closed unipotent
subgroup now makes `H ⟶ G` an isomorphism: the actual affine vector orbit
descends to `Q`, where proper connected reduced affine-valued constancy
forces it to be constant. Unipotence transports from `H` to `G`.

For the closed-torus corollary, the actual image of a cocharacter is a
closed torus, so the hypothesis makes its inclusion zero and therefore
makes the cocharacter zero. For the exact maximal-torus target, a
range-trivial maximal torus has zero inclusion. Its zero map to any
closed torus of `G` is an isomorphism by maximality. Cancellation then
makes that closed torus inclusion zero. The closed-torus corollary
applies.

## Provenance and scope

This is a deduction from the imported actual flag action, closed orbit,
reduced stabilizer, homogeneous quotient, finite-index properness
transfer, solvable cocharacter criterion, proper unipotent quotient
criterion and torus image theorems. It follows the closed flag orbit
route through existing Library constructions and asserts no additional
structural input. The proper quotient criterion uses an affine vector
map in place of a quasi-affineness theorem.

The arbitrary-field `NoTorusUnipotentStatement` remains a separate proof
obligation. In particular this unit does not assert that a ground-field
maximal torus remains maximal after extending the field.
