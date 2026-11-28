# The identity and inverse on the glued scheme

`exists_right_identity` solves `ce = c` at the closed point of the base,
with `c` a section of `Y` in the original chart. The neighbourhood is the
whole base since every point generizes the closed point. Associativity
then gives the right identity on the image of right translation by `c`
in the original chart. Its density gives the identity for the group
operation everywhere by agreement of morphisms.

Local solutions of `ab = e` and `bd = e` yield `ea = a` and `ba = e`
by associativity and the right identity. The equalities descend from
the open covers. Right inverses are then unique and glue on every test
scheme. `relativeGroupLaw` records the operations and their identities
on scheme-valued points. This proves the group-law step of BLR,
*Néron Models*, §5.3 Lemma 8, pp. 127–128, from total multiplication and
local division.
