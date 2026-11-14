# A fixed lifted reflection cell for a descended cyclic action

This internal construction supplies the residue-field normalizer and translated
cell used in the unramified facet comparison. Every field and group has arbitrary
universe `u`. The source is affine, and its quotient is connected reductive with
the given torus mapping to a maximal split torus. The actual fppf quotient kernel
is represented by a smooth connected closed unipotent subgroup. The field is
perfect for the exact source normalizer lift.

The conjugation action on the quotient must actually descend through the
specified original character to an automorphic action of `Gm`. The original
character pairs positively with the chosen cocharacter. Its dynamic positive
subgroup must be nontrivial. The original character is not required to belong
to the quotient's actual relative roots.

First the full scheme-theoretic character kernel acts trivially, because the
conjugation action is the restriction of the descended action. Its full kernel
centralizer is therefore the whole quotient on every test scheme. The published
full-kernel root-support theorem implies that every actual quotient root is an
integral multiple of the original character.

`cyclicDynamicRoot` then selects an actual indivisible positive quotient root
`b`, independently of any later point, and identifies both dynamic subgroups
with `U_b` and `U_(-b)` on all test schemes. The fixed root reflection normalizer
from `RootReflectionTranslatedCell` lifts through the unipotent quotient kernel,
retaining its actual torus automorphism. Since `b` is a positive multiple of the
original character, negation of `b` forces negation of that original character
by split-torus character rationalization.

`dynamicReflectionNormalizerLift` returns the actual source point and torus
automorphism together with their normalization equation and character negation.
The same pair works for every nonidentity point `x` in the quotient dynamic
positive subgroup: its subtype retains

`x = y * z * q(m) * w`,

where `y` and `w` belong to the quotient dynamic negative subgroup and `z`
belongs to the quotient dynamic centralizer. The centralizer comparison uses
the actual descended action and the nonzero character pairing.

The proof is an internal composition of the named root-support, cyclic
comparison, fixed-cell and perfect-field quotient-lifting results. It does not
lift the cell factors integrally or prove the final facet root-datum assertion.
