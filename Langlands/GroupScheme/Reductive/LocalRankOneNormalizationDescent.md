# Descent of actual rank-one normalizing points

This is an internal construction derived from the actual rank-one ring cell and
its coefficient transport. For arbitrary commutative `R`, `scalarWeylPoint xp xm d`
is the actual base point given by the Weyl product for `xp` and
`scaleHom d ≫ xm`. At every test scheme its coordinates are
`xm(-d) * (xp(1) * xm(-d))`, with scalars pulled back to that test.
`constantPoint_scalarWeylPoint` proves this formula, and
`baseChangeBasePoint_scalarWeylPoint` preserves the product and extends `d` by
the algebra map under every commutative coefficient extension. For supplied
`RingRootCell.WeylData`, taking `d` to be its beta unit gives exactly its
`normalizedWeylPoint` at the base test.

`IsNormalizingPoint.of_faithfulBaseChange` applies to group schemes over arbitrary
schemes, a commutative group scheme mapping into the ambient group, a prescribed
base point and an automorphism of the commutative group scheme. If pullback on
over-schemes is faithful, the normalizing identity for their actual base changes
implies the original identity. The proof uses faithfulness on the two group
morphisms and compatibility of inner conjugation with base change.

The actual-centralizer specialization is over any commutative local ring `R`.
It assumes an affine reductive group scheme `G`, a fibrewise maximal split torus
`i`, a fibrewise root datum on its actual lattices, a root `a`, a cocharacter `mu`
annihilated by `a` and by no roots except `a` and `-a`, and actual opposite root
parametrizations `hp` and `hm`. It also assumes that `i` is a closed subgroup and
supplies `AffineEtaleUnitCellData E` for the corresponding coroot centralizer
cell and coroot reflection. The latter data retain a prescribed point `n₀` over
the closed residue point. In `scalarWeylPoint_isNormalizing`, any scalar `d`
whose image in `E.ring` is the beta unit of `affineEtaleWeylData` gives a point
normalizing `torusHom` in the original relative cocharacter centralizer, with
exactly `corootReflectionIso hP a` as its action.

The proof identifies the pulled-back scalar product with the normalized Weyl
product in the affine coefficient ring. The normalized ring theorem supplies its
normalizing identity; split-torus coordinates identify its reflection with the
base change of the prescribed integral reflection. The pointed etale projection
is surjective over the local base, by the imported normalization-unit result,
so flat descent makes its pullback faithful. This descends the morphism identity
itself, retaining nilpotents.

`exists_normalizing_scalar` retains all those assumptions, including the supplied
`E` and residue point. It additionally assumes an actual factorization
`A(1) * B(epsilon) = cellPt y t x` in the original dual-number cell. The imported
coefficient comparison and unit-reflection theorem show that minus the epsilon
coefficient of `x` is a unit whose image is the inverse beta unit. Inverting that
unit gives `d : Rˣ` with beta image, and the preceding descent theorem proves the
normalizing identity. This module does not construct `E` or the dual factorization
from the remaining group hypotheses, and it does not prove the full local
Isomorphism Theorem.
