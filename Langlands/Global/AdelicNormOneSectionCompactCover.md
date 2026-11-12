# Compact norm-one representatives from a scheme section

Author: Worker 82.

This internal derived unit combines compact rational representatives along an
actual quotient with an actual scheme section. All point carriers, rational
maps, norm-one subgroups and topologies are the existing Library constructions.

`normOneSectionCompactSet j s CK CV` is the part in the actual norm-one
subgroup of the product of the image of `CK` under the kernel inclusion and
the image of `CV` under the section. Here `CK` consists of full adelic kernel
points, and `CV` consists of norm-one adelic quotient points. If these two
sets are compact and the middle group is affine, this set is compact:
scheme postcomposition and multiplication are continuous, and the norm-one
subgroup is closed.

`hasCompactNormOneRationalCover_of_section` assumes a group homomorphism
`q : H → V`, a map `j : K → H` whose all-test image equals the actual kernel,
a scheme section of `q`, a full compact rational cover of `K`, and a
norm-one compact rational cover of `V`. It constructs a compact norm-one
rational cover of `H`. The section need not preserve multiplication or
norm-one points. For a norm-one point `h`, first translate `q(h)` by a
rational quotient point into `CV`. The section lifts both that rational
point and its translated adelic value. Their discrepancy with `h` lies
in the actual kernel, so a rational kernel translate puts it in `CK`.
The resulting principal rational translate of `h` is in the product
defining the compact set and remains norm one by the product formula.

`HasCompactRationalCover.normOne` also restricts a full compact rational
cover to the closed norm-one subgroup.

For `hasCompactNormOneRationalCover_of_rationalLevi`, the existing
`IsRationalLeviSubgroup` supplies an actual retraction and its exact
all-test kernel. The geometric unipotent radical is smooth, connected and
unipotent, so the published perfect-field splitting and affine torsor
theorems give its full compact rational cover. Thus compact norm-one
representatives for the Levi imply the same for the original group.
When this Levi is a split torus, the unconditional split-torus compact-cover
theorem supplies that input. The last theorem consequently proves compact
norm-one representatives for every such actual split-torus Levi
decomposition, without a reduction-theory premise.

The source motivation is Springer, *Reduction theory over global fields*
(1994), §2.1 and Remark 2.2(a), printed pp.211–212 (PDF pp.5–6), and the
unipotent-quotient step of §3.5, printed p.215 (PDF p.9). The registered
source is `springer-1994-reduction-global-fields`, SHA-256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`, file
`literature/Reduction theory over global fields (Springer, 1994).pdf`.
No errata note exists. The general section lemma is derived infrastructure;
its proof adapts the published full-cover section argument in
`SplitUnipotentRationalQuotientCompact` to a norm-one quotient.

This unit proves no existence of a rational Levi in a supplied group,
no compactness for a general Levi, no root bounds and no Galois descent.
It does not prove the general central-maximal-split-torus compactness theorem.
