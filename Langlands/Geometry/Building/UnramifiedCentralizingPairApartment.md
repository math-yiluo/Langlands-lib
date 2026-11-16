# Centralizing pair apartments from an actual neutral-model torus

Author: Worker 362.

This internal assembly constructs a centralizing chart covering two points
from explicit neutral-model torus data. It works in arbitrary universe `u`
and imposes no characteristic restriction.

`centralizingPairApartmentOfNeutralTorus` takes lower component-model data
`N` over the original local integers. It retains the equality of the
unramified extension of `N.full`'s integral-point image with the
character-kernel fixer of the pair. The original ambient group is connected
reductive. A split original source torus maps into both the original
apartment torus and a second torus defined over the original field, with
literal commuting equations. The original apartment torus is maximal split
after unramified extension, and its supplied apartment and centralizer datum
satisfy the stated compatibility.

The remaining input is a split integral torus of the unramified
extension of `N.neutral`: more precisely, its actual residue inclusion must
be maximal split, and its generic fibre is identified, by an explicit
commutative-source isomorphism and exact generic square, with the
unramified extension of the second original-field torus. Closedness of the
integral inclusion is not an independent input here.
Existence and descent of this second torus, its integral lift, its splitting
and its residue maximality remain hypotheses.

The construction first applies `N.neutralPairReference` to obtain the
actual closed integral reference torus and a common translated chart.
`N.neutral_baseChange_integralPoints_le_fixingSubgroup` proves that the
same ambient model's integral points fix the pair. Smoothness follows from
base change of the supplied neutral model; geometric connectedness of its
fibres follows from component-model functoriality. In particular its
actual residue fibre is connected. The maximal-unramified integer ring is
Henselian and its residue map is surjective.

It then applies
`KPApartmentData.centralizingConjOfResidueMaximalIntegralTorus` with these
data. That construction derives generic maximality and integral conjugacy
from the residue-maximal torus and the generic-maximal reference torus.
It preserves coverage through the integral-point fixer inclusion and
adjusts the torus conjugator to centralize the shared split source.
The output is an actual point `g` centralizing that source after
unramified extension, with `g⁻¹ σ(g)` in the original torus normalizer
for every coefficient automorphism, and actual apartment coordinates for
both endpoints in the chart translated by `g`.

The provenance is composition of the named reference and fixation
constructions with the published centralizing integral-apartment assembly.
This conditional unit does not by itself prove the host fixed-pair
special-apartment statement.
