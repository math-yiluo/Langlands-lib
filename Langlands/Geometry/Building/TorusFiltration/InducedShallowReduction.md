# Positive-depth reductions of induced torus models

Take the maximal unramified extension \(K\) of a nonarchimedean local
field \(F\), with valuation ring \(O\) and residue characteristic \(p\).
For \(0<r<1\), `InducedTorusShallow.modelOfFactors_reduction_pPower`
proves that the reduction of each integral section of `modelOfFactors`
is killed by a power of \(p\). Its coefficient algebra consists of pairs
congruent modulo `depthIdeal F E r`, the ideal of coordinate values
at least \(r\). The first coordinate of the section's unit is one.

The additive valuation of the base uniformizer is one by
`baseUniformizer_value`. Dividing by it takes the depth-\(r+1\) ideal
into the depth-\(r\) ideal. The proof chooses \(n\) with
\(p^n r\ge r+1\). Raising the unit difference to \(p^n\) gives a pair
with first coordinate zero and second coordinate in the depth-\(r+1\)
ideal. This pair is a uniformizer multiple in the pair algebra.
It therefore vanishes after reduction. In characteristic \(p\),
the \(p^n\)-th power of the difference from one is the difference
of the \(p^n\)-th powers. `WeilCongruence.reduction_eq_one_iff`
turns this into identity reduction of the powered section.

`InducedTorusShallow.exists_model_reduction_pPower` uses
`inducedTorusWeilDecomposition` to carry the factor model to any induced
torus over \(K\). `modelOfFactors_integralPoints` and functoriality of
geometric character congruence identify the exact point group. The
transport changes the generic identification and preserves the integral
group, so the reduction calculation carries over.

The models in this calculation implement the positive shallow
induced-torus construction of Kaletha–Prasad, *Bruhat–Tits Theory:
A New Approach* (2023), Proposition B.3.6, printed pp. 658–659,
PDF pp. 689–690. The power calculation is derived from `depthIdeal`,
`modelOfFactors` and the coefficient reduction formula in
`WeilUnitReduction`.
