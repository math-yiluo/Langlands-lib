# The descended middle exterior matrix algebra

Let \(M/K\) be finite Galois with a normal quadratic intermediate field
\(F\). A `UnitaryTwistedChart.Cocycle` of degree \(2m\) supplies twisted
projective lifts \(P_\sigma\) for the descent of the unitary algebra over
\(F\). The basis of the middle exterior power is indexed by the \(m\)-element
subsets of \(\operatorname{Fin}(2m)\).

`middleExteriorAction` acts on matrices indexed by these subsets. It applies
\(\sigma\) to the coefficients and then conjugates by the lift
`middleExteriorLift`. For \(\sigma\) fixing \(F\) the lift is \(\bigwedge^m
P_\sigma\). For \(\sigma\) moving \(F\) it is the product of \(\bigwedge^m
P_\sigma\) and the matrix of the wedge pairing. The scalar multiplication law
for these lifts is `middleExteriorLift_mul`. It gives a semilinear action by
`SemilinearGaloisAction.ofProjectiveLifts`. Its fixed algebra
`middleExteriorCSA` is central simple over \(K\), with the descent chart
`middleExteriorSplittingChart` over \(M\).

`middleExteriorCSA_classOf` identifies the Brauer class of this fixed algebra
with the discriminant class of the descended unitary algebra computed in
`c.action.descentEquiv`. This is the middle exterior construction of the
discriminant algebra in Knus–Merkurjev–Rost–Tignol, *The Book of Involutions*,
(10.25) and (10.28), printed pp. 126 and 128.

The proof computes the relative class of the fixed algebra using
`relativeClass_ofProjectiveLifts`. Its factor set is `detCocycle` evaluated on
the original lifts and their twisted scalar factors. The pure tensor
\(1\otimes b\) maps to the matrix underlying \(b\) in the chart of the unitary
algebra. On these matrices the lifts fixing \(F\) act trivially and all other
lifts act by the descended involution. These are the hypotheses of
`relativeDiscriminantClass_eq_of_lifts`, which identifies the relative
discriminant class with the same factor set. The comparison with the
absolute Brauer group sends both classes to the inflation of this relative
class over a supplied separable closure.
