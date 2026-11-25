# Actual diagonalizable models on local adic quotients

For a commutative local ring `A`, `LocalAdic.Ring A n` is the actual quotient
`A / maximalIdeal(A)^(n+1)`. Its defining ideal is contained in the proper
maximal ideal, so the quotient is nonzero. Surjectivity of the quotient map
makes it local and makes the structural map local. The maximal ideal of the
quotient is the image of the maximal ideal of `A`; its `(n+1)`st power is
zero because mapping ideals commutes with taking powers. These statements
require neither noetherianity nor completeness.

`LocalAdic.isDiagonalizable A G hG n` assumes that `G` is flat and affine
over `A` and that its actual special fibre is diagonalizable. It proves
that the actual group over every `LocalAdic.Ring A n` is diagonalizable.
Flatness and affineness are preserved by base change. The published actual
special-fibre comparison identifies the special fibre of this group with
base change of the original special fibre, so it is diagonalizable. The
quotient ring has nilpotent maximal ideal, and the nilpotent deformation
result from `NilpotentDiagonalizableDeformation` reconstructs a
diagonalizable presentation of the whole group over the quotient.

`evaluate_bijective_of_isDiagonalizable` concerns the actual relative Hom
functor over any base scheme. Let the larger and smaller test schemes be
spectra of local commutative rings, with an actual map over the base. If the
source and target groups over the larger test scheme are diagonalizable,
restriction of relative Hom families to the smaller test scheme is
bijective. The canonical `Descent.pullbackComparison` isomorphisms identify
relative Hom evaluation with raw base change conjugated by those
isomorphisms. The local diagonalizable Hom comparison makes raw base change
bijective, so conjugation gives the required bijection.
`diagonalizableEvaluationEquiv` packages the actual evaluation map as an
equivalence.

Together these interfaces give the local adic group models and the
stepwise unique Hom restrictions needed for a compatible adic system when
the source is diagonalizable and the target has split diagonalizable
special fibre. This is internal derived content for the Artinian step of
Conrad (2014), Theorem B.3.2(2), pp.288–289. It does not construct an effective
infinite system or descend homomorphisms along a finite étale cover.
