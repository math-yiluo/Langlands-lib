# Formal reduction of reductive Kottwitz descent

This derived proof unit proves
`ReductiveKottwitzDescentReductionStatement` and
`ReductiveKottwitzRationalRestrictionStatement`. It implements the cocenter,
z-extension and rational restriction steps in Kaletha–Prasad, *Bruhat–Tits
theory: a new approach* (2023), §11.5 and Lemma 11.5.1, printed pp. 429–430 /
PDF pp. 460–461. The authors' corrections of 1 November 2024, Chapter 11,
pp. 43–46, do not change these items.

The reduction is conditional on all five named input statements. It does not
prove the unconditional `ReductiveKottwitzDescentStatement` or any of these
inputs. In particular, the general-coefficient torus input retains every
coefficient-field quantifier of the original descent target; the proof does not
replace it by the narrower statement concerning tori over the local field `F`.

`cocenterTargetMap_equivariant` uses
`FundamentalInertiaMapStatement` and `TorusInertiaComparisonStatement` to
show that the two factors defining the actual cocenter target map commute with
the residual actions. Their composite therefore commutes with those actions.

`simplyConnectedDerivedKottwitz_equivariant_of_inputs` chooses an actual
cocenter using the existing `nonempty_cocenter` theorem. The
`SimplyConnectedDerivedKottwitzStatement` input supplies the chosen map's
cocenter square and injectivity of the target comparison. After applying that
comparison, the two sides of equivariance become equal by the cocenter square,
the preceding residual equivariance lemma, naturality of coefficient points
under the actual quotient homomorphism, and
`GeneralTorusKottwitzEquivarianceStatement`.

`reductiveKottwitz_equivariant_of_inputs` chooses a z-extension from
`ReductiveKottwitzExistenceStatement`. Its surjectivity on K-points gives a
lift of the point under consideration. Naturality of coefficient points
commutes this lift with the residual automorphism. The selected reductive
map's z-extension square expresses both sides using the
simply-connected-derived map. Its equivariance, followed by equivariance of
the induced fundamental inertia map, finishes the equality. Only consequences
of the five displayed inputs are used; the proof does not assume any extra
point-lifting or map-selection law.

`reductiveKottwitzRestriction_of_equivariant` assumes the explicitly named
`ReductiveKottwitzEquivariant` property of the selected K-point map. A rational
point extends to a coefficient point fixed by every residual automorphism, by
`GaloisPoint.conjugate_extend`. Equivariance therefore puts its Kottwitz image in
the invariant submodule. The proof constructs a homomorphism with this value,
proves its restriction property, uses injectivity of the invariant inclusion for
uniqueness, and applies classical epsilon specification for the selected rational
map. No existence, uniqueness, surjectivity or kernel property of the K-point map
is assumed beyond the displayed equivariance hypothesis.

`reductiveKottwitzRationalRestriction` packages this last lemma as the exact
published conditional rational restriction statement.

`reductiveKottwitzDescent_of_inputs` proves the exact published five-input
reduction. Its first conjunct is the general-coefficient equivariance lemma.
For the second conjunct it specializes that lemma to `k = F`, obtaining
`ReductiveKottwitzEquivariant`, and applies the rational restriction lemma.
Thus the restriction has values in the actual residual invariant submodule,
and uniqueness and correctness of the selected rational map are both proved.
Rational surjectivity is not part of either conclusion.
