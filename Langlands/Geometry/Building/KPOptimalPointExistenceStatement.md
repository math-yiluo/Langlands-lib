# Existence of a rational optimal point (KP §13.4)

`Langlands.Geometry.Building.AffineRootSystem.OptimalPointExistenceStatement`
expresses the existence assertion after Definition 13.4.2 in Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), printed pp. 472–473 / PDF
pp. 503–504. The authors' corrections of 1 November 2024 do not change it
(Chapter 13, PDF p. 49).

The ambient space is a real affine torsor `A` for the real translation space
`V`. The set `Ψ` of affine roots satisfies `IsAffineRootSystemWithRankZero`,
the Library's form of the corrected Definition 1.3.1 axioms (book printed
pp. 14–15 / PDF pp. 45–46; AR 4 addition in corrections PDF p. 2), and
admits a positive rational period, i.e. a member of `rationalRootPeriods Ψ`.
For any regular chamber representative `c` and nonempty `Finset S` contained
in `positiveRootsBelowPeriod Ψ c` (the strip `Σ` using the least period),
the proposition asks for a point `x` satisfying `IsOptimalPointFor Ψ c S x`.
Thus `x` is in the closed chamber, maximizes the minimum value of the roots
of `S` there, and gives a rational value to **every** root of `Ψ`, not just
to those in `S`. Under these hypotheses the least period exists whenever
`S` is supplied: nonemptiness of `S` implies nonemptiness of `Ψ`, and the
bounded-finite derivative fibres give a least period in `KPOptimalPoints`.
No assertion of an optimal point is made when `Ψ` is empty, since there is
then no admissible `S`.

This is an affine-root-system formulation of the source's assertion on
one apartment. The supplied valuation-apartment interface provides the
axioms and has positive rational period `2` by `KPOptimalPoints`. It is
not necessary to assume characteristic, splitness or irreducibility of
the root system in the formulation. The statement does not identify the
literal §13.4 positive indecomposables with Chapter 1 wall roots, choose a
canonical optimizer, construct the actual building, or assert Lemma 13.4.4.
It is a Prop-valued target, not a proof. No external code is adapted.
