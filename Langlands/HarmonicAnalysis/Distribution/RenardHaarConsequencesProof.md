# Inversion and positive scalar consequences of left Haar uniqueness

This helper unit proves two implications at the full group universe:
`rightHaar_of_leftHaar` derives `RightHaarStatement` from
`LeftHaarStatement`, and `positiveScalarUniqueness_of_leftHaar` derives
`PositiveScalarUniquenessStatement` from the same input. It does not supply
the left Haar assertion. The aggregate proof imports this unit and supplies
that assertion separately.

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
II.3.6 Proposition, printed pp.46–47 / PDF pp.52–53. The two source pages
were read. The positivity normalization consequence is also used in the
opening of II.3.7 on printed p.47. The proof below is a derived argument on
the published algebraic distributions and actual inversion maps.

The published linear involutions `GroupAction.inversionTests` and
`GroupAction.inversionDistributions` preserve nonzero nonnegative tests and
strictly positive distributions. The published intertwining identities
exchange left and right translation. Given a positive left Haar generator,
its inversion is therefore a positive right invariant generator. Inverting
an arbitrary right invariant algebraic distribution reduces its scalar
existence and uniqueness to the supplied left Haar assertion. Inverting the
result preserves the complex scalar because the inversion is complex linear.
No measure realization or continuity on the algebraic dual is used here.

For positive-real uniqueness, the common compact open invariance theorem,
applied to the empty test family, supplies a compact open subgroup. Its
indicator is a nonzero nonnegative test. Evaluating a strictly positive
distribution on this indicator shows that the distribution is nonzero.
If `S = c • T` for two strictly positive distributions, evaluation on that
same indicator gives zero imaginary part and strictly positive real part
for `c`. Thus `c` is the complex embedding of a positive real number.
Cancellation against the nonzero distribution proves uniqueness of that
real number.

Finally, two distributions invariant on the same side are scalar multiples
of a common Haar generator. The first scalar is nonzero because the first
distribution is strictly positive. Dividing the second scalar by the first
gives the needed proportionality, to which the preceding evaluation
argument applies. The right side uses `rightHaar_of_leftHaar`.

The auxiliary existence, inversion and scalar lemmas are internal derived
steps of this route. All the invariant distributions remain elements of the
full complex algebraic dual, with no countability hypothesis.
