# Finite-place cutoffs under positive-torus averaging

`positiveAverageOrbitSupport` proves `PositiveAverageOrbitSupportStatement`
for an affine group scheme over a number field. The supplied torus
is split and the restriction of rational characters along its map
to the group is injective with finite-index image. A fixed compact
set in the adelic group gives a fixed compact set in its norm-one
group, valid for the positive averages of all functions supported
in the original set. The statement allows any measure on the
intrinsic positive subgroup, including the normalized Haar measure
used in the ordinary and twisted simple trace formulas.
If a value of the average is nonzero, the norm-one point lies in the
new compact set, and a point in the support of the original function
has all the same finite-place components.

The new compact set is the image under `normOneFactor`, which is
continuous. The positive split torus has trivial image in every
finite completion, so removing the positive factor preserves all
finite components. A nonzero integral implies a nonzero integrand
at some positive point. The norm-one factor of that point times
the original norm-one point is the original norm-one point.
The same argument on the left centralizer quotient shows that a
nonzero twisted orbital integral of the average forces a
norm-one twisted conjugate in the compact set with the stated
finite components. Ordinary conjugation is the identity twist.

This is an internal support lemma for the norm-one and split-centre
convention of Getz–Hahn, §2.6, and the positive averages in the
Library's two simple trace formula statements based on §§18.4–18.5.
