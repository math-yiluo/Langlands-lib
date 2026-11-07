# Rational parabolic radicals generate the binary special linear group

This internal construction proves that the rational points of actual geometric
unipotent radicals of rational parabolic subgroups generate all rational points
of the existing split binary special linear group scheme. The field has arbitrary
characteristic and universe `u`; no local-field hypothesis is needed.

The existing `BinaryUpper.weylMatrix` from
`Langlands.GroupScheme.SpecialLinearBinaryBigCell` is the explicit determinant-one matrix with rows `(0,-1)` and
`(1,0)`. Direct multiplication proves that conjugation by this matrix takes
the upper transvection with coefficient `a` to the lower transvection with
coefficient `-a`, over any commutative ring. `weylPoint` is its actual rational
point under the published rational-point matrix equivalence.

For a normal subgroup of the actual rational-point group containing the upper
root image, each lower-root point is the conjugate of an upper-root point.
The proof chooses the upper coefficient to be the negative of the lower
coefficient, uses the surjective scalar-root parametrization, and checks the
equality under the actual rational-point matrix equivalence. Normality gives
containment. The published two-root generation theorem then proves
`eq_top_of_normal_upper_image`.

The actual triangular inclusion is parabolic, and its actual upper additive
root is its represented geometric unipotent radical, by the imported
constructions. Hence its rational upper-root image lies in the existing
`parabolicElementarySubgroup`. This subgroup is already proved normal by
conjugating actual parabolic embeddings. Applying the preceding generation
argument proves `parabolicElementarySubgroup_eq_top`. The universal property
of this subgroup gives `eq_top_of_parabolic_radical_images`: every subgroup
containing every actual rational parabolic radical image is the whole point
group, without an additional normality assumption.

The argument is derived from direct binary matrix multiplication, the existing
actual root maps and rational generation theorem, the actual triangular
parabolic and geometric-radical constructions, and the proved normality of
the elementary subgroup. It proves the split binary case of the generation
conclusion in local Kneser–Tits. General isotropic almost-simple simply connected
groups, nonsplit rank-one groups, and the unrestricted local statement remain
unproved here.
