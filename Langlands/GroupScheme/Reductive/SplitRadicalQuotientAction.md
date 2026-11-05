# Local products from affine-line rigidity of the radical quotient

Worker 1150; scope documentation corrected by Worker 1468.

This derived infrastructure constructs the canonical inclusion of a supplied
split ground-field unipotent radical into a supplied ordinary ground-field
unipotent radical. It uses their published all-test containment and the
factorization construction for represented subgroups. Its composition is the
specified ambient inclusion. Closedness follows by factoring a closed inclusion;
normality follows by identifying its full range with the inverse image of the
ambient normal subgroup. These inclusion, closedness and normality constructions
place no smoothness, connectedness or affineness assumption on the ambient `G`.
The theorem `exists_quotient_inRadical` additionally assumes that `G` is affine
over `Spec k`. Its closed ordinary radical is then affine, and the published
normal subgroup quotient theorem gives a smooth connected affine fppf quotient
of the ordinary radical by the canonical inclusion. These statements hold over
every field at arbitrary universe.

The theorem `fppfLocallyInProduct_parabolic_of_wound_quotient` is more general
than the radical specialization. Its ambient group `G` is smooth, connected
and affine over `Spec k`. It takes nested smooth closed subgroups
`V → U → G` with normal ambient images, a specified smooth connected affine
fppf quotient of `U` by the full image of `V`, and the explicit geometric
hypothesis `HasConstantAffineLineMaps Q`. It proves, on every relative scheme
test, that every point of the image of `U` lies fppf-locally in the ordered
product of the dynamic parabolic of an arbitrary cocharacter of `G` with the
image of `V`. It makes no assertion that radical maximality alone supplies
affine-line rigidity, and it does not prove the unconditional split-radical
product target.

The implemented proof restricts cocharacter conjugation to `U` using ambient
normality. The full image of `V` is stable under this restriction, so the action
descends to the specified affine quotient. The published affine-line rigidity
theorem makes this split-torus action trivial on every relative test. The
nonnegative character semigroup contains zero, so its quotient subgroup is
the entire quotient. The published realization and smooth quotient theorems
therefore supply an actual fppf image of the semigroup subgroup of `U` onto the
quotient. The full-kernel product construction supplies actual local factors.
Semigroup functoriality maps the left factor into the ambient semigroup subgroup,
which the dynamic comparison identifies with the requested parabolic. The right
factor maps into the specified image of `V` using the quotient's full kernel
identity and the commuting inclusion triangle. No local lifts or local sections
are assumed as inputs. This is internal composition of published constructions
and proofs; no additional external structural result is invoked.
