# Actual norm-kernel compact projector from fixed-level finiteness

Worker 491 constructs the normal-subgroup compact projector on the actual
rational points and proves the all/no compact-restriction category decomposition
from fixed-level finiteness alone. This is an internal construction using
published intrinsic complements, normal-subgroup projectors, total compactness
and the arbitrary-subquotient category assembly.

Let `F : Type uF` be a nonarchimedean local field with its given topology and
valuation. Let `G` be an affine group scheme locally of finite type over `F`.
Its actual rational points carry exactly `rationalPointTopology F G.X`.
Assume this point group is nonarchimedean and locally compact. The construction
uses its actual common rational-character norm kernel with the induced subgroup
topology. The representation-carrier universe `uV` is independent of `uF`.

The supplied `hstrata` asserts that at each compact open subgroup of this kernel
only finitely many compact irreducible smooth classes have nonzero fixed
vectors. This is precisely the fixed-stratum condition in the published
norm-kernel fixed-level-finiteness statement; it is not proved here.

`rationalNormKernelCompactProjector G hstrata A` is an actual intertwining
endomorphism of any smooth complex representation `A` of the point group.
The published openness of the norm kernel supplies its local compactness;
the subgroup inherits the nonarchimedean neighborhood basis. The existing
`openSubgroup_isCompl_isotypic_annihilator` chooses a Borel structure and a
left Haar measure on the kernel. The intrinsic compact-class complement
theorem then supplies every complement required by `normalSubgroupProjector`.
Its construction uses finite fixed-level strata to make the sum of the
class projectors finite on each vector and proves ambient equivariance using
normality of the actual kernel.

The inherited laws prove idempotence, identify the restricted range with the
actual total intrinsic compact-isotypic subrepresentation, and prove naturality
for every ambient intertwiner. The projector and these three laws require no
admissibility, finite length or dimension assumption on `A`.

`rationalCompactRestrictionCategoryDecomposition_of_fixedStrata` additionally
assumes the point group is Hausdorff. Total disconnectedness of the given
local field and its affine rational points passes to the kernel. With the
kernel's Borel structure and a chosen left Haar measure, the published total
compactness and exhaustion theorems apply. The arbitrary-subquotient category
assembly supplies the existing `Renard.IsCategoryDecomposition` predicate for
`SmoothRep.compactRestrictionSubquotientProperties` of the actual kernel.
The `true` factor tests compact restriction for every actual subquotient;
the `false` factor excludes it for every nontrivial actual subquotient.
The result includes an actual coproduct presentation of every object and
off-diagonal zero morphisms.

No countability, right-invariance, measure regularity or rational-point
representation-theoretic splitting is supplied as a premise. In particular,
the complement hypothesis of the earlier conditional assembly has been
discharged, as have total compactness and exhaustion. Fixed-level finiteness
and both directions of the comparison between compact restriction and
proper-standard cuspidality remain obligations for the whole-cuspidal target.

Renard VI.3.5, French edition dated 9 July 2026, printed pp.146–147 /
PDF pp.152–153, motivates this use of the norm kernel, uniqueness and ambient
stability; A.IX, printed p.268 / PDF p.274, fixes the category-decomposition
convention. The implemented argument is the imported projector and
coefficient-permanence construction described above. This intermediate
module does not prove either original VI.3.4 or VI.3.5 statement, and it
does not add its remaining finiteness input to the unchanged final target.
