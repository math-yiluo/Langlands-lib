# Renard VI.3.4: universal norm-kernel finiteness and decomposition

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, VI.3.4, printed pp.145–146 / PDF pp.151–152.
The fixed-level finiteness condition (KF) is stated in IV.1.7, printed p.95 /
PDF p.101, and verified for the norm kernel in the proof of VI.3.4. The
registered source is `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 6 reread these original PDF pages for this statement unit. Neither
proposition is proved here.

Both targets use an arbitrary nonarchimedean local field `F : Type uF`,
a connected reductive group scheme `G` over `F`, and the actual point group
with `rationalPointTopology F G.X`. They quantify over an actual maximal
split torus, a generic cocharacter, and the same explicit structural
premises as `RationalCuspidalInertiaFinitenessStatement`: local compactness,
nonarchimedean group structure and Hausdorffness of the actual point group,
`StandardCocharacterStatement`, `HasRelativeRootSystem i`, and closedness
of all actual standard unipotent point subgroups. The conclusions depend
only on `G`, its canonical topology and the representation universe; the
standard-family inputs provide the common representation-theoretic setting.
The carrier universe `uV` is independent of `uF`. No characteristic-zero,
split-group, general-linear-group or positive-rank restriction is imposed.

The subgroup in both conclusions is
`Plancherel.rationalCommonNormKernel G`: the intersection of the kernels of
the normalized absolute values of all actual rational algebraic characters.
It has the subtype topology inherited from the canonical point topology.
Its openness is supplied by the published `RationalNormKernelTopology`.
No auxiliary group, replacement topology or choice of character coordinates
occurs in either conclusion.

`Langlands.CuspidalSupport.RationalNormKernelFixedLevelFinitenessStatement`
asserts that for every compact open subgroup `K` of this actual norm kernel,
`CompactCoefficientClass.fixedStratum K.toSubgroup` is a finite set.
The reused class quotient consists of actual irreducible smooth complex
representations with compact coefficients against every smooth vector of
the algebraic dual. Membership in `fixedStratum` means that the actual
fixed-vector submodule is not bottom. It is invariant under isomorphism
by the published quotient construction. Thus the set counts isomorphism
classes with a nonzero fixed vector, rather than representatives or
inertia classes.

Condition (KF) is about compact open subgroups of the norm kernel itself.
The VI.3.4 proof uses the notation `K` for a compact open subgroup of `G`
while considering fixed vectors of a norm-kernel representation. This
target states the condition required by IV.1.7. Since the norm kernel is
open, its compact open subgroups are also compact open in `G` under the
actual inclusion. The inclusion, topology and fixed-vector comparisons
are proof steps to supply when following that route; no such comparison
is assumed in the target.

`Langlands.CuspidalSupport.RationalNormKernelCategoryDecompositionStatement`
concludes the published `IsRationalNormKernelCategoryDecomposition`.
Its `Option`-indexed family has, at `some c`, the full category of actual
coproducts of irreducible compact representatives of class `c`. Infinite
and empty multiplicities in the carrier universe are permitted. At `none`
it has the full category whose objects have no nonzero compact actual
smooth subquotient. The latter condition tests arbitrary subquotients,
not only irreducible subquotients. The zero exclusion is necessary because
the zero representation is compact and is a subquotient of every object.

The reused Appendix A.IX assertion, printed p.268 / PDF p.274, asks for an
actual coproduct presentation of each ambient smooth representation with
one component in each factor, and zero morphisms between distinct factors.
It imposes no separate existence of coproducts for all families at the
possibly larger compact-class index universe. The target does not assert
a constructed equivalence or projection functors. It neither replaces
the class-sum factors with irreducible-subquotient tests nor assumes a
comparison with such tests.

The source proves (KF) by extending a compact irreducible norm-kernel
representation to a supercuspidal representation of `G`, invoking VI.2.4's
uniform compact coefficient bound modulo the center, passing to compact
support on the norm kernel, and applying coefficient orthogonality in a
common finite-dimensional space of compactly supported bi-invariant
functions. IV.1.7 then gives the decomposition. Those arguments, the
averaging/compact-coefficient comparison, topology transports and actual
class-sum identifications remain proof obligations. Neither statement
assumes (KF), a projector, compact-restriction finiteness, a category
decomposition, admissibility, finite dimension, finite length, a central
character, or a finite family of restriction constituents.

The published `CompactCoefficientFixedLevelFinitenessTheorem` concerns
determinant-unit subgroups of positive-rank product Levis over `PadicField`.
It is a possible specialization input, not a proof of the present
arbitrary-characteristic connected-reductive target. Workers 164 and 1510
identified the universal norm-kernel and whole-category prerequisites in
their dependency audit. Worker 6 implemented these two targets over the
published full factors, separately from the VI.3.5 targets and the
VI.3.4 concluding inertia-class finiteness remark.
