# Restriction to the unitary Jacquet part for tempered representations

Authors: Worker 1629 and Worker 1593.

`temperedJacquetUnitaryRestriction` proves the exact published proposition
`TemperedJacquetUnitaryRestrictionStatement` at independent field and
representation-carrier universes `u` and `v`. The proposition is the
Jacquet-side restriction step of Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, VII.2.4,
printed p.229 / PDF p.235 (registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).

The proof introduces every quantifier of that proposition and installs the
same canonical rational-point topology on the ambient group and the same
`leviPointTopology` on the supplied rational Levi. The Levi's local
compactness and nonarchimedean-group instances are derived by the
published Levi-point transport.

For a tempered source `π`, the imported pointwise lemma
`IsNormalizedExponentTempered.unitaryJacquetPart_isCompl` gives
complementarity of the actual unitary and nonunitary Jacquet submodules.
That lemma derives admissibility of the specified normalized Jacquet
module from source admissibility and a compatible root presentation,
both already contained in `IsNormalizedExponentTempered`. The
presentation identifies the literal radical and Levi point images with
the corresponding dynamic groups, to which the published contraction
basis and Jacquet-admissibility theorem apply. Characteristic-space
spanning then supplies complementarity.

The proof applies the existing
`leviUnitaryJacquetRestriction_bijective_of_isCompl` to this derived
complementarity and the given tempered target `σ`. Its function is
literally precomposition with `leviUnitaryJacquetModuleι`. The imported
restriction construction extends a morphism by zero on the nonunitary
part; any morphism to a tempered target vanishes on that part, giving
the inverse law.

Thus the theorem adds no presentation-existence, Jacquet-admissibility,
splitting, standardness, compactness, finite-length, irreducibility or
central-character premise to the published target. Its quantifiers,
actual parabolic, Levi, radical and split component, normalized Jacquet
functor and inclusion remain unchanged. The proof does not need general
Jacquet-admissibility preservation for arbitrary admissible sources.

This proves the named restriction proposition. The source's full
Frobenius isomorphism also includes first adjointness, which is outside
that proposition. Temperedness of the unitary part and the
square-integrability criterion are the other two host-task targets and
are not conclusions of this theorem.

Worker 1593 supplied the pointwise structure route and its helper module;
Worker 1629 supplied the restriction construction and the exact-target
assembly here.
