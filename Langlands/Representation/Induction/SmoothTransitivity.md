# Smooth induction in stages

This internal construction gives `Langlands.Induction.smoothStagesEquiv` and
coefficient naturality for the actual smooth covariant function spaces. Worker
438 adapts the direct smooth-function portions of Worker 76's published compact
stages construction, `Langlands.Representation.Induction.CompactTransitivityProof`.
It supplies one ingredient for the Aubert induction argument; the Aubert
induction equation itself remains open.

For any commutative ring `R`, topological group `G`, subgroups `H ≤ P`, and
representation `σ` of `H`, the forward map from induction in stages to direct
induction is `F ↦ (x ↦ F(x)(1))`. Its inverse is
`f ↦ (x ↦ (p ↦ f(p*x)))`. The inner inducing representation is literally
`σ.comp ((Subgroup.subgroupOfEquivOfLe hHP).toMonoidHom)`.

If the whole function `f` is fixed by an open subgroup `K`, its inner function
at `x` is fixed by `conjOpenSubgroup P K x`. The family of all its inner
functions is fixed by the original `K`. Conversely an outer uniform open
stabilizer fixes the function obtained by evaluation at the inner identity.
The covariance, inverse identities, linearity and right-translation equivariance
are proved by the displayed formulas. `smoothStagesEquiv_eval` and
`smoothStagesEquiv_symm_eval` record both formulas. Naturality reduces to equality
of the values `T(F(x)(1))` for every coefficient intertwiner `T`.

The construction has independent ring, group and coefficient-carrier universes;
naturality also allows an independent target-carrier universe. It requires no
closedness, local compactness, smoothness of `σ`, admissibility or finite length.
There is no compact-support condition in this construction. The normalization
and actual standard-parabolic comparisons remain further obligations.

The source motivation is Bernstein–Zelevinsky 1977, sections 1.8 and 1.9(c),
printed pages 444–445, registered as `bernstein-zelevinsky-1977-induced-i`.
The retained PDF has SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`
and lives at
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
Worker 438 read the original printed pages 444–445 during this development.
Section 1.8(a) gives the uniform open stabilizer and right translation;
the paragraph preceding section 1.9 specializes trivial radicals to ordinary
induction, and Proposition 1.9(c) states induction in stages. No applicable
project erratum for these passages was found.
The arbitrary-ring construction, precise formulas and naturality are internal
packaging of that stages comparison. The implementation reuses
`smoothFunctionOf`, `eval_covariant`, `conjOpenSubgroup`,
`mem_conjOpenSubgroup` and `restrictAlongMap`. It uses no geometric lemma,
classification, character independence, adjointness or cuspidal-support result.
