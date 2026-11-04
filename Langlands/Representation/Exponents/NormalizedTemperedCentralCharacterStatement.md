# Central characters of nonzero normalized-exponent tempered representations

`Langlands.Aubert.General.RepresentedParabolic.NormalizedTemperedCentralCharacterStatement`
is a proposition stating a corrected derived normalized-parameter formulation
of the second sentence of Renard, *Représentations des groupes réductifs
p-adiques*, French version of 9 July 2026, VII.2.1, Remark 1, printed p.227/PDF
p.233. The registered original source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
This pair states the assertion; it does not prove it.

## Actual meaning and scope

For every connected reductive group scheme `G` over a nonarchimedean local
field `k` in the existing `IsNonarchimedeanLocalField` interface, the
proposition quantifies a smooth complex representation `π` of the actual
group `rationalPoints G`, with nonzero carrier expressed by `[Nontrivial π]`.
For every homomorphism
`ω : Subgroup.center (rationalPoints G) →* ℂˣ`, it asserts

- `IsNormalizedExponentTempered hG π`;
- `π.HasCentralCharacter ω`;

together imply `‖(ω z : ℂ)‖ = 1` for every
`z : Subgroup.center (rationalPoints G)`.
The two listed properties are premises of the implication.

The imported `SmoothRep.HasCentralCharacter` from
`Langlands.Representation.Category.Basic` is precisely scalar action:
for every central point `z` and vector `v`,
`π.representation (z : rationalPoints G) v = (ω z : ℂ) • v`.
The conclusion concerns every element of the full center of the actual point
group. No split component replaces that center, no character is selected, and
existence of a scalar central character is not asserted.

The imported all-parabolic predicate `IsNormalizedExponentTempered`
includes admissibility and the normalized exponent cone condition for every
actual rational parabolic, rational Levi and split component. Its cone
condition requires nonempty compatible presentation coverage and tests every
compatible presentation and represented radical decomposition. The present
statement does not weaken that predicate or add a scalar-character condition
to its definition.

The canonical rational-point topology is installed explicitly. The field
topology is Hausdorff, and the ambient point group is locally compact and
nonarchimedean, as required by the actual exponent interface. Connected
reductivity supplies the affine structure for that topology. The field and
group lie in universe `u`; the representation carrier lies in independent
universe `v`. Arbitrary characteristic and nonsplit ambient groups are
retained. No irreducibility, finite-dimensional carrier, assumed smoothness of
`ω`, or assumed split-center-to-full-center implication is a premise.

## Necessary nonzero correction

III.1.1, printed p.58/PDF p.64, defines representations on arbitrary complex
vector spaces and imposes no nonzero convention. III.1.10, printed p.63/PDF
p.69, defines admitting a prescribed central character by scalar action.
The uniqueness parenthesis there, and the unqualified central-character
consequence in VII.2.1, need a nonzero qualification.

Indeed, every character satisfies scalar action on the zero representation.
The source's normalized exponent definition in VII.1.1, printed p.220/PDF
p.226, requires a nonzero generalized weight space, so the zero representation
has no exponents. It is admissible and meets the source's temperedness
condition vacuously. For the multiplicative group over a nonarchimedean local
field, the smooth absolute-value character is nonunitary: its value at a
uniformizer has modulus different from one. This gives a counterexample to
the printed consequence without a nonzero hypothesis. These are source
counterexample arguments; this module does not implement or kernel-check
that counterexample, or assert that the zero representation satisfies the
derived predicate's presentation-existence conditions.

The explicit `[Nontrivial π]` repairs this issue while leaving reducible
nonzero representations in scope. Nontriviality is not replaced by
irreducibility or any dimension bound.

## Normalization and retained proof obligations

The proposition uses the published derived predicate based on
`Plancherel.SplitTorus.normalizedRealPart`, with the normalized `q^(-s)`
parameter. V.3.20, printed p.116/PDF p.122, also uses a raw-logarithm
description. In the published positive-valuation convention,
`rawLogRealPart hA χ = (-Real.log (LocalField.residueCardinality k : ℝ)) • normalizedRealPart hA χ`.
The scalar is negative because `q > 1`. This pair does not identify the two
real-part parameters or their membership in the same nonnegative root cone.
The consistent corrected-source comparison for V.3.20 and VII.2.1 remains
separate.

VII.2.1, Remark 1 first asserts unitarity of full-group normalized exponents,
then gives the central-character consequence. The present proposition states
the corrected second assertion using the actual published definitions. It
does not assume the neighboring
`NormalizedTemperedFullGroupExponentStatement` as a premise.
Its proof must establish the needed actual full-center structure,
restriction to a split component, character smoothness from the nonzero
smooth action, and identity-Jacquet comparisons, or supply another checked
route to the same conclusion. This pair proves none of those steps.
The full-group exponent proof, other remarks, Casselman's criterion and
later induction and classification results remain separate obligations.
