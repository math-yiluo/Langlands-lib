# Native split stages from an actual kernel compact-open cover

This internally derived construction discharges the measure-existence and
neighborhood-basis inputs of `splitStagesAmbientCompactEquiv`. It uses the
published compatible quotient-measure existence theorem, compact-open-cover
unimodularity, and the compact-open subgroup neighborhood basis. It does not
assert the existence of a compact-open cover for an actual rational radical.

The ambient group is locally compact, Hausdorff and nonarchimedean. The retraction
`r : G →* L` and section `s : L →* G` split, are continuous, and have independent
group universes. The closed subgroups `H ≤ P` contain the section over `P.comap s`,
and `P` contains the closed kernel of `r`. The additional geometric hypothesis
says that every element of the actual ambient kernel `r.ker` belongs to a compact
open subgroup of that kernel.

The restricted retraction is literally `splitStagesRetraction r s hrs P hker`;
its kernel is `r.ker.subgroupOf P`. Its subgroup topology is identified with the
ambient kernel topology by `splitStagesKernelContinuousEquiv`.
`splitStagesCoveredKernelCover` pulls back each compact open subgroup along this
homeomorphism. Closedness of the restricted kernel follows by pulling back
closedness of `r.ker` along `P.subtype`, hence supplies its local compactness. The
intersection
`I = (H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype`
is closed in this kernel and is locally compact as well.

Choose Mathlib's regular Haar measure on this restricted kernel and on `I`.
The proved compact-open-cover unimodularity theorem makes both choices right
invariant: its ambient part applies to the restricted kernel, and its
closed-subgroup part applies to `I`. Thus all hypotheses of the proved
`compatibleMeasureExists` theorem hold.
`splitStagesCoveredQuotientMeasure` chooses a quotient measure from this theorem.
`splitStagesCoveredQuotientMeasure_isCompatible` supplies its nonzeroness,
regularity, right-translation invariance, integrability of compactly supported
complex subgroup averages and the complex Weil formula. Its regularity instance
also supplies finiteness on compact sets. These are proved measure properties,
not supplied representation-theoretic hypotheses.

The measurable structures of the restricted kernel, intersection and left
quotient remain arbitrary supplied Borel structures. No Haar measure, quotient
measure, measure-compatibility proof or neighborhood basis is supplied by the
consumer. The subgroup nonarchimedean instances and local compactness derive the
two required compact-open neighborhood bases from
`Langlands.compactOpenSubgroupBasis`.

For every commutative complex algebra `R` and smooth native `R`-representation
`σ` of `H`, `splitStagesCoveredCompactEquiv` is the equivalence from the native
kernel coinvariants of `compactInduced H σ`, restricted along `s`, to compact
induction from `P.comap s` of the original inducing normal coinvariants. The
coefficient ring and inducing-carrier universes are independent of both group
universes. Compatible complex and `R` scalar structures are retained.

The public comparison type installs the derived restricted-kernel local
compactness internally; consumers do not supply that instance.

The target uses the original action
`(σ.toCoinvariants (r.ker.comap H.subtype)).comp
  (splitStagesInducingSection s P H hsH)`,
twisted by the complex-algebra image of the same
`splitKernelHaarRatio` as the supplied-measure comparison. The definition applies
that comparison to the derived Haar measures, quotient measure and bases.
`splitStagesCoveredCompactEquiv_eval_mk` is its original-function evaluation:
the relative integral of the slice of `f` at `s(l)`, followed by the
class-preserving `splitStagesCoefficientEquiv`. Consequently its integrand still
represents the original value `f(n*s(l))` in the original inducing quotient.

The chosen measures depend only on the group data, closedness proofs and cover,
not on the coefficient ring, representation or carrier.
`splitStagesCoveredCompactEquiv_natural` therefore reuses the full ambient
naturality theorem with these same measure choices for every native inducing
intertwiner and independently sized target carrier.

This is an unnormalized compact split-stages construction. Actual rational
kernel covers, actual parabolic and orbit identifications, any normalization
identities, coefficient admissibility, a finite geometric filtration and the
universal-family fixed-module finiteness theorem remain separate obligations.
