# Stability of the full relative polarization predicate under canonical base change

`Langlands.AbelianScheme.PolarizationBaseChangeStatement` states
preservation of the existing whole `IsPolarization` predicate by the
existing canonical dual-valued base-change map. It is a `Prop`-valued
proof obligation, not a proof of preservation.

For arbitrary schemes `S`, `S'` in one universe and an actual map
`b : S' ⟶ S`, let `A` be an actual abelian scheme and
`lam : A ⟶ dualAbelianSchemeFromEvaluation A` an actual relative
polarization. The conclusion says that
`dualAbelianBaseChangeMap ... b A ... lam` is a relative polarization
on the actual changed abelian scheme. This homomorphism is exactly
the actual pullback of `lam` followed by the forward canonical
`dualAbelianBaseChangeIso`. Its target is the constructed dual of
the changed abelian scheme, rather than an arbitrary identified
target.

The premise and conclusion use the full existing `IsPolarization`
definition. Each contains an actual isogeny condition and, for every
algebraically closed field in the schemes' universe and every
geometric point of its base, a
`HasFieldAmpleMumfordPresentation` assertion. The latter uses the
actual canonical scheme comparison and permits a further field
extension as in `FieldPolarization`. The desired result is thus
stronger than an isogeny base-change lemma or a field-polarization
assertion on a selected geometric fibre.

Both endpoints retain their actual `HasDualScheme` witnesses,
the geometry of those selected dual parameter schemes, ordinary
inverse Poincare line bundles and tensor evaluation isomorphisms.
The statement quantifies over every such pair of choices and
uses the same endpoint choices in every occurrence.
The seven inputs for the constructed dual group structures are
explicit, as are `MumfordBundlePicardZeroStatement`,
`PicardZeroUniversalBaseChangeStatement` and
`DualAbelianBaseChangeStatement`. These inputs concern the existing
tensor, pullback, family-classification and canonical-comparison
constructions. They do not assume the polarization-preservation
conclusion.

No flatness, noetherian, quasi-separated, field or projectivity
hypothesis is imposed on `b` or the bases beyond the explicitly
supplied construction data. No dual-map additivity is required
to state this integral stability result. No rational action or
faithfulness assertion occurs in it.

The provenance is internal: this is the compatibility required
between the Library's existing canonical dual pullback and its
geometric-fibre definition of relative polarization. Worker 144
identified the remaining family-comparison obligations and Worker
57 formulated the exact target. The isogeny conjunct should follow
from actual isogeny base change and composition with the canonical
isomorphism. For a point `s' : Spec K ⟶ S'`, the other conjunct
must compare the actual iterated fibre with the actual direct fibre
at `s' ≫ b`, together with their canonical dual comparisons. It
must then transport the given ample-Mumford presentation, including
its line bundles, normalization, inverse/evaluation data and
classifier equality. Ampleness and those family/classifier
equalities must be justified across the actual isomorphisms.
`IsPolarization.geometricFibre` alone does not establish that
comparison.

This file does not supply these comparisons or a proof of
polarization stability. It does not claim existence of polarizations,
preservation of an involution equation or of a faithful action,
pointed Weil-level pullback, a varying-base polarized quotient,
representability or scheme levels. The statement retains all
existing pauses on unconditional Picard, inverse-bundle,
ampleness-existence and related infrastructure.
