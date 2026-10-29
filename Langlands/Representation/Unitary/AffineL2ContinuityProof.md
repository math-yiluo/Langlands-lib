# Joint continuity of the actual normalized affine L² action: proof

Authors: Worker 452 and Worker 971.

This module proves
`Langlands.AffineL2.jointContinuity : Langlands.AffineL2.JointContinuity F T`
from the published statement in
`Langlands.Representation.Unitary.AffineL2ContinuityStatement`. It also
exports the two component theorems `continuous_operator` and
`continuous_mirabolicRepresentation`. It imports the published generic proof
`Langlands.Analysis.NormalizedL2PullbackContinuityProof`.

## Exact statement

For every prime `p` with `[Fact p.Prime]`, `F : PadicField.{u} p`, and
supplied `T : F.TopologicalData`, the theorem uses `T.topology` and the
inherited finite product, matrix-unit, subgroup, and product topologies.
It quantifies over every `n : ℕ`, including zero, every measurable
structure on `Fin n → F.Carrier` with its `BorelSpace` instance, and every
actual additive Haar measure `μ` there. It proves joint continuity, with
the L² norm topology on the carrier, of

```text
((A,v),f) ↦ operator F T μ A v f,
(g,f)     ↦ mirabolicRepresentation F T μ g f.
```

The first parameter space is
`GeneralLinear n F.Carrier × (Fin n → F.Carrier)`. The matrix group has
the units topology over the entrywise matrix topology. The second uses the
actual mirabolic matrix subgroup of rank `n+1`, with its subspace topology.
Both operators act on the actual almost-everywhere quotient `Lp ℂ 2 μ`.
By the published representative formulas, the affine action is represented
`μ`-almost everywhere by

```text
x ↦ |det A|^(-1/2) f(A⁻¹(x-v)).
```

The determinant norm is residue normalized, and the factor is the published
positive inverse square root. For `g`, the coordinates `A,v` are its actual
leading block and final column. The construction supplies the left-action
multiplication law in these affine coordinates.

No regularity, measure-scaling, local-constancy, or continuity premise is
added to `JointContinuity F T`. The conclusion applies to every additive
Haar normalization. The local instances for the field topology, valuative
relation and local field are installed before the dependent Borel and Haar
binders. This module states no separate orbit corollary and makes no
operator-norm continuity claim.

## Implemented proof

The private helper `isLocallyConstant_of_isOpen_ker` takes a group
homomorphism `χ` with open kernel. At `x`, the open set
`{y | y * x⁻¹ ∈ χ.ker}` contains `x`. Its points satisfy
`χ y * (χ x)⁻¹ = 1`, hence `χ y = χ x`. This proves local constancy
without requiring a topology or continuity hypothesis on the target group.

Apply this helper to `T.determinantNorm n` using its published theorem
`T.isOpen_ker_determinantNorm n`, and postcompose with the coercion
`ℝ≥0ˣ → ℝ≥0`. Projection to the matrix coordinate then gives local
constancy of `(A,v) ↦ (T.determinantNorm n A : ℝ≥0)`.

For inverse-affine evaluation, unfold the published measurable equivalence
to `(A⁻¹).val.mulVec (x-v)`. Mathlib's `Units.continuous_coe_inv`,
`Continuous.matrix_mulVec`, and continuity of subtraction prove joint
continuity in `A,v,x`.

The generic continuity theorem needs `R1Space` on both spatial types,
`μ.InnerRegularCompactLTTop` and `IsLocallyFiniteMeasure μ`. Inside
`continuous_operator`, the proof installs the field topology, valuative
relation and local field instances, and also the published theorem
`T.secondCountableTopology` from
`Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof`. Lean's instance
search then supplies the required instances for `Fin n → F.Carrier`.
Inner regularity on compact sets uses the second-countability instance
and fails to synthesize without it. Local finiteness comes from the Haar
instance on the locally compact space. No separate Hausdorff instance
is installed.

Apply the published theorem
`NormalizedL2Pullback.locallyConstantScalingContinuity` with both spatial
types equal to `Fin n → F.Carrier`, both measures equal to `μ`, and
parameter space `GeneralLinear n F.Carrier × (Fin n → F.Carrier)`.
Use the inverse-affine measurable equivalence, the determinant-norm scalar,
its nonvanishing as a unit, and the published exact identity
`AffineChangeOfVariables.padic_map_haar_symm`. The inverse pushforward
factor is `|det A|`, giving exactly the constructed normalization
`|det A|^(-1/2)`. This proves `continuous_operator` for the actual
`AffineL2.operator`, which unfolds to that normalized pullback.

For `continuous_mirabolicRepresentation`, unfold the actual representation
to the operator with `GeneralLinear.Mirabolic.linearPart` and
`GeneralLinear.Mirabolic.columnPart`. Their published continuity theorems
give a continuous map
`(g,f) ↦ ((linearPart g, columnPart g),f)`. Compose with
`continuous_operator`. This uses the actual mirabolic subgroup topology
and its actual coordinate maps. Finally, `jointContinuity` introduces the
rank, Borel structure and Haar measure and pairs the two component results.
The same proof includes rank zero.

## Provenance and scope

This is an internal analytic consequence of the published affine
construction, generic normalized-pullback continuity, inverse-affine Haar
scaling and mirabolic coordinate continuity, together with Mathlib's
topology facts. It does not transcribe a separately numbered literature
result.

Fourier/Plancherel, induced Hilbert models, quotient transport, coefficient
completion, general semidirect induction, smooth-vector recovery and
block-induction irreducibility remain separate obligations. Joint
continuity of these operators supplies none of those comparisons.
