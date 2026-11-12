# Renard II.3.6: Haar distributions and density embeddings

This unit states five closed propositions and their conjunction, without proofs.
They use the published complex algebraic dual `Distribution G` of
`SchwartzBruhat G`, the original translation actions and the concrete integration
and density maps in `Distribution.Haar`. No continuity condition on the dual is
introduced. All groups are Hausdorff, locally compact and totally disconnected,
with their supplied group topology. No countability assumption is added.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The exact locator is II.3.6 Proposition, printed pp.46–47 / PDF pp.52–53,
and the following density paragraph on printed p.47 / PDF p.53.

The declarations are in
`Langlands.HarmonicAnalysis.Distribution.RenardHaar`:

- `LeftHaarStatement` supplies a strictly positive left-invariant distribution
  and expresses every left-invariant algebraic distribution as its unique
  complex scalar multiple. The zero distribution is allowed among those being
  compared, with scalar zero.
- `RightHaarStatement` states the corresponding right-invariant assertion.
- `PositiveScalarUniquenessStatement` compares two strictly positive
  distributions invariant on the same side. Their unique scalar is a strictly
  positive real number, embedded into the complex scalar field. This makes the
  positive normalization consequence of the Proposition explicit.
- `MeasureHaarBridgeStatement` identifies the actual `ofMeasure μ`, for any
  Mathlib left Haar measure, as positive and left invariant, and compares every
  invariant algebraic distribution with this very integration functional.
- `DensityEmbeddingStatement` states injectivity of `density μ`, equality of
  its topological distribution support with the nonzero locus of the locally
  constant density, and membership of every `testDensity μ f` in the published
  compact-support submodule `compactlySupported`.

The support equality makes explicit a consequence of positivity and local
constancy used by the source's embedding claim. The nonzero locus of a locally
constant function is closed, so it is its topological support; for a test it is
compact. Thus this is the actual density embedding, with no replacement carrier
or abstract injective map assumed. The support equality is a derived bridge
rather than a separately numbered assertion of the source.

Mathlib's `Measure.isHaarMeasure_haarMeasure` constructs an actual measure;
`Measure.haarMeasure_unique` and the general uniqueness results in
`Mathlib.MeasureTheory.Measure.Haar.Unique` concern measures. They do not
classify arbitrary elements of the full algebraic dual. The bridge above states
that additional conclusion explicitly. In particular this unit neither assumes
that all algebraic distributions are measures nor claims a distribution proof
from measure uniqueness alone. The predicates `IsPositive`, `IsLeftInvariant`
and `IsRightInvariant` are the published ones; strict positivity includes real
values on all nonzero nonnegative real-valued tests.
