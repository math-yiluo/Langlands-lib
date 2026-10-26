# Ordered ordinary induction in stages

This module composes two published constructions. The actual equivalence
`Langlands.Parabolic.orderedRefinementInductionEquiv` compares induction first
inside the outer Levi and then to the ambient general linear group with ordinary
normalized induction from the original ordered block shape.

The inputs are a prime, a p-adic field `F`, compatible topological data `T`,
shapes `B D` of the same rank, a refinement `S` of `D`, and the exact coordinate
data `e`, `hs`, `hc` of `RefinementCoordinatesNormalizationTheorem`. The input
representation `σ` acts on the actual Levi of `B`; its coefficient space has
arbitrary universe `uV`, independent of the field universe `uF`. The
construction assumes `IsSmooth σ` in the topology supplied by `T`. It imposes
no admissibility, irreducibility, finite-dimensionality or positive-rank
assumption. The general construction includes empty shapes at rank zero.

Write `E_L = B.leviRefinementEquiv D S e hs F.Carrier` and
`σL = σ.comp E_L.symm.toMonoidHom`. The source action, abbreviated
`orderedRefinementIteratedInduced`, is

```text
T.normalizedParabolicInduced D (T.normalizedRefinedInduced D S σL).
```

The target is `T.normalizedParabolicInduced B σ`. Both actions use the actual
smooth induced functions, a uniform open right stabilizer and right translation.
Their carriers have universe `max uF uV`.

The inverse Levi-coordinate map is continuous, so the existing smooth-pullback
theorem supplies smoothness of `σL`. It therefore defines an object in the full
smooth representation category. At that object,
`normalizedRefinementInductionTransitivity` gives the actual equivalence from
the iterated action to `T.normalizedComposedInduced D S σL`.
`refinementCoordinatesNormalization` then supplies the equivalence from
composed to ordinary induction. A private existence proof selects these two
equivalences with their published evaluation properties and composes them.
The public definition chooses the resulting witness; its two accessor lemmas
use the corresponding existence specification. The categorical component is
converted to the concrete actions by unfolding only the functor and object
wrappers.

The forward formula is

```text
(E f)(g) = f(g)(1).
```

For an ordinary induced function `f`, its inverse is specified by

```text
(E.symm f)(g)(m) =
  (T.leviHalfModulus D m : ℂ)⁻¹ • f(D.leviEmbedding F.Carrier m * g).
```

The notation here stands for the corresponding one or two applications of
`Induction.eval` in the Lean lemmas. The inverse retains the specified outer
positive-half correction. These identities follow from the induction-in-stages
formulas because the normalization comparison keeps the underlying ambient
function in each direction. Linearity and equivariance are part of the
composed `Representation.Equiv`.

`headTailInductionEquiv` specializes this same construction when
`h : B.length = k + 2`. It uses `B.headTailShape h`,
`B.headTailRefinement h`, `B.headTailBlockEquiv h`,
`B.headTailBlock_size h` and `B.headTail_index h`, without supplying a new
coordinate hypothesis. Its two evaluation lemmas are the general formulas at
these published coordinates.

This is an internal composition of the published constructions in
`RefinementInductionTransitivityProof`, `RefinementCoordinatesNormalizationProof`,
`Smooth.Transfer.PullbackProof` and `Group.GL.HeadTailBlocks`, rather than a
new transcription from the literature. No modulus calculation is repeated.
The module compares iterated and ordinary induction of the transported
representation. It does not identify refined induction of an external tensor
with the tensor of the block inductions, or prove Whittaker type, factor
existence or L-factor multiplicativity. Those are separate obligations for the
Rankin–Selberg application.
