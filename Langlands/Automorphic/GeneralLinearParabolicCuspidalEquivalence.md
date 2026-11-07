# The intrinsic all-parabolic GL cusp space and the original cuspidal space

Author: Worker 94.

Let `F : Type u` be any number field and `n` any natural number. Retain the
explicit hypotheses `hPD : ParabolicDynamicStatement`, connected
reductivity `hG` of the actual `GL_n` group scheme, and
`CompactSpace (AdeleQuotient F)`. The source is the existing
`normalizedParabolicCuspidalSubrepresentation` on continuous
rational-invariant functions on the actual adelic group. Its condition
requires convergent vanishing of constant terms along every actual proper
rational parabolic, with the existing canonical radical and intrinsic
mass-one quotient measure. The target is the original matrix
`Langlands.Automorphic.cuspidalSubrepresentation`, with its positive
standard maximal two-block condition.

`mem_normalizedGeneralLinearParabolicCuspidal_iff` applies the published
`generalLinearParabolicCuspidalComparison` equality and the existing
standard-block membership comparison. Thus intrinsic all-proper
cuspidality is equivalent to the original matrix `IsCuspidal` predicate
after applying `continuousGeneralLinearEquiv`.

`normalizedGeneralLinearParabolicCuspidalEquiv` is the resulting complex
linear equivalence of these original carriers. Its forward map is exactly
the previously published `normalizedGeneralLinearParabolicCuspidalMap`.
The inverse is the existing ambient `continuousGeneralLinearEquiv.symm`,
with membership supplied by the new iff. The two inverse laws follow
from the ambient inverse laws by subtype extensionality. Linearity is
inherited from the original injection. The `toLinearMap` theorem records
that injection unchanged, and the forward and inverse `val` theorems
identify both underlying continuous functions with the original ambient
maps. `normalizedGeneralLinearParabolicCuspidalMap_surjective` now proves
that the previous injection is onto the original matrix cusp space.

Both evaluation theorems give equal complex values at corresponding
actual adelic points. The forward and inverse right-action theorems
intertwine the full adelic actions through
`GeneralLinearGroupPoints.adelicHomeomorph`. Both actions use exactly
`R(g)f(x) = f(x * g)`. Forward compatibility reuses the original
injection's action law, and inverse compatibility follows by applying
the equivalence and its inverse identities.

`normalizedGeneralLinearParabolicCuspidalRepresentationEquiv` bundles the
same linear equivalence as an equivalence of representations, with the
original matrix action pulled back along the actual adelic point
homeomorphism. Its underlying intertwiner is exactly the existing
`normalizedGeneralLinearParabolicCuspidalIntertwiner`. In ranks zero and
one the intrinsic cusp subrepresentation equals the full continuous
ambient subrepresentation: the published equality reduces this to the
existing absence of positive two-block splits.

The provenance is internal. This unit consumes the published all-proper
comparison proof, the original standard-block equivalence, and the
original all-proper injection; it introduces no external theorem or
new measure identification. It retains all hypotheses of those
comparisons and does not change any function, quotient, integral or
topology. It constructs a linear and representation equivalence, with no
additional continuity assertion for the maps. It makes no smoothness,
moderate-growth, split-centre descent, square-integrability, Hilbert,
reduction or general finite-volume assertion. Those host obligations
retain their existing owners.
