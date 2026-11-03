# Local compactness of actual function-field adeles

`Langlands.Global.FunctionFieldAdelesLocallyCompactStatement` is a proposition
for fields `k` and `F` in one arbitrary universe. Its inputs are a finite
constant field `k`, a `k`-algebra structure on `F`, a `RatFunc k`-algebra
structure compatible with that action, and `FunctionField k F`, meaning finite
dimensionality over the specified rational-function field. It imposes no
separability hypothesis on that presentation and does not supply residue
finiteness or a local compactness assumption as an input. Finiteness of the
constant field implies its perfectness.

The conclusions are:

- For every actual `AlgebraicCurve.Place k F`, the valuation ring
  `curvePlaceCompletionIntegers v` in the actual adic completion is compact
  in its existing subspace topology, and `curvePlaceCompletion v` is locally
  compact in its existing completion topology.
- The full ring `CurvePlaceAdeleRing k F`, indexed by all actual curve places,
  is locally compact in its cofinite restricted-product topology. Every
  `curvePlaceAdeleLevel k F S`, for a finite set of those places, is locally
  compact in its existing subspace topology.
- `RealAbsoluteValueAdeleRing k F`, indexed by the actual equivalence-class
  quotient of all nontrivial real absolute values of `F`, is locally compact
  in its published restricted-product topology. Every corresponding finite
  `realAbsoluteValueAdeleLevel k F S` is locally compact in its subspace
  topology. Its factors are the actual completions of the chosen quotient
  representatives, with their norm unit balls as integer rings.

These are the published actual objects, rather than an abstract supplied local
field family. The existing adelic homeomorphism identifies the two full
restricted-product rings. The levels are the literal open subrings integral at
every place outside the specified finite set; no assertion of compactness of
a full level is made.

This is a derived local-compactness target in the function-field branch of the
Conrad program. Its arithmetic route uses finiteness of actual curve-place
residue extensions, the canonical completed-residue comparison, and Mathlib's
complete discrete-valuation-ring compactness criterion. Open integer rings
then provide local compactness of the completed fields and the restricted
product. The published adelic homeomorphism and openness of both kinds of
levels give the remaining conclusions. This infrastructure is not presented
as a numbered assertion transcribed from Conrad. This file defines the target;
it contains no proof. Diagonal discreteness, geometric point-space comparisons,
model descent, and the remaining whole-paper assertions are separate obligations.
