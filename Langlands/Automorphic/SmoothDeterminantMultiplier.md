# Finite-order determinant multiplication on actual smooth adelic functions

Author: Worker 2.

This internal construction restricts the actual automorphism from
`Langlands.Automorphic.DeterminantMultiplier` to the published smooth spaces
from `Langlands.Automorphic.Smooth`. It uses the proved local constancy of
finite-order Hecke characters in `Langlands.Global.HeckeCharacterFiniteOrder`.
The number field is `F : Type u`, coefficients are complex, and every natural
rank is allowed, including zero. Finite order is an explicit hypothesis.

`HeckeCharacter.finiteDeterminantKernel n χ hχ` is the actual kernel of the
character pulled back by the finite adelic inclusion and determinant. It is
an open subgroup: local constancy of the character makes its identity fiber
open. Its membership criterion is exactly that actual character value being one.
It does not assert that the whole finite adelic group is discrete.

`infiniteSmooth_determinantMultiplier` proves real smoothness on every infinite
slice. In the existing mixed archimedean coordinates, the multiplier is locally
constant, because the coordinate map and slice inclusion are continuous.
At each point the multiplied slice agrees on a neighborhood with a constant
complex scalar multiple of the original smooth slice. The smooth-function
submodule is closed under that scalar multiplication, and
`ContMDiffAt.congr_of_eventuallyEq` transfers smoothness to the multiplied
slice. A local canonical completeness instance for the matrix function type
allows Lean to recover the existing units charts; it changes neither the norm
nor the topology. `finiteLocallyConstant_determinantMultiplier`
uses the product of the two locally constant factors on each finite slice.
Together they prove preservation of the existing slice-wise smooth subspace.

For a function with one common open finite stabilizer, the proof uses the
intersection of that stabilizer with `finiteDeterminantKernel`. The actual
right-translation covariance and character value one show this intersection
fixes the multiplied function. This proves preservation of the stronger
common-stabilizer condition and its intersection with infinite smoothness.
`hasFiniteLevel_determinantMultiplier` obtains compact finite level by
intersecting the new open stabilizer with the original compact open level.
The existing compact-intersection proof supplies compactness; no existence
of a compact open subgroup is assumed implicitly.

`SmoothRationalFunctions.finiteOrderDeterminantMultiplier` and
`FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier` are actual
continuous complex-linear automorphisms of these two existing submodule
carriers, with their inherited subtype topologies. Their construction uses
`ContinuousLinearEquiv.ofSubmodules`. Preservation for the inverse character
and the proved inverse multiplication formula establish the required image
equalities. Evaluation gives multiplication by `χ(det g)`, and the inverse
gives multiplication by its inverse. The restricted actions obey
`R(g) Mχ = χ(det g) Mχ R(g)` for every actual adelic matrix.
The four named additive instances are the canonical submodule structures.

All provenance is the direct internal restriction argument just described,
using published actual functions, Hecke characters and Mathlib locality of
smoothness. No new comparison with an original-literature passage is claimed.
This module establishes neither differentiation covariance nor preservation
of center finiteness, compact finiteness or growth. A total twist of automorphic
operator realizations and their classes remains a separate construction.
