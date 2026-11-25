# Short exact sequences and the smooth contragredient

The proposition target is
`Langlands.SmoothContragredientShortExactStatement`.

Let `G` be a topological group in which every open subgroup contains a compact
open subgroup. For complex representations `rho`, `sigma`, and `tau` on
independently sized vector spaces, assume that `rho` and `sigma` are smooth.
Given intertwiners `f : rho -> sigma` and `g : sigma -> tau`, assume that `f`
is injective, the pair `(f,g)` is exact, and `g` is surjective. Then the reversed
pair of smooth contragredient maps is short exact: the map induced by `g` is
injective, the pair is exact at the smooth dual of `sigma`, and the map induced
by `f` is surjective.

`Function.Exact f g` means that `g w = 0` if and only if `w` is in the image
of `f`. No module carries a topology. The topological-group instance,
compact-open cofinality, smoothness and all exactness hypotheses are internal
to the proposition. No admissibility, finite dimension, global Hausdorffness,
local compactness or countability is assumed. Smoothness of the last
representation need not be an additional hypothesis: a surjective intertwiner
from the smooth middle representation supplies it.

## Provenance

Casselman, *Introduction to representations of p-adic groups*, Chapter II,
June 16, 2019, Section 3, page 6, Corollary II.3.3, gives reversal of short exact
sequences of admissible representations with free fixed spaces. Proposition
II.3.1 on the same page identifies compact-open fixed smooth functionals with
the algebraic dual of the original fixed-vector space.

The present complex-coefficient result is a derived strengthening that removes
admissibility. Algebraic functionals extend across an inclusion of complex
vector spaces. Combining that extension on fixed-vector spaces with the
compact-open duality theorem gives the surjective endpoint of the reversed
sequence. The injective endpoint and exactness at the middle follow directly
from pullback and descent of functionals along the original surjection.
This argument uses only the explicitly stated cofinality, rather than the
source's stronger ambient assumptions on page 1.

- Literature ID: `casselman-2019-smooth-representations`.
- Content SHA256:
  `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
- Actual original file:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

The statement imports the smooth-contragredient construction
`Langlands.Representation.Smooth.Contragredient.Definitions`, whose transitive
construction dependencies are the algebraic dual
(`Langlands.Representation.Dual.Definitions`), the smooth part
(`Langlands.Representation.Smooth.SmoothPart.Definitions`), and the smooth
foundation (`Langlands.Representation.Smooth.Definitions`).
Mathlib supplies `Function.Exact` and the complex field.
The adjacent proof `Langlands.smoothContragredientShortExact`
(`Langlands.Representation.Smooth.Contragredient.ExactProof`) is not an
assumption or an import of this statement.

The construction closure was found published at Library commit
`2eb67c073b981ff1b1432ba20e6016c3070c424b`, with no changed sources or
unavailable dependencies.

Environment: Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
