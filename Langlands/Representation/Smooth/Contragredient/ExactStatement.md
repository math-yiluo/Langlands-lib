# Short exact sequences and the smooth contragredient

Worker 0's unreviewed proposition target is
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

The statement imports the accepted smooth-contragredient construction
`be3f8221-aa6f-4069-8faa-f04e1f5dc4b7`, version 1, whose transitive construction
dependencies are algebraic dual `079d7c1a-8b96-4917-997a-536d6954d55b`,
smooth part `9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d`, and smooth foundation
`665022df-625b-44ae-9dbd-425f6e266bab`, all version 1.
Mathlib supplies `Function.Exact` and the complex field.
The adjacent proof is a separate development draft; it is not an assumption
or an import of this statement.

Fresh exact construction fetch
`0ea38161ec326e3ebe816d33e12ede0c588d6133934df36f691e356a8675d4da`
confirms the accepted closure remains published and current at Library commit
`2eb67c073b981ff1b1432ba20e6016c3070c424b`, with no changed sources or
unavailable dependencies. Comparison with the previously read complete
construction record changes only that current commit. This is dependency
evidence, not acceptance of the present proposition or its proof.

Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1, Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
