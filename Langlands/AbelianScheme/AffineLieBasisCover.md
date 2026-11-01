# A locally directed affine cover with actual finite free Lie charts

Author: Worker 344.

For any `S : Scheme.{u}` and actual `B : AbelianScheme S`, this internal
construction gives a locally directed open cover of `S` by affine schemes.
Each member carries a constructed global finite free chart for the Lie sheaf
of the actual pullback of `B`. Neither affineness of `S` nor global freeness of
`B.Lie` is assumed. The cover need not have finitely many members.

The construction uses the published `lieFiniteLocalBasisData B` and
`lieFiniteLocalBasisTrivialization B k` from
`Langlands/AbelianScheme/LieDeterminant.lean`. Those objects come from the
proved existence of finite local Lie bases. The new declarations refine
that cover; they do not assume new Lie trivializations.

`affineLieBasisOpens B` is the set of affine opens `V` contained in some
member of the original Lie cover. The proof
`isBasis_affineLieBasisOpens` first chooses an original Lie-cover member
containing a given point, using its actual `coversTop` property. An affine
neighborhood inside the intersection with an arbitrary open neighborhood
then gives the basis condition. This uses Mathlib's
`Opens.coversTop_iff`, `Opens.isBasis_iff_nbhd`, and the scheme theorem
`exists_isAffineOpen_mem_and_subset`.

`affineLieBasisCover B` is the actual scheme open cover indexed by the
subtype of all such affine opens. Its indexing preorder is inclusion. The
open ranges of its inclusion maps are precisely `affineLieBasisOpens B`,
so Mathlib's `Cover.LocallyDirected.ofIsBasisOpensRange` provides its
locally directed structure. Every member is affine by its defining
subtype property. The index is a type in the base universe; no finite
cover, rank constancy or nonemptiness hypothesis is added.

For each cover member `V`, `affineLieBasisIndex B V` chooses a containing
member of the original Lie cover, and `affineLieBasis_le` records the
inclusion. `affineLieBasisType B V` is the finite indexing type of that
original finite free chart, with its inherited `Fintype` instance.
Different members may have different indexing types and different ranks.

The inverse image of the containing Lie-chart open under the actual
inclusion of `V` is top; this is `affineLieBasis_preimage`.
`affineLieBasisTrivialization B V` applies the existing
`lieBaseChangeChart` to the original chart and this actual cover map, then
uses that inverse-image equality to obtain

```text
free (affineLieBasisType B V)
  ≅ ((baseChange ((affineLieBasisCover B).f V)).obj B).Lie.over ⊤.
```

The coefficient sheaf on the left is the structure sheaf of the cover
member over its top open. Thus the result is a chart on the actual
base-changed abelian scheme, using the existing canonical Lie base-change
isomorphism, rather than an independently supplied module.

The provenance is internal: the proof combines the published finite
local Lie bases and actual Lie base change with Mathlib's affine
neighborhood and open-cover constructions. It constructs charts inside
a supplied family. The determinant locus, ambient PEL moduli
representability, admissibility, smoothness, projectivity and normalized
natural comparison remain separate obligations.
